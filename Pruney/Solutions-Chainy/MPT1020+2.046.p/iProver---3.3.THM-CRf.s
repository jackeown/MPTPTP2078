%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:14 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_46)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

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
    inference(ennf_transformation,[],[f22])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f51,f50])).

fof(f94,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

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

fof(f85,plain,(
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

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f83,plain,(
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

fof(f87,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f95,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f69,f82])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f70,f82,f82])).

cnf(c_33,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2030,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2026,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2036,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3532,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2026,c_2036])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_276,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_277,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_349,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_277])).

cnf(c_2022,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_7038,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3532,c_2022])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_95,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_97,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_7162,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7038,c_97])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_23,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_537,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_538,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_540,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_41,c_38])).

cnf(c_623,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_540])).

cnf(c_624,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_624])).

cnf(c_671,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_673,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_675,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_671,c_38,c_673])).

cnf(c_2018,plain,
    ( k2_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_7167,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_7162,c_2018])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2034,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4944,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2026,c_2034])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f85])).

cnf(c_30,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_206,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_30])).

cnf(c_207,plain,
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
    inference(renaming,[status(thm)],[c_206])).

cnf(c_2023,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_5355,plain,
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
    inference(superposition,[status(thm)],[c_4944,c_2023])).

cnf(c_42,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_43,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6919,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_relat_1(sK1) != sK0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5355,c_42,c_43,c_45])).

cnf(c_6920,plain,
    ( k2_funct_1(sK1) = X0
    | k2_relat_1(sK1) != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6919])).

cnf(c_8309,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7167,c_6920])).

cnf(c_8313,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8309])).

cnf(c_10455,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_8313])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_10456,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10455])).

cnf(c_10458,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10455,c_46,c_47,c_49])).

cnf(c_10459,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_10458])).

cnf(c_32,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2031,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_556,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_557,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_559,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_41,c_40,c_38])).

cnf(c_2084,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2031,c_559])).

cnf(c_10462,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10459,c_2084])).

cnf(c_49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2275,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2276,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2275])).

cnf(c_10864,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10462,c_49,c_2276])).

cnf(c_2029,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3531,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2029,c_2036])).

cnf(c_10902,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10864,c_3531])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_10931,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10902,c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2039,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2037,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_12])).

cnf(c_2021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_4900,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_2021])).

cnf(c_7302,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_4900])).

cnf(c_7637,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7302,c_95])).

cnf(c_7644,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_7637])).

cnf(c_16,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_15,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2671,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16,c_15])).

cnf(c_7676,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7644,c_2671])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2040,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7697,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7676,c_2040])).

cnf(c_11398,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10931,c_7697])).

cnf(c_10903,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10864,c_2084])).

cnf(c_13505,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11398,c_10903])).

cnf(c_17,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3389,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16,c_17])).

cnf(c_3390,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3389,c_16])).

cnf(c_10901,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10864,c_3532])).

cnf(c_10934,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10901,c_6])).

cnf(c_11458,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10934,c_7697])).

cnf(c_14345,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13505,c_3390,c_11458])).

cnf(c_2033,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4059,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_2033])).

cnf(c_7699,plain,
    ( r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7676,c_4059])).

cnf(c_14347,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14345,c_7699])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.72/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.01  
% 3.72/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/1.01  
% 3.72/1.01  ------  iProver source info
% 3.72/1.01  
% 3.72/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.72/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/1.01  git: non_committed_changes: false
% 3.72/1.01  git: last_make_outside_of_git: false
% 3.72/1.01  
% 3.72/1.01  ------ 
% 3.72/1.01  
% 3.72/1.01  ------ Input Options
% 3.72/1.01  
% 3.72/1.01  --out_options                           all
% 3.72/1.01  --tptp_safe_out                         true
% 3.72/1.01  --problem_path                          ""
% 3.72/1.01  --include_path                          ""
% 3.72/1.01  --clausifier                            res/vclausify_rel
% 3.72/1.01  --clausifier_options                    --mode clausify
% 3.72/1.01  --stdin                                 false
% 3.72/1.01  --stats_out                             all
% 3.72/1.01  
% 3.72/1.01  ------ General Options
% 3.72/1.01  
% 3.72/1.01  --fof                                   false
% 3.72/1.01  --time_out_real                         305.
% 3.72/1.01  --time_out_virtual                      -1.
% 3.72/1.01  --symbol_type_check                     false
% 3.72/1.01  --clausify_out                          false
% 3.72/1.01  --sig_cnt_out                           false
% 3.72/1.01  --trig_cnt_out                          false
% 3.72/1.01  --trig_cnt_out_tolerance                1.
% 3.72/1.01  --trig_cnt_out_sk_spl                   false
% 3.72/1.01  --abstr_cl_out                          false
% 3.72/1.01  
% 3.72/1.01  ------ Global Options
% 3.72/1.01  
% 3.72/1.01  --schedule                              default
% 3.72/1.01  --add_important_lit                     false
% 3.72/1.01  --prop_solver_per_cl                    1000
% 3.72/1.01  --min_unsat_core                        false
% 3.72/1.01  --soft_assumptions                      false
% 3.72/1.01  --soft_lemma_size                       3
% 3.72/1.01  --prop_impl_unit_size                   0
% 3.72/1.01  --prop_impl_unit                        []
% 3.72/1.01  --share_sel_clauses                     true
% 3.72/1.01  --reset_solvers                         false
% 3.72/1.01  --bc_imp_inh                            [conj_cone]
% 3.72/1.01  --conj_cone_tolerance                   3.
% 3.72/1.01  --extra_neg_conj                        none
% 3.72/1.01  --large_theory_mode                     true
% 3.72/1.01  --prolific_symb_bound                   200
% 3.72/1.01  --lt_threshold                          2000
% 3.72/1.01  --clause_weak_htbl                      true
% 3.72/1.01  --gc_record_bc_elim                     false
% 3.72/1.01  
% 3.72/1.01  ------ Preprocessing Options
% 3.72/1.01  
% 3.72/1.01  --preprocessing_flag                    true
% 3.72/1.01  --time_out_prep_mult                    0.1
% 3.72/1.01  --splitting_mode                        input
% 3.72/1.01  --splitting_grd                         true
% 3.72/1.01  --splitting_cvd                         false
% 3.72/1.01  --splitting_cvd_svl                     false
% 3.72/1.01  --splitting_nvd                         32
% 3.72/1.01  --sub_typing                            true
% 3.72/1.01  --prep_gs_sim                           true
% 3.72/1.01  --prep_unflatten                        true
% 3.72/1.01  --prep_res_sim                          true
% 3.72/1.01  --prep_upred                            true
% 3.72/1.01  --prep_sem_filter                       exhaustive
% 3.72/1.01  --prep_sem_filter_out                   false
% 3.72/1.01  --pred_elim                             true
% 3.72/1.01  --res_sim_input                         true
% 3.72/1.01  --eq_ax_congr_red                       true
% 3.72/1.01  --pure_diseq_elim                       true
% 3.72/1.01  --brand_transform                       false
% 3.72/1.01  --non_eq_to_eq                          false
% 3.72/1.01  --prep_def_merge                        true
% 3.72/1.01  --prep_def_merge_prop_impl              false
% 3.72/1.01  --prep_def_merge_mbd                    true
% 3.72/1.01  --prep_def_merge_tr_red                 false
% 3.72/1.01  --prep_def_merge_tr_cl                  false
% 3.72/1.01  --smt_preprocessing                     true
% 3.72/1.01  --smt_ac_axioms                         fast
% 3.72/1.01  --preprocessed_out                      false
% 3.72/1.01  --preprocessed_stats                    false
% 3.72/1.01  
% 3.72/1.01  ------ Abstraction refinement Options
% 3.72/1.01  
% 3.72/1.01  --abstr_ref                             []
% 3.72/1.01  --abstr_ref_prep                        false
% 3.72/1.01  --abstr_ref_until_sat                   false
% 3.72/1.01  --abstr_ref_sig_restrict                funpre
% 3.72/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/1.01  --abstr_ref_under                       []
% 3.72/1.01  
% 3.72/1.01  ------ SAT Options
% 3.72/1.01  
% 3.72/1.01  --sat_mode                              false
% 3.72/1.01  --sat_fm_restart_options                ""
% 3.72/1.01  --sat_gr_def                            false
% 3.72/1.01  --sat_epr_types                         true
% 3.72/1.01  --sat_non_cyclic_types                  false
% 3.72/1.01  --sat_finite_models                     false
% 3.72/1.01  --sat_fm_lemmas                         false
% 3.72/1.01  --sat_fm_prep                           false
% 3.72/1.01  --sat_fm_uc_incr                        true
% 3.72/1.01  --sat_out_model                         small
% 3.72/1.01  --sat_out_clauses                       false
% 3.72/1.01  
% 3.72/1.01  ------ QBF Options
% 3.72/1.01  
% 3.72/1.01  --qbf_mode                              false
% 3.72/1.01  --qbf_elim_univ                         false
% 3.72/1.01  --qbf_dom_inst                          none
% 3.72/1.01  --qbf_dom_pre_inst                      false
% 3.72/1.01  --qbf_sk_in                             false
% 3.72/1.01  --qbf_pred_elim                         true
% 3.72/1.01  --qbf_split                             512
% 3.72/1.01  
% 3.72/1.01  ------ BMC1 Options
% 3.72/1.01  
% 3.72/1.01  --bmc1_incremental                      false
% 3.72/1.01  --bmc1_axioms                           reachable_all
% 3.72/1.01  --bmc1_min_bound                        0
% 3.72/1.01  --bmc1_max_bound                        -1
% 3.72/1.01  --bmc1_max_bound_default                -1
% 3.72/1.01  --bmc1_symbol_reachability              true
% 3.72/1.01  --bmc1_property_lemmas                  false
% 3.72/1.01  --bmc1_k_induction                      false
% 3.72/1.01  --bmc1_non_equiv_states                 false
% 3.72/1.01  --bmc1_deadlock                         false
% 3.72/1.01  --bmc1_ucm                              false
% 3.72/1.01  --bmc1_add_unsat_core                   none
% 3.72/1.01  --bmc1_unsat_core_children              false
% 3.72/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/1.01  --bmc1_out_stat                         full
% 3.72/1.01  --bmc1_ground_init                      false
% 3.72/1.01  --bmc1_pre_inst_next_state              false
% 3.72/1.01  --bmc1_pre_inst_state                   false
% 3.72/1.01  --bmc1_pre_inst_reach_state             false
% 3.72/1.01  --bmc1_out_unsat_core                   false
% 3.72/1.01  --bmc1_aig_witness_out                  false
% 3.72/1.01  --bmc1_verbose                          false
% 3.72/1.01  --bmc1_dump_clauses_tptp                false
% 3.72/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.72/1.01  --bmc1_dump_file                        -
% 3.72/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.72/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.72/1.01  --bmc1_ucm_extend_mode                  1
% 3.72/1.01  --bmc1_ucm_init_mode                    2
% 3.72/1.01  --bmc1_ucm_cone_mode                    none
% 3.72/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.72/1.01  --bmc1_ucm_relax_model                  4
% 3.72/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.72/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/1.01  --bmc1_ucm_layered_model                none
% 3.72/1.01  --bmc1_ucm_max_lemma_size               10
% 3.72/1.01  
% 3.72/1.01  ------ AIG Options
% 3.72/1.01  
% 3.72/1.01  --aig_mode                              false
% 3.72/1.01  
% 3.72/1.01  ------ Instantiation Options
% 3.72/1.01  
% 3.72/1.01  --instantiation_flag                    true
% 3.72/1.01  --inst_sos_flag                         false
% 3.72/1.01  --inst_sos_phase                        true
% 3.72/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/1.01  --inst_lit_sel_side                     num_symb
% 3.72/1.01  --inst_solver_per_active                1400
% 3.72/1.01  --inst_solver_calls_frac                1.
% 3.72/1.01  --inst_passive_queue_type               priority_queues
% 3.72/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/1.01  --inst_passive_queues_freq              [25;2]
% 3.72/1.01  --inst_dismatching                      true
% 3.72/1.01  --inst_eager_unprocessed_to_passive     true
% 3.72/1.01  --inst_prop_sim_given                   true
% 3.72/1.01  --inst_prop_sim_new                     false
% 3.72/1.01  --inst_subs_new                         false
% 3.72/1.01  --inst_eq_res_simp                      false
% 3.72/1.01  --inst_subs_given                       false
% 3.72/1.01  --inst_orphan_elimination               true
% 3.72/1.01  --inst_learning_loop_flag               true
% 3.72/1.01  --inst_learning_start                   3000
% 3.72/1.01  --inst_learning_factor                  2
% 3.72/1.01  --inst_start_prop_sim_after_learn       3
% 3.72/1.01  --inst_sel_renew                        solver
% 3.72/1.01  --inst_lit_activity_flag                true
% 3.72/1.01  --inst_restr_to_given                   false
% 3.72/1.01  --inst_activity_threshold               500
% 3.72/1.01  --inst_out_proof                        true
% 3.72/1.01  
% 3.72/1.01  ------ Resolution Options
% 3.72/1.01  
% 3.72/1.01  --resolution_flag                       true
% 3.72/1.01  --res_lit_sel                           adaptive
% 3.72/1.01  --res_lit_sel_side                      none
% 3.72/1.01  --res_ordering                          kbo
% 3.72/1.01  --res_to_prop_solver                    active
% 3.72/1.01  --res_prop_simpl_new                    false
% 3.72/1.01  --res_prop_simpl_given                  true
% 3.72/1.01  --res_passive_queue_type                priority_queues
% 3.72/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/1.01  --res_passive_queues_freq               [15;5]
% 3.72/1.01  --res_forward_subs                      full
% 3.72/1.01  --res_backward_subs                     full
% 3.72/1.01  --res_forward_subs_resolution           true
% 3.72/1.01  --res_backward_subs_resolution          true
% 3.72/1.01  --res_orphan_elimination                true
% 3.72/1.01  --res_time_limit                        2.
% 3.72/1.01  --res_out_proof                         true
% 3.72/1.01  
% 3.72/1.01  ------ Superposition Options
% 3.72/1.01  
% 3.72/1.01  --superposition_flag                    true
% 3.72/1.01  --sup_passive_queue_type                priority_queues
% 3.72/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.72/1.01  --demod_completeness_check              fast
% 3.72/1.01  --demod_use_ground                      true
% 3.72/1.01  --sup_to_prop_solver                    passive
% 3.72/1.01  --sup_prop_simpl_new                    true
% 3.72/1.01  --sup_prop_simpl_given                  true
% 3.72/1.01  --sup_fun_splitting                     false
% 3.72/1.01  --sup_smt_interval                      50000
% 3.72/1.01  
% 3.72/1.01  ------ Superposition Simplification Setup
% 3.72/1.01  
% 3.72/1.01  --sup_indices_passive                   []
% 3.72/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.01  --sup_full_bw                           [BwDemod]
% 3.72/1.01  --sup_immed_triv                        [TrivRules]
% 3.72/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.01  --sup_immed_bw_main                     []
% 3.72/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.01  
% 3.72/1.01  ------ Combination Options
% 3.72/1.01  
% 3.72/1.01  --comb_res_mult                         3
% 3.72/1.01  --comb_sup_mult                         2
% 3.72/1.01  --comb_inst_mult                        10
% 3.72/1.01  
% 3.72/1.01  ------ Debug Options
% 3.72/1.01  
% 3.72/1.01  --dbg_backtrace                         false
% 3.72/1.01  --dbg_dump_prop_clauses                 false
% 3.72/1.01  --dbg_dump_prop_clauses_file            -
% 3.72/1.01  --dbg_out_stat                          false
% 3.72/1.01  ------ Parsing...
% 3.72/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/1.01  
% 3.72/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.72/1.01  
% 3.72/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/1.01  
% 3.72/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/1.01  ------ Proving...
% 3.72/1.01  ------ Problem Properties 
% 3.72/1.01  
% 3.72/1.01  
% 3.72/1.01  clauses                                 33
% 3.72/1.01  conjectures                             8
% 3.72/1.01  EPR                                     9
% 3.72/1.01  Horn                                    31
% 3.72/1.01  unary                                   19
% 3.72/1.01  binary                                  6
% 3.72/1.01  lits                                    70
% 3.72/1.01  lits eq                                 22
% 3.72/1.01  fd_pure                                 0
% 3.72/1.01  fd_pseudo                               0
% 3.72/1.01  fd_cond                                 1
% 3.72/1.01  fd_pseudo_cond                          5
% 3.72/1.01  AC symbols                              0
% 3.72/1.01  
% 3.72/1.01  ------ Schedule dynamic 5 is on 
% 3.72/1.01  
% 3.72/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.72/1.01  
% 3.72/1.01  
% 3.72/1.01  ------ 
% 3.72/1.01  Current options:
% 3.72/1.01  ------ 
% 3.72/1.01  
% 3.72/1.01  ------ Input Options
% 3.72/1.01  
% 3.72/1.01  --out_options                           all
% 3.72/1.01  --tptp_safe_out                         true
% 3.72/1.01  --problem_path                          ""
% 3.72/1.01  --include_path                          ""
% 3.72/1.01  --clausifier                            res/vclausify_rel
% 3.72/1.01  --clausifier_options                    --mode clausify
% 3.72/1.01  --stdin                                 false
% 3.72/1.01  --stats_out                             all
% 3.72/1.01  
% 3.72/1.01  ------ General Options
% 3.72/1.01  
% 3.72/1.01  --fof                                   false
% 3.72/1.01  --time_out_real                         305.
% 3.72/1.01  --time_out_virtual                      -1.
% 3.72/1.01  --symbol_type_check                     false
% 3.72/1.01  --clausify_out                          false
% 3.72/1.01  --sig_cnt_out                           false
% 3.72/1.01  --trig_cnt_out                          false
% 3.72/1.01  --trig_cnt_out_tolerance                1.
% 3.72/1.01  --trig_cnt_out_sk_spl                   false
% 3.72/1.01  --abstr_cl_out                          false
% 3.72/1.01  
% 3.72/1.01  ------ Global Options
% 3.72/1.01  
% 3.72/1.01  --schedule                              default
% 3.72/1.01  --add_important_lit                     false
% 3.72/1.01  --prop_solver_per_cl                    1000
% 3.72/1.01  --min_unsat_core                        false
% 3.72/1.01  --soft_assumptions                      false
% 3.72/1.01  --soft_lemma_size                       3
% 3.72/1.01  --prop_impl_unit_size                   0
% 3.72/1.01  --prop_impl_unit                        []
% 3.72/1.01  --share_sel_clauses                     true
% 3.72/1.01  --reset_solvers                         false
% 3.72/1.01  --bc_imp_inh                            [conj_cone]
% 3.72/1.01  --conj_cone_tolerance                   3.
% 3.72/1.01  --extra_neg_conj                        none
% 3.72/1.01  --large_theory_mode                     true
% 3.72/1.01  --prolific_symb_bound                   200
% 3.72/1.01  --lt_threshold                          2000
% 3.72/1.01  --clause_weak_htbl                      true
% 3.72/1.01  --gc_record_bc_elim                     false
% 3.72/1.01  
% 3.72/1.01  ------ Preprocessing Options
% 3.72/1.01  
% 3.72/1.01  --preprocessing_flag                    true
% 3.72/1.01  --time_out_prep_mult                    0.1
% 3.72/1.01  --splitting_mode                        input
% 3.72/1.01  --splitting_grd                         true
% 3.72/1.01  --splitting_cvd                         false
% 3.72/1.01  --splitting_cvd_svl                     false
% 3.72/1.01  --splitting_nvd                         32
% 3.72/1.01  --sub_typing                            true
% 3.72/1.01  --prep_gs_sim                           true
% 3.72/1.01  --prep_unflatten                        true
% 3.72/1.01  --prep_res_sim                          true
% 3.72/1.01  --prep_upred                            true
% 3.72/1.01  --prep_sem_filter                       exhaustive
% 3.72/1.01  --prep_sem_filter_out                   false
% 3.72/1.01  --pred_elim                             true
% 3.72/1.01  --res_sim_input                         true
% 3.72/1.01  --eq_ax_congr_red                       true
% 3.72/1.01  --pure_diseq_elim                       true
% 3.72/1.01  --brand_transform                       false
% 3.72/1.01  --non_eq_to_eq                          false
% 3.72/1.01  --prep_def_merge                        true
% 3.72/1.01  --prep_def_merge_prop_impl              false
% 3.72/1.01  --prep_def_merge_mbd                    true
% 3.72/1.01  --prep_def_merge_tr_red                 false
% 3.72/1.01  --prep_def_merge_tr_cl                  false
% 3.72/1.01  --smt_preprocessing                     true
% 3.72/1.01  --smt_ac_axioms                         fast
% 3.72/1.01  --preprocessed_out                      false
% 3.72/1.01  --preprocessed_stats                    false
% 3.72/1.01  
% 3.72/1.01  ------ Abstraction refinement Options
% 3.72/1.01  
% 3.72/1.01  --abstr_ref                             []
% 3.72/1.01  --abstr_ref_prep                        false
% 3.72/1.01  --abstr_ref_until_sat                   false
% 3.72/1.01  --abstr_ref_sig_restrict                funpre
% 3.72/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/1.01  --abstr_ref_under                       []
% 3.72/1.01  
% 3.72/1.01  ------ SAT Options
% 3.72/1.01  
% 3.72/1.01  --sat_mode                              false
% 3.72/1.01  --sat_fm_restart_options                ""
% 3.72/1.01  --sat_gr_def                            false
% 3.72/1.01  --sat_epr_types                         true
% 3.72/1.01  --sat_non_cyclic_types                  false
% 3.72/1.01  --sat_finite_models                     false
% 3.72/1.01  --sat_fm_lemmas                         false
% 3.72/1.01  --sat_fm_prep                           false
% 3.72/1.01  --sat_fm_uc_incr                        true
% 3.72/1.01  --sat_out_model                         small
% 3.72/1.01  --sat_out_clauses                       false
% 3.72/1.01  
% 3.72/1.01  ------ QBF Options
% 3.72/1.01  
% 3.72/1.01  --qbf_mode                              false
% 3.72/1.01  --qbf_elim_univ                         false
% 3.72/1.01  --qbf_dom_inst                          none
% 3.72/1.01  --qbf_dom_pre_inst                      false
% 3.72/1.01  --qbf_sk_in                             false
% 3.72/1.01  --qbf_pred_elim                         true
% 3.72/1.01  --qbf_split                             512
% 3.72/1.01  
% 3.72/1.01  ------ BMC1 Options
% 3.72/1.01  
% 3.72/1.01  --bmc1_incremental                      false
% 3.72/1.01  --bmc1_axioms                           reachable_all
% 3.72/1.01  --bmc1_min_bound                        0
% 3.72/1.01  --bmc1_max_bound                        -1
% 3.72/1.01  --bmc1_max_bound_default                -1
% 3.72/1.01  --bmc1_symbol_reachability              true
% 3.72/1.01  --bmc1_property_lemmas                  false
% 3.72/1.01  --bmc1_k_induction                      false
% 3.72/1.01  --bmc1_non_equiv_states                 false
% 3.72/1.01  --bmc1_deadlock                         false
% 3.72/1.01  --bmc1_ucm                              false
% 3.72/1.01  --bmc1_add_unsat_core                   none
% 3.72/1.01  --bmc1_unsat_core_children              false
% 3.72/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/1.01  --bmc1_out_stat                         full
% 3.72/1.01  --bmc1_ground_init                      false
% 3.72/1.01  --bmc1_pre_inst_next_state              false
% 3.72/1.01  --bmc1_pre_inst_state                   false
% 3.72/1.01  --bmc1_pre_inst_reach_state             false
% 3.72/1.01  --bmc1_out_unsat_core                   false
% 3.72/1.01  --bmc1_aig_witness_out                  false
% 3.72/1.01  --bmc1_verbose                          false
% 3.72/1.01  --bmc1_dump_clauses_tptp                false
% 3.72/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.72/1.01  --bmc1_dump_file                        -
% 3.72/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.72/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.72/1.01  --bmc1_ucm_extend_mode                  1
% 3.72/1.01  --bmc1_ucm_init_mode                    2
% 3.72/1.01  --bmc1_ucm_cone_mode                    none
% 3.72/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.72/1.01  --bmc1_ucm_relax_model                  4
% 3.72/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.72/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/1.01  --bmc1_ucm_layered_model                none
% 3.72/1.01  --bmc1_ucm_max_lemma_size               10
% 3.72/1.01  
% 3.72/1.01  ------ AIG Options
% 3.72/1.01  
% 3.72/1.01  --aig_mode                              false
% 3.72/1.01  
% 3.72/1.01  ------ Instantiation Options
% 3.72/1.01  
% 3.72/1.01  --instantiation_flag                    true
% 3.72/1.01  --inst_sos_flag                         false
% 3.72/1.01  --inst_sos_phase                        true
% 3.72/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/1.01  --inst_lit_sel_side                     none
% 3.72/1.01  --inst_solver_per_active                1400
% 3.72/1.01  --inst_solver_calls_frac                1.
% 3.72/1.01  --inst_passive_queue_type               priority_queues
% 3.72/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/1.01  --inst_passive_queues_freq              [25;2]
% 3.72/1.01  --inst_dismatching                      true
% 3.72/1.01  --inst_eager_unprocessed_to_passive     true
% 3.72/1.01  --inst_prop_sim_given                   true
% 3.72/1.01  --inst_prop_sim_new                     false
% 3.72/1.01  --inst_subs_new                         false
% 3.72/1.01  --inst_eq_res_simp                      false
% 3.72/1.01  --inst_subs_given                       false
% 3.72/1.01  --inst_orphan_elimination               true
% 3.72/1.01  --inst_learning_loop_flag               true
% 3.72/1.01  --inst_learning_start                   3000
% 3.72/1.01  --inst_learning_factor                  2
% 3.72/1.01  --inst_start_prop_sim_after_learn       3
% 3.72/1.01  --inst_sel_renew                        solver
% 3.72/1.01  --inst_lit_activity_flag                true
% 3.72/1.01  --inst_restr_to_given                   false
% 3.72/1.01  --inst_activity_threshold               500
% 3.72/1.01  --inst_out_proof                        true
% 3.72/1.01  
% 3.72/1.01  ------ Resolution Options
% 3.72/1.01  
% 3.72/1.01  --resolution_flag                       false
% 3.72/1.01  --res_lit_sel                           adaptive
% 3.72/1.01  --res_lit_sel_side                      none
% 3.72/1.01  --res_ordering                          kbo
% 3.72/1.01  --res_to_prop_solver                    active
% 3.72/1.01  --res_prop_simpl_new                    false
% 3.72/1.01  --res_prop_simpl_given                  true
% 3.72/1.01  --res_passive_queue_type                priority_queues
% 3.72/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/1.01  --res_passive_queues_freq               [15;5]
% 3.72/1.01  --res_forward_subs                      full
% 3.72/1.01  --res_backward_subs                     full
% 3.72/1.01  --res_forward_subs_resolution           true
% 3.72/1.01  --res_backward_subs_resolution          true
% 3.72/1.01  --res_orphan_elimination                true
% 3.72/1.01  --res_time_limit                        2.
% 3.72/1.01  --res_out_proof                         true
% 3.72/1.01  
% 3.72/1.01  ------ Superposition Options
% 3.72/1.01  
% 3.72/1.01  --superposition_flag                    true
% 3.72/1.01  --sup_passive_queue_type                priority_queues
% 3.72/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.72/1.01  --demod_completeness_check              fast
% 3.72/1.01  --demod_use_ground                      true
% 3.72/1.01  --sup_to_prop_solver                    passive
% 3.72/1.01  --sup_prop_simpl_new                    true
% 3.72/1.01  --sup_prop_simpl_given                  true
% 3.72/1.01  --sup_fun_splitting                     false
% 3.72/1.01  --sup_smt_interval                      50000
% 3.72/1.01  
% 3.72/1.01  ------ Superposition Simplification Setup
% 3.72/1.01  
% 3.72/1.01  --sup_indices_passive                   []
% 3.72/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.01  --sup_full_bw                           [BwDemod]
% 3.72/1.01  --sup_immed_triv                        [TrivRules]
% 3.72/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.01  --sup_immed_bw_main                     []
% 3.72/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.01  
% 3.72/1.01  ------ Combination Options
% 3.72/1.01  
% 3.72/1.01  --comb_res_mult                         3
% 3.72/1.01  --comb_sup_mult                         2
% 3.72/1.01  --comb_inst_mult                        10
% 3.72/1.01  
% 3.72/1.01  ------ Debug Options
% 3.72/1.01  
% 3.72/1.01  --dbg_backtrace                         false
% 3.72/1.01  --dbg_dump_prop_clauses                 false
% 3.72/1.01  --dbg_dump_prop_clauses_file            -
% 3.72/1.01  --dbg_out_stat                          false
% 3.72/1.01  
% 3.72/1.01  
% 3.72/1.01  
% 3.72/1.01  
% 3.72/1.01  ------ Proving...
% 3.72/1.01  
% 3.72/1.01  
% 3.72/1.01  % SZS status Theorem for theBenchmark.p
% 3.72/1.01  
% 3.72/1.01   Resolution empty clause
% 3.72/1.01  
% 3.72/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/1.01  
% 3.72/1.01  fof(f21,conjecture,(
% 3.72/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f22,negated_conjecture,(
% 3.72/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.72/1.01    inference(negated_conjecture,[],[f21])).
% 3.72/1.01  
% 3.72/1.01  fof(f40,plain,(
% 3.72/1.01    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.72/1.01    inference(ennf_transformation,[],[f22])).
% 3.72/1.01  
% 3.72/1.01  fof(f41,plain,(
% 3.72/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.72/1.01    inference(flattening,[],[f40])).
% 3.72/1.01  
% 3.72/1.01  fof(f51,plain,(
% 3.72/1.01    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.72/1.01    introduced(choice_axiom,[])).
% 3.72/1.01  
% 3.72/1.01  fof(f50,plain,(
% 3.72/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.72/1.01    introduced(choice_axiom,[])).
% 3.72/1.01  
% 3.72/1.01  fof(f52,plain,(
% 3.72/1.01    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.72/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f51,f50])).
% 3.72/1.01  
% 3.72/1.01  fof(f94,plain,(
% 3.72/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f89,plain,(
% 3.72/1.01    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f5,axiom,(
% 3.72/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f46,plain,(
% 3.72/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.72/1.01    inference(nnf_transformation,[],[f5])).
% 3.72/1.01  
% 3.72/1.01  fof(f61,plain,(
% 3.72/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.72/1.01    inference(cnf_transformation,[],[f46])).
% 3.72/1.01  
% 3.72/1.01  fof(f6,axiom,(
% 3.72/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f24,plain,(
% 3.72/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.72/1.01    inference(ennf_transformation,[],[f6])).
% 3.72/1.01  
% 3.72/1.01  fof(f63,plain,(
% 3.72/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f24])).
% 3.72/1.01  
% 3.72/1.01  fof(f62,plain,(
% 3.72/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f46])).
% 3.72/1.01  
% 3.72/1.01  fof(f8,axiom,(
% 3.72/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f66,plain,(
% 3.72/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.72/1.01    inference(cnf_transformation,[],[f8])).
% 3.72/1.01  
% 3.72/1.01  fof(f12,axiom,(
% 3.72/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f26,plain,(
% 3.72/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/1.01    inference(ennf_transformation,[],[f12])).
% 3.72/1.01  
% 3.72/1.01  fof(f72,plain,(
% 3.72/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/1.01    inference(cnf_transformation,[],[f26])).
% 3.72/1.01  
% 3.72/1.01  fof(f16,axiom,(
% 3.72/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f32,plain,(
% 3.72/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.72/1.01    inference(ennf_transformation,[],[f16])).
% 3.72/1.01  
% 3.72/1.01  fof(f33,plain,(
% 3.72/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.72/1.01    inference(flattening,[],[f32])).
% 3.72/1.01  
% 3.72/1.01  fof(f49,plain,(
% 3.72/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.72/1.01    inference(nnf_transformation,[],[f33])).
% 3.72/1.01  
% 3.72/1.01  fof(f79,plain,(
% 3.72/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f49])).
% 3.72/1.01  
% 3.72/1.01  fof(f15,axiom,(
% 3.72/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f30,plain,(
% 3.72/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/1.01    inference(ennf_transformation,[],[f15])).
% 3.72/1.01  
% 3.72/1.01  fof(f31,plain,(
% 3.72/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/1.01    inference(flattening,[],[f30])).
% 3.72/1.01  
% 3.72/1.01  fof(f78,plain,(
% 3.72/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/1.01    inference(cnf_transformation,[],[f31])).
% 3.72/1.01  
% 3.72/1.01  fof(f88,plain,(
% 3.72/1.01    v3_funct_2(sK1,sK0,sK0)),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f86,plain,(
% 3.72/1.01    v1_funct_1(sK1)),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f13,axiom,(
% 3.72/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f27,plain,(
% 3.72/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/1.01    inference(ennf_transformation,[],[f13])).
% 3.72/1.01  
% 3.72/1.01  fof(f73,plain,(
% 3.72/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/1.01    inference(cnf_transformation,[],[f27])).
% 3.72/1.01  
% 3.72/1.01  fof(f20,axiom,(
% 3.72/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f38,plain,(
% 3.72/1.01    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.72/1.01    inference(ennf_transformation,[],[f20])).
% 3.72/1.01  
% 3.72/1.01  fof(f39,plain,(
% 3.72/1.01    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.72/1.01    inference(flattening,[],[f38])).
% 3.72/1.01  
% 3.72/1.01  fof(f85,plain,(
% 3.72/1.01    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f39])).
% 3.72/1.01  
% 3.72/1.01  fof(f19,axiom,(
% 3.72/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f36,plain,(
% 3.72/1.01    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.72/1.01    inference(ennf_transformation,[],[f19])).
% 3.72/1.01  
% 3.72/1.01  fof(f37,plain,(
% 3.72/1.01    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.72/1.01    inference(flattening,[],[f36])).
% 3.72/1.01  
% 3.72/1.01  fof(f83,plain,(
% 3.72/1.01    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f37])).
% 3.72/1.01  
% 3.72/1.01  fof(f87,plain,(
% 3.72/1.01    v1_funct_2(sK1,sK0,sK0)),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f90,plain,(
% 3.72/1.01    v1_funct_1(sK2)),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f91,plain,(
% 3.72/1.01    v1_funct_2(sK2,sK0,sK0)),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f93,plain,(
% 3.72/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f95,plain,(
% 3.72/1.01    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.72/1.01    inference(cnf_transformation,[],[f52])).
% 3.72/1.01  
% 3.72/1.01  fof(f17,axiom,(
% 3.72/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f34,plain,(
% 3.72/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.72/1.01    inference(ennf_transformation,[],[f17])).
% 3.72/1.01  
% 3.72/1.01  fof(f35,plain,(
% 3.72/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.72/1.01    inference(flattening,[],[f34])).
% 3.72/1.01  
% 3.72/1.01  fof(f81,plain,(
% 3.72/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f35])).
% 3.72/1.01  
% 3.72/1.01  fof(f14,axiom,(
% 3.72/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f28,plain,(
% 3.72/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.72/1.01    inference(ennf_transformation,[],[f14])).
% 3.72/1.01  
% 3.72/1.01  fof(f29,plain,(
% 3.72/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/1.01    inference(flattening,[],[f28])).
% 3.72/1.01  
% 3.72/1.01  fof(f48,plain,(
% 3.72/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/1.01    inference(nnf_transformation,[],[f29])).
% 3.72/1.01  
% 3.72/1.01  fof(f75,plain,(
% 3.72/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/1.01    inference(cnf_transformation,[],[f48])).
% 3.72/1.01  
% 3.72/1.01  fof(f104,plain,(
% 3.72/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/1.01    inference(equality_resolution,[],[f75])).
% 3.72/1.01  
% 3.72/1.01  fof(f4,axiom,(
% 3.72/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f44,plain,(
% 3.72/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.72/1.01    inference(nnf_transformation,[],[f4])).
% 3.72/1.01  
% 3.72/1.01  fof(f45,plain,(
% 3.72/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.72/1.01    inference(flattening,[],[f44])).
% 3.72/1.01  
% 3.72/1.01  fof(f59,plain,(
% 3.72/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.72/1.01    inference(cnf_transformation,[],[f45])).
% 3.72/1.01  
% 3.72/1.01  fof(f103,plain,(
% 3.72/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.72/1.01    inference(equality_resolution,[],[f59])).
% 3.72/1.01  
% 3.72/1.01  fof(f60,plain,(
% 3.72/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.72/1.01    inference(cnf_transformation,[],[f45])).
% 3.72/1.01  
% 3.72/1.01  fof(f102,plain,(
% 3.72/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.72/1.01    inference(equality_resolution,[],[f60])).
% 3.72/1.01  
% 3.72/1.01  fof(f2,axiom,(
% 3.72/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f42,plain,(
% 3.72/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/1.01    inference(nnf_transformation,[],[f2])).
% 3.72/1.01  
% 3.72/1.01  fof(f43,plain,(
% 3.72/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/1.01    inference(flattening,[],[f42])).
% 3.72/1.01  
% 3.72/1.01  fof(f54,plain,(
% 3.72/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.72/1.01    inference(cnf_transformation,[],[f43])).
% 3.72/1.01  
% 3.72/1.01  fof(f101,plain,(
% 3.72/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.72/1.01    inference(equality_resolution,[],[f54])).
% 3.72/1.01  
% 3.72/1.01  fof(f71,plain,(
% 3.72/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/1.01    inference(cnf_transformation,[],[f26])).
% 3.72/1.01  
% 3.72/1.01  fof(f7,axiom,(
% 3.72/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f25,plain,(
% 3.72/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.72/1.01    inference(ennf_transformation,[],[f7])).
% 3.72/1.01  
% 3.72/1.01  fof(f47,plain,(
% 3.72/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.72/1.01    inference(nnf_transformation,[],[f25])).
% 3.72/1.01  
% 3.72/1.01  fof(f64,plain,(
% 3.72/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f47])).
% 3.72/1.01  
% 3.72/1.01  fof(f10,axiom,(
% 3.72/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f69,plain,(
% 3.72/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.72/1.01    inference(cnf_transformation,[],[f10])).
% 3.72/1.01  
% 3.72/1.01  fof(f18,axiom,(
% 3.72/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f82,plain,(
% 3.72/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f18])).
% 3.72/1.01  
% 3.72/1.01  fof(f98,plain,(
% 3.72/1.01    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.72/1.01    inference(definition_unfolding,[],[f69,f82])).
% 3.72/1.01  
% 3.72/1.01  fof(f9,axiom,(
% 3.72/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f67,plain,(
% 3.72/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.72/1.01    inference(cnf_transformation,[],[f9])).
% 3.72/1.01  
% 3.72/1.01  fof(f97,plain,(
% 3.72/1.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.72/1.01    inference(definition_unfolding,[],[f67,f82])).
% 3.72/1.01  
% 3.72/1.01  fof(f56,plain,(
% 3.72/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.72/1.01    inference(cnf_transformation,[],[f43])).
% 3.72/1.01  
% 3.72/1.01  fof(f11,axiom,(
% 3.72/1.01    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.01  
% 3.72/1.01  fof(f70,plain,(
% 3.72/1.01    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.72/1.01    inference(cnf_transformation,[],[f11])).
% 3.72/1.01  
% 3.72/1.01  fof(f99,plain,(
% 3.72/1.01    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.72/1.01    inference(definition_unfolding,[],[f70,f82,f82])).
% 3.72/1.01  
% 3.72/1.01  cnf(c_33,negated_conjecture,
% 3.72/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.72/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2030,plain,
% 3.72/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_38,negated_conjecture,
% 3.72/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.72/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2026,plain,
% 3.72/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_9,plain,
% 3.72/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.72/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2036,plain,
% 3.72/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.72/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_3532,plain,
% 3.72/1.01      ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_2026,c_2036]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10,plain,
% 3.72/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_8,plain,
% 3.72/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_276,plain,
% 3.72/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.72/1.01      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_277,plain,
% 3.72/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/1.01      inference(renaming,[status(thm)],[c_276]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_349,plain,
% 3.72/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.72/1.01      inference(bin_hyper_res,[status(thm)],[c_10,c_277]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2022,plain,
% 3.72/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.72/1.01      | v1_relat_1(X1) != iProver_top
% 3.72/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7038,plain,
% 3.72/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.72/1.01      | v1_relat_1(sK1) = iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_3532,c_2022]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_13,plain,
% 3.72/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.72/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_95,plain,
% 3.72/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_97,plain,
% 3.72/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.72/1.01      inference(instantiation,[status(thm)],[c_95]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7162,plain,
% 3.72/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 3.72/1.01      inference(global_propositional_subsumption,[status(thm)],[c_7038,c_97]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_18,plain,
% 3.72/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.72/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_27,plain,
% 3.72/1.01      ( ~ v2_funct_2(X0,X1)
% 3.72/1.01      | ~ v5_relat_1(X0,X1)
% 3.72/1.01      | ~ v1_relat_1(X0)
% 3.72/1.01      | k2_relat_1(X0) = X1 ),
% 3.72/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_23,plain,
% 3.72/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.72/1.01      | v2_funct_2(X0,X2)
% 3.72/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/1.01      | ~ v1_funct_1(X0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_39,negated_conjecture,
% 3.72/1.01      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_537,plain,
% 3.72/1.01      ( v2_funct_2(X0,X1)
% 3.72/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.72/1.01      | ~ v1_funct_1(X0)
% 3.72/1.01      | sK1 != X0
% 3.72/1.01      | sK0 != X1
% 3.72/1.01      | sK0 != X2 ),
% 3.72/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_39]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_538,plain,
% 3.72/1.01      ( v2_funct_2(sK1,sK0)
% 3.72/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.72/1.01      | ~ v1_funct_1(sK1) ),
% 3.72/1.01      inference(unflattening,[status(thm)],[c_537]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_41,negated_conjecture,
% 3.72/1.01      ( v1_funct_1(sK1) ),
% 3.72/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_540,plain,
% 3.72/1.01      ( v2_funct_2(sK1,sK0) ),
% 3.72/1.01      inference(global_propositional_subsumption,
% 3.72/1.01                [status(thm)],
% 3.72/1.01                [c_538,c_41,c_38]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_623,plain,
% 3.72/1.01      ( ~ v5_relat_1(X0,X1)
% 3.72/1.01      | ~ v1_relat_1(X0)
% 3.72/1.01      | k2_relat_1(X0) = X1
% 3.72/1.01      | sK1 != X0
% 3.72/1.01      | sK0 != X1 ),
% 3.72/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_540]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_624,plain,
% 3.72/1.01      ( ~ v5_relat_1(sK1,sK0) | ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 3.72/1.01      inference(unflattening,[status(thm)],[c_623]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_670,plain,
% 3.72/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/1.01      | ~ v1_relat_1(sK1)
% 3.72/1.01      | k2_relat_1(sK1) = sK0
% 3.72/1.01      | sK1 != X0
% 3.72/1.01      | sK0 != X2 ),
% 3.72/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_624]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_671,plain,
% 3.72/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.72/1.01      | ~ v1_relat_1(sK1)
% 3.72/1.01      | k2_relat_1(sK1) = sK0 ),
% 3.72/1.01      inference(unflattening,[status(thm)],[c_670]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_673,plain,
% 3.72/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.72/1.01      | ~ v1_relat_1(sK1)
% 3.72/1.01      | k2_relat_1(sK1) = sK0 ),
% 3.72/1.01      inference(instantiation,[status(thm)],[c_671]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_675,plain,
% 3.72/1.01      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 3.72/1.01      inference(global_propositional_subsumption,
% 3.72/1.01                [status(thm)],
% 3.72/1.01                [c_671,c_38,c_673]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2018,plain,
% 3.72/1.01      ( k2_relat_1(sK1) = sK0 | v1_relat_1(sK1) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7167,plain,
% 3.72/1.01      ( k2_relat_1(sK1) = sK0 ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_7162,c_2018]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_20,plain,
% 3.72/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2034,plain,
% 3.72/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.72/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_4944,plain,
% 3.72/1.01      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_2026,c_2034]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_31,plain,
% 3.72/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.72/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.72/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.72/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.72/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.72/1.01      | ~ v2_funct_1(X2)
% 3.72/1.01      | ~ v1_funct_1(X2)
% 3.72/1.01      | ~ v1_funct_1(X3)
% 3.72/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.72/1.01      | k2_funct_1(X2) = X3
% 3.72/1.01      | k1_xboole_0 = X1
% 3.72/1.01      | k1_xboole_0 = X0 ),
% 3.72/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_30,plain,
% 3.72/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.72/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.72/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.72/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.72/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.72/1.01      | v2_funct_1(X2)
% 3.72/1.01      | ~ v1_funct_1(X2)
% 3.72/1.01      | ~ v1_funct_1(X3) ),
% 3.72/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_206,plain,
% 3.72/1.01      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.72/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.72/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.72/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.72/1.01      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.72/1.01      | ~ v1_funct_1(X2)
% 3.72/1.01      | ~ v1_funct_1(X3)
% 3.72/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.72/1.01      | k2_funct_1(X2) = X3
% 3.72/1.01      | k1_xboole_0 = X1
% 3.72/1.01      | k1_xboole_0 = X0 ),
% 3.72/1.01      inference(global_propositional_subsumption,[status(thm)],[c_31,c_30]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_207,plain,
% 3.72/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.72/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.72/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.72/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.72/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.72/1.01      | ~ v1_funct_1(X2)
% 3.72/1.01      | ~ v1_funct_1(X3)
% 3.72/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.72/1.01      | k2_funct_1(X2) = X3
% 3.72/1.01      | k1_xboole_0 = X1
% 3.72/1.01      | k1_xboole_0 = X0 ),
% 3.72/1.01      inference(renaming,[status(thm)],[c_206]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2023,plain,
% 3.72/1.01      ( k2_relset_1(X0,X1,X2) != X1
% 3.72/1.01      | k2_funct_1(X2) = X3
% 3.72/1.01      | k1_xboole_0 = X1
% 3.72/1.01      | k1_xboole_0 = X0
% 3.72/1.01      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.72/1.01      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.72/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.72/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.72/1.01      | v1_funct_1(X2) != iProver_top
% 3.72/1.01      | v1_funct_1(X3) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_5355,plain,
% 3.72/1.01      ( k2_funct_1(sK1) = X0
% 3.72/1.01      | k2_relat_1(sK1) != sK0
% 3.72/1.01      | sK0 = k1_xboole_0
% 3.72/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.72/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.72/1.01      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.72/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.72/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.72/1.01      | v1_funct_1(X0) != iProver_top
% 3.72/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_4944,c_2023]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_42,plain,
% 3.72/1.01      ( v1_funct_1(sK1) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_40,negated_conjecture,
% 3.72/1.01      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_43,plain,
% 3.72/1.01      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_45,plain,
% 3.72/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_6919,plain,
% 3.72/1.01      ( v1_funct_1(X0) != iProver_top
% 3.72/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.72/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.72/1.01      | sK0 = k1_xboole_0
% 3.72/1.01      | k2_relat_1(sK1) != sK0
% 3.72/1.01      | k2_funct_1(sK1) = X0
% 3.72/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.72/1.01      inference(global_propositional_subsumption,
% 3.72/1.01                [status(thm)],
% 3.72/1.01                [c_5355,c_42,c_43,c_45]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_6920,plain,
% 3.72/1.01      ( k2_funct_1(sK1) = X0
% 3.72/1.01      | k2_relat_1(sK1) != sK0
% 3.72/1.01      | sK0 = k1_xboole_0
% 3.72/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.72/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.72/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.72/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.72/1.01      inference(renaming,[status(thm)],[c_6919]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_8309,plain,
% 3.72/1.01      ( k2_funct_1(sK1) = X0
% 3.72/1.01      | sK0 != sK0
% 3.72/1.01      | sK0 = k1_xboole_0
% 3.72/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.72/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.72/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.72/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.72/1.01      inference(demodulation,[status(thm)],[c_7167,c_6920]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_8313,plain,
% 3.72/1.01      ( k2_funct_1(sK1) = X0
% 3.72/1.01      | sK0 = k1_xboole_0
% 3.72/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 3.72/1.01      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 3.72/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.72/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.72/1.01      inference(equality_resolution_simp,[status(thm)],[c_8309]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10455,plain,
% 3.72/1.01      ( k2_funct_1(sK1) = sK2
% 3.72/1.01      | sK0 = k1_xboole_0
% 3.72/1.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.72/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.72/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_2030,c_8313]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_37,negated_conjecture,
% 3.72/1.01      ( v1_funct_1(sK2) ),
% 3.72/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_36,negated_conjecture,
% 3.72/1.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_34,negated_conjecture,
% 3.72/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.72/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10456,plain,
% 3.72/1.01      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.72/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.72/1.01      | ~ v1_funct_1(sK2)
% 3.72/1.01      | k2_funct_1(sK1) = sK2
% 3.72/1.01      | sK0 = k1_xboole_0 ),
% 3.72/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_10455]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10458,plain,
% 3.72/1.01      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.72/1.01      inference(global_propositional_subsumption,
% 3.72/1.01                [status(thm)],
% 3.72/1.01                [c_10455,c_46,c_47,c_49]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10459,plain,
% 3.72/1.01      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.72/1.01      inference(renaming,[status(thm)],[c_10458]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_32,negated_conjecture,
% 3.72/1.01      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.72/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2031,plain,
% 3.72/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_28,plain,
% 3.72/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.72/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.72/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.72/1.01      | ~ v1_funct_1(X0)
% 3.72/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_556,plain,
% 3.72/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.72/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.72/1.01      | ~ v1_funct_1(X0)
% 3.72/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.72/1.01      | sK1 != X0
% 3.72/1.01      | sK0 != X1 ),
% 3.72/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_557,plain,
% 3.72/1.01      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.72/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.72/1.01      | ~ v1_funct_1(sK1)
% 3.72/1.01      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.72/1.01      inference(unflattening,[status(thm)],[c_556]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_559,plain,
% 3.72/1.01      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.72/1.01      inference(global_propositional_subsumption,
% 3.72/1.01                [status(thm)],
% 3.72/1.01                [c_557,c_41,c_40,c_38]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2084,plain,
% 3.72/1.01      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.72/1.01      inference(light_normalisation,[status(thm)],[c_2031,c_559]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10462,plain,
% 3.72/1.01      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_10459,c_2084]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_49,plain,
% 3.72/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_21,plain,
% 3.72/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.72/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.72/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2275,plain,
% 3.72/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.72/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.72/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2276,plain,
% 3.72/1.01      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.72/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2275]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10864,plain,
% 3.72/1.01      ( sK0 = k1_xboole_0 ),
% 3.72/1.01      inference(global_propositional_subsumption,
% 3.72/1.01                [status(thm)],
% 3.72/1.01                [c_10462,c_49,c_2276]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2029,plain,
% 3.72/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_3531,plain,
% 3.72/1.01      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_2029,c_2036]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10902,plain,
% 3.72/1.01      ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.72/1.01      inference(demodulation,[status(thm)],[c_10864,c_3531]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_6,plain,
% 3.72/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.72/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10931,plain,
% 3.72/1.01      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.72/1.01      inference(demodulation,[status(thm)],[c_10902,c_6]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_5,plain,
% 3.72/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.72/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f101]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2039,plain,
% 3.72/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2037,plain,
% 3.72/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.72/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_19,plain,
% 3.72/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.72/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_12,plain,
% 3.72/1.01      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_468,plain,
% 3.72/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.72/1.01      | ~ v1_relat_1(X0) ),
% 3.72/1.01      inference(resolution,[status(thm)],[c_19,c_12]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2021,plain,
% 3.72/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.72/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.72/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_4900,plain,
% 3.72/1.01      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.72/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.72/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_2037,c_2021]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7302,plain,
% 3.72/1.01      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top
% 3.72/1.01      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_2039,c_4900]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7637,plain,
% 3.72/1.01      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
% 3.72/1.01      inference(global_propositional_subsumption,[status(thm)],[c_7302,c_95]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7644,plain,
% 3.72/1.01      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_5,c_7637]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_16,plain,
% 3.72/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.72/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_15,plain,
% 3.72/1.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.72/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2671,plain,
% 3.72/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_16,c_15]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7676,plain,
% 3.72/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.72/1.01      inference(light_normalisation,[status(thm)],[c_7644,c_2671]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_1,plain,
% 3.72/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.72/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2040,plain,
% 3.72/1.01      ( X0 = X1
% 3.72/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.72/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7697,plain,
% 3.72/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_7676,c_2040]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_11398,plain,
% 3.72/1.01      ( sK2 = k1_xboole_0 ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_10931,c_7697]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10903,plain,
% 3.72/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.72/1.01      inference(demodulation,[status(thm)],[c_10864,c_2084]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_13505,plain,
% 3.72/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.72/1.01      inference(demodulation,[status(thm)],[c_11398,c_10903]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_17,plain,
% 3.72/1.01      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.72/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_3389,plain,
% 3.72/1.01      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_16,c_17]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_3390,plain,
% 3.72/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.72/1.01      inference(light_normalisation,[status(thm)],[c_3389,c_16]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10901,plain,
% 3.72/1.01      ( r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.72/1.01      inference(demodulation,[status(thm)],[c_10864,c_3532]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_10934,plain,
% 3.72/1.01      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.72/1.01      inference(demodulation,[status(thm)],[c_10901,c_6]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_11458,plain,
% 3.72/1.01      ( sK1 = k1_xboole_0 ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_10934,c_7697]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_14345,plain,
% 3.72/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.72/1.01      inference(light_normalisation,[status(thm)],[c_13505,c_3390,c_11458]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_2033,plain,
% 3.72/1.01      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.72/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_4059,plain,
% 3.72/1.01      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.72/1.01      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_2037,c_2033]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_7699,plain,
% 3.72/1.01      ( r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.72/1.01      inference(superposition,[status(thm)],[c_7676,c_4059]) ).
% 3.72/1.01  
% 3.72/1.01  cnf(c_14347,plain,
% 3.72/1.01      ( $false ),
% 3.72/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_14345,c_7699]) ).
% 3.72/1.01  
% 3.72/1.01  
% 3.72/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/1.01  
% 3.72/1.01  ------                               Statistics
% 3.72/1.01  
% 3.72/1.01  ------ General
% 3.72/1.01  
% 3.72/1.01  abstr_ref_over_cycles:                  0
% 3.72/1.01  abstr_ref_under_cycles:                 0
% 3.72/1.01  gc_basic_clause_elim:                   0
% 3.72/1.01  forced_gc_time:                         0
% 3.72/1.01  parsing_time:                           0.017
% 3.72/1.01  unif_index_cands_time:                  0.
% 3.72/1.01  unif_index_add_time:                    0.
% 3.72/1.01  orderings_time:                         0.
% 3.72/1.01  out_proof_time:                         0.011
% 3.72/1.01  total_time:                             0.503
% 3.72/1.01  num_of_symbols:                         56
% 3.72/1.01  num_of_terms:                           16787
% 3.72/1.01  
% 3.72/1.01  ------ Preprocessing
% 3.72/1.01  
% 3.72/1.01  num_of_splits:                          0
% 3.72/1.01  num_of_split_atoms:                     0
% 3.72/1.01  num_of_reused_defs:                     0
% 3.72/1.01  num_eq_ax_congr_red:                    17
% 3.72/1.01  num_of_sem_filtered_clauses:            3
% 3.72/1.01  num_of_subtypes:                        0
% 3.72/1.01  monotx_restored_types:                  0
% 3.72/1.01  sat_num_of_epr_types:                   0
% 3.72/1.01  sat_num_of_non_cyclic_types:            0
% 3.72/1.01  sat_guarded_non_collapsed_types:        0
% 3.72/1.01  num_pure_diseq_elim:                    0
% 3.72/1.01  simp_replaced_by:                       0
% 3.72/1.01  res_preprocessed:                       174
% 3.72/1.01  prep_upred:                             0
% 3.72/1.01  prep_unflattend:                        62
% 3.72/1.01  smt_new_axioms:                         0
% 3.72/1.01  pred_elim_cands:                        7
% 3.72/1.01  pred_elim:                              4
% 3.72/1.01  pred_elim_cl:                           5
% 3.72/1.01  pred_elim_cycles:                       7
% 3.72/1.01  merged_defs:                            8
% 3.72/1.01  merged_defs_ncl:                        0
% 3.72/1.01  bin_hyper_res:                          9
% 3.72/1.01  prep_cycles:                            4
% 3.72/1.01  pred_elim_time:                         0.016
% 3.72/1.01  splitting_time:                         0.
% 3.72/1.01  sem_filter_time:                        0.
% 3.72/1.01  monotx_time:                            0.
% 3.72/1.01  subtype_inf_time:                       0.
% 3.72/1.01  
% 3.72/1.01  ------ Problem properties
% 3.72/1.01  
% 3.72/1.01  clauses:                                33
% 3.72/1.01  conjectures:                            8
% 3.72/1.01  epr:                                    9
% 3.72/1.01  horn:                                   31
% 3.72/1.01  ground:                                 14
% 3.72/1.01  unary:                                  19
% 3.72/1.01  binary:                                 6
% 3.72/1.01  lits:                                   70
% 3.72/1.01  lits_eq:                                22
% 3.72/1.01  fd_pure:                                0
% 3.72/1.01  fd_pseudo:                              0
% 3.72/1.01  fd_cond:                                1
% 3.72/1.01  fd_pseudo_cond:                         5
% 3.72/1.01  ac_symbols:                             0
% 3.72/1.01  
% 3.72/1.01  ------ Propositional Solver
% 3.72/1.01  
% 3.72/1.01  prop_solver_calls:                      27
% 3.72/1.01  prop_fast_solver_calls:                 1468
% 3.72/1.01  smt_solver_calls:                       0
% 3.72/1.01  smt_fast_solver_calls:                  0
% 3.72/1.01  prop_num_of_clauses:                    5997
% 3.72/1.01  prop_preprocess_simplified:             13445
% 3.72/1.01  prop_fo_subsumed:                       43
% 3.72/1.01  prop_solver_time:                       0.
% 3.72/1.01  smt_solver_time:                        0.
% 3.72/1.01  smt_fast_solver_time:                   0.
% 3.72/1.01  prop_fast_solver_time:                  0.
% 3.72/1.01  prop_unsat_core_time:                   0.
% 3.72/1.01  
% 3.72/1.01  ------ QBF
% 3.72/1.01  
% 3.72/1.01  qbf_q_res:                              0
% 3.72/1.01  qbf_num_tautologies:                    0
% 3.72/1.01  qbf_prep_cycles:                        0
% 3.72/1.01  
% 3.72/1.01  ------ BMC1
% 3.72/1.01  
% 3.72/1.01  bmc1_current_bound:                     -1
% 3.72/1.01  bmc1_last_solved_bound:                 -1
% 3.72/1.01  bmc1_unsat_core_size:                   -1
% 3.72/1.01  bmc1_unsat_core_parents_size:           -1
% 3.72/1.01  bmc1_merge_next_fun:                    0
% 3.72/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.72/1.01  
% 3.72/1.01  ------ Instantiation
% 3.72/1.01  
% 3.72/1.01  inst_num_of_clauses:                    1691
% 3.72/1.01  inst_num_in_passive:                    105
% 3.72/1.01  inst_num_in_active:                     813
% 3.72/1.01  inst_num_in_unprocessed:                773
% 3.72/1.01  inst_num_of_loops:                      820
% 3.72/1.01  inst_num_of_learning_restarts:          0
% 3.72/1.01  inst_num_moves_active_passive:          6
% 3.72/1.01  inst_lit_activity:                      0
% 3.72/1.01  inst_lit_activity_moves:                0
% 3.72/1.01  inst_num_tautologies:                   0
% 3.72/1.01  inst_num_prop_implied:                  0
% 3.72/1.01  inst_num_existing_simplified:           0
% 3.72/1.01  inst_num_eq_res_simplified:             0
% 3.72/1.01  inst_num_child_elim:                    0
% 3.72/1.01  inst_num_of_dismatching_blockings:      442
% 3.72/1.01  inst_num_of_non_proper_insts:           1827
% 3.72/1.01  inst_num_of_duplicates:                 0
% 3.72/1.01  inst_inst_num_from_inst_to_res:         0
% 3.72/1.01  inst_dismatching_checking_time:         0.
% 3.72/1.01  
% 3.72/1.01  ------ Resolution
% 3.72/1.01  
% 3.72/1.01  res_num_of_clauses:                     0
% 3.72/1.01  res_num_in_passive:                     0
% 3.72/1.01  res_num_in_active:                      0
% 3.72/1.01  res_num_of_loops:                       178
% 3.72/1.01  res_forward_subset_subsumed:            141
% 3.72/1.01  res_backward_subset_subsumed:           0
% 3.72/1.01  res_forward_subsumed:                   0
% 3.72/1.01  res_backward_subsumed:                  0
% 3.72/1.01  res_forward_subsumption_resolution:     1
% 3.72/1.01  res_backward_subsumption_resolution:    0
% 3.72/1.01  res_clause_to_clause_subsumption:       707
% 3.72/1.01  res_orphan_elimination:                 0
% 3.72/1.01  res_tautology_del:                      90
% 3.72/1.01  res_num_eq_res_simplified:              0
% 3.72/1.01  res_num_sel_changes:                    0
% 3.72/1.01  res_moves_from_active_to_pass:          0
% 3.72/1.01  
% 3.72/1.01  ------ Superposition
% 3.72/1.01  
% 3.72/1.01  sup_time_total:                         0.
% 3.72/1.01  sup_time_generating:                    0.
% 3.72/1.01  sup_time_sim_full:                      0.
% 3.72/1.01  sup_time_sim_immed:                     0.
% 3.72/1.01  
% 3.72/1.01  sup_num_of_clauses:                     126
% 3.72/1.01  sup_num_in_active:                      76
% 3.72/1.01  sup_num_in_passive:                     50
% 3.72/1.01  sup_num_of_loops:                       162
% 3.72/1.01  sup_fw_superposition:                   210
% 3.72/1.01  sup_bw_superposition:                   133
% 3.72/1.01  sup_immediate_simplified:               100
% 3.72/1.01  sup_given_eliminated:                   4
% 3.72/1.01  comparisons_done:                       0
% 3.72/1.01  comparisons_avoided:                    3
% 3.72/1.01  
% 3.72/1.01  ------ Simplifications
% 3.72/1.01  
% 3.72/1.01  
% 3.72/1.01  sim_fw_subset_subsumed:                 21
% 3.72/1.01  sim_bw_subset_subsumed:                 14
% 3.72/1.01  sim_fw_subsumed:                        15
% 3.72/1.01  sim_bw_subsumed:                        1
% 3.72/1.01  sim_fw_subsumption_res:                 2
% 3.72/1.01  sim_bw_subsumption_res:                 0
% 3.72/1.01  sim_tautology_del:                      8
% 3.72/1.01  sim_eq_tautology_del:                   96
% 3.72/1.01  sim_eq_res_simp:                        2
% 3.72/1.01  sim_fw_demodulated:                     42
% 3.72/1.01  sim_bw_demodulated:                     96
% 3.72/1.01  sim_light_normalised:                   47
% 3.72/1.01  sim_joinable_taut:                      0
% 3.72/1.01  sim_joinable_simp:                      0
% 3.72/1.01  sim_ac_normalised:                      0
% 3.72/1.01  sim_smt_subsumption:                    0
% 3.72/1.01  
%------------------------------------------------------------------------------
