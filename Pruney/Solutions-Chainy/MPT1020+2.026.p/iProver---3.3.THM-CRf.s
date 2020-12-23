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
% DateTime   : Thu Dec  3 12:07:09 EST 2020

% Result     : Theorem 11.83s
% Output     : CNFRefutation 11.83s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_41)

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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f53,f52])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f46])).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f88,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f78])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f92,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f62,plain,(
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
    inference(definition_unfolding,[],[f62,f78])).

fof(f61,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f93,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f78])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1044,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1050,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7928,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1050])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9605,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7928,c_40])).

cnf(c_9606,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9605])).

cnf(c_9616,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_9606])).

cnf(c_1557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X3,X4,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1946,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_1948,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_9683,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9616,c_31,c_28,c_1948])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1053,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9686,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9683,c_1053])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20682,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9686,c_40,c_43])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1045,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1040,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1060,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4144,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1040,c_1060])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_288,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_24])).

cnf(c_289,plain,
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
    inference(renaming,[status(thm)],[c_288])).

cnf(c_1036,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_4670,plain,
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
    inference(superposition,[status(thm)],[c_4144,c_1036])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1412,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1488,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | v2_funct_2(sK1,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1490,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_17,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1728,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4746,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4670,c_35,c_36,c_37,c_33,c_32,c_39,c_1391,c_1412,c_1490,c_1728])).

cnf(c_4747,plain,
    ( k2_funct_1(sK1) = X0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0,sK0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4746])).

cnf(c_4758,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_4747])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4759,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4758])).

cnf(c_4868,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4758,c_40,c_41,c_43])).

cnf(c_4869,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4868])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1049,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7720,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1049])).

cnf(c_1532,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1534,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_9201,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7720,c_35,c_34,c_33,c_32,c_1534])).

cnf(c_26,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1046,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9204,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9201,c_1046])).

cnf(c_9602,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4869,c_9204])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1447,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1448,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1447])).

cnf(c_14185,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9602,c_43,c_1448])).

cnf(c_1057,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | v2_funct_2(X0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5909,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v2_funct_2(sK2,sK0) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1057])).

cnf(c_29,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1483,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | v2_funct_2(sK2,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1484,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | v2_funct_2(sK2,X1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_1486,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v2_funct_2(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_6097,plain,
    ( v2_funct_2(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5909,c_40,c_42,c_43,c_1486])).

cnf(c_1054,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | v5_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6102,plain,
    ( k2_relat_1(sK2) = sK0
    | v5_relat_1(sK2,sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6097,c_1054])).

cnf(c_1388,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1409,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1485,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_1722,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_14956,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6102,c_31,c_29,c_28,c_1388,c_1409,c_1485,c_1722])).

cnf(c_14958,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14956,c_14185])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1067,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14962,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14958,c_1067])).

cnf(c_1389,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_16692,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14962,c_43,c_1389])).

cnf(c_20686,plain,
    ( m1_subset_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20682,c_14185,c_16692])).

cnf(c_6,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1066,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2761,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1066])).

cnf(c_0,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_115,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3379,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2761,c_115])).

cnf(c_3380,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3379])).

cnf(c_3384,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3380])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1051,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3387,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3384,c_1051])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1058,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5934,plain,
    ( k1_xboole_0 = X0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3387,c_1058])).

cnf(c_20699,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20686,c_5934])).

cnf(c_9617,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_9606])).

cnf(c_1562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1956,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,X2,X3,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_1958,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_9719,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9617,c_35,c_32,c_31,c_28,c_1958])).

cnf(c_9722,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9719,c_1045])).

cnf(c_14193,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK2),k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14185,c_9722])).

cnf(c_14285,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK2),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14193,c_3384])).

cnf(c_5910,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v2_funct_2(sK1,sK0) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1057])).

cnf(c_38,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1489,plain,
    ( v3_funct_2(sK1,X0,X1) != iProver_top
    | v2_funct_2(sK1,X1) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_1491,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v2_funct_2(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_6476,plain,
    ( v2_funct_2(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5910,c_36,c_38,c_39,c_1491])).

cnf(c_6481,plain,
    ( k2_relat_1(sK1) = sK0
    | v5_relat_1(sK1,sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6476,c_1054])).

cnf(c_18528,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6481,c_35,c_33,c_32,c_1391,c_1412,c_1490,c_1728])).

cnf(c_18530,plain,
    ( k2_relat_1(sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18528,c_14185])).

cnf(c_18534,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18530,c_1067])).

cnf(c_1392,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_18720,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18534,c_39,c_1392])).

cnf(c_28817,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14285,c_16692,c_18720])).

cnf(c_20698,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = X0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20686,c_1058])).

cnf(c_28820,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28817,c_20698])).

cnf(c_28823,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20699,c_3387,c_28820])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1063,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_28839,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | k6_partfun1(k2_relat_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_28823,c_1063])).

cnf(c_3389,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3384,c_6])).

cnf(c_5,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3390,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3384,c_5])).

cnf(c_28840,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28839,c_3384,c_3389,c_3390])).

cnf(c_28841,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_28840])).

cnf(c_1068,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3388,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3384,c_1068])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1056,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5209,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1056])).

cnf(c_1453,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1454,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_1456,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_6091,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5209,c_40,c_42,c_43,c_1456])).

cnf(c_16699,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16692,c_6091])).

cnf(c_1041,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16702,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16692,c_1041])).

cnf(c_31444,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28841,c_3388,c_16699,c_16702])).

cnf(c_14197,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14185,c_9204])).

cnf(c_18868,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14197,c_16692,c_18720])).

cnf(c_31447,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31444,c_18868])).

cnf(c_1059,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3983,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3387,c_1059])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31447,c_3983])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:16:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.83/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.83/2.00  
% 11.83/2.00  ------  iProver source info
% 11.83/2.00  
% 11.83/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.83/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.83/2.00  git: non_committed_changes: false
% 11.83/2.00  git: last_make_outside_of_git: false
% 11.83/2.00  
% 11.83/2.00  ------ 
% 11.83/2.00  ------ Parsing...
% 11.83/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.83/2.00  ------ Proving...
% 11.83/2.00  ------ Problem Properties 
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  clauses                                 35
% 11.83/2.00  conjectures                             10
% 11.83/2.00  EPR                                     6
% 11.83/2.00  Horn                                    34
% 11.83/2.00  unary                                   14
% 11.83/2.00  binary                                  4
% 11.83/2.00  lits                                    108
% 11.83/2.00  lits eq                                 22
% 11.83/2.00  fd_pure                                 0
% 11.83/2.00  fd_pseudo                               0
% 11.83/2.00  fd_cond                                 2
% 11.83/2.00  fd_pseudo_cond                          4
% 11.83/2.00  AC symbols                              0
% 11.83/2.00  
% 11.83/2.00  ------ Input Options Time Limit: Unbounded
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  ------ 
% 11.83/2.00  Current options:
% 11.83/2.00  ------ 
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  ------ Proving...
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  % SZS status Theorem for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  fof(f19,conjecture,(
% 11.83/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f20,negated_conjecture,(
% 11.83/2.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 11.83/2.00    inference(negated_conjecture,[],[f19])).
% 11.83/2.00  
% 11.83/2.00  fof(f47,plain,(
% 11.83/2.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 11.83/2.00    inference(ennf_transformation,[],[f20])).
% 11.83/2.00  
% 11.83/2.00  fof(f48,plain,(
% 11.83/2.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 11.83/2.00    inference(flattening,[],[f47])).
% 11.83/2.00  
% 11.83/2.00  fof(f53,plain,(
% 11.83/2.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f52,plain,(
% 11.83/2.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f54,plain,(
% 11.83/2.00    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 11.83/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f53,f52])).
% 11.83/2.00  
% 11.83/2.00  fof(f89,plain,(
% 11.83/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f14,axiom,(
% 11.83/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f39,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.83/2.00    inference(ennf_transformation,[],[f14])).
% 11.83/2.00  
% 11.83/2.00  fof(f40,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.83/2.00    inference(flattening,[],[f39])).
% 11.83/2.00  
% 11.83/2.00  fof(f76,plain,(
% 11.83/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f40])).
% 11.83/2.00  
% 11.83/2.00  fof(f86,plain,(
% 11.83/2.00    v1_funct_1(sK2)),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f12,axiom,(
% 11.83/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f37,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.83/2.00    inference(ennf_transformation,[],[f12])).
% 11.83/2.00  
% 11.83/2.00  fof(f38,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.83/2.00    inference(flattening,[],[f37])).
% 11.83/2.00  
% 11.83/2.00  fof(f74,plain,(
% 11.83/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f38])).
% 11.83/2.00  
% 11.83/2.00  fof(f90,plain,(
% 11.83/2.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f85,plain,(
% 11.83/2.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f8,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f30,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f8])).
% 11.83/2.00  
% 11.83/2.00  fof(f65,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f30])).
% 11.83/2.00  
% 11.83/2.00  fof(f18,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f45,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.83/2.00    inference(ennf_transformation,[],[f18])).
% 11.83/2.00  
% 11.83/2.00  fof(f46,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.83/2.00    inference(flattening,[],[f45])).
% 11.83/2.00  
% 11.83/2.00  fof(f81,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f46])).
% 11.83/2.00  
% 11.83/2.00  fof(f17,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f43,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.83/2.00    inference(ennf_transformation,[],[f17])).
% 11.83/2.00  
% 11.83/2.00  fof(f44,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.83/2.00    inference(flattening,[],[f43])).
% 11.83/2.00  
% 11.83/2.00  fof(f79,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f44])).
% 11.83/2.00  
% 11.83/2.00  fof(f82,plain,(
% 11.83/2.00    v1_funct_1(sK1)),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f83,plain,(
% 11.83/2.00    v1_funct_2(sK1,sK0,sK0)),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f84,plain,(
% 11.83/2.00    v3_funct_2(sK1,sK0,sK0)),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f6,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f28,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f6])).
% 11.83/2.00  
% 11.83/2.00  fof(f63,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f28])).
% 11.83/2.00  
% 11.83/2.00  fof(f7,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f22,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.83/2.00    inference(pure_predicate_removal,[],[f7])).
% 11.83/2.00  
% 11.83/2.00  fof(f29,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f22])).
% 11.83/2.00  
% 11.83/2.00  fof(f64,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f29])).
% 11.83/2.00  
% 11.83/2.00  fof(f10,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f33,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f10])).
% 11.83/2.00  
% 11.83/2.00  fof(f34,plain,(
% 11.83/2.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(flattening,[],[f33])).
% 11.83/2.00  
% 11.83/2.00  fof(f70,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f34])).
% 11.83/2.00  
% 11.83/2.00  fof(f11,axiom,(
% 11.83/2.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f35,plain,(
% 11.83/2.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.83/2.00    inference(ennf_transformation,[],[f11])).
% 11.83/2.00  
% 11.83/2.00  fof(f36,plain,(
% 11.83/2.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(flattening,[],[f35])).
% 11.83/2.00  
% 11.83/2.00  fof(f51,plain,(
% 11.83/2.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(nnf_transformation,[],[f36])).
% 11.83/2.00  
% 11.83/2.00  fof(f71,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f51])).
% 11.83/2.00  
% 11.83/2.00  fof(f87,plain,(
% 11.83/2.00    v1_funct_2(sK2,sK0,sK0)),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f15,axiom,(
% 11.83/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f41,plain,(
% 11.83/2.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 11.83/2.00    inference(ennf_transformation,[],[f15])).
% 11.83/2.00  
% 11.83/2.00  fof(f42,plain,(
% 11.83/2.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 11.83/2.00    inference(flattening,[],[f41])).
% 11.83/2.00  
% 11.83/2.00  fof(f77,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f42])).
% 11.83/2.00  
% 11.83/2.00  fof(f91,plain,(
% 11.83/2.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f9,axiom,(
% 11.83/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f31,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.83/2.00    inference(ennf_transformation,[],[f9])).
% 11.83/2.00  
% 11.83/2.00  fof(f32,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(flattening,[],[f31])).
% 11.83/2.00  
% 11.83/2.00  fof(f50,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(nnf_transformation,[],[f32])).
% 11.83/2.00  
% 11.83/2.00  fof(f67,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f96,plain,(
% 11.83/2.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(equality_resolution,[],[f67])).
% 11.83/2.00  
% 11.83/2.00  fof(f88,plain,(
% 11.83/2.00    v3_funct_2(sK2,sK0,sK0)),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f2,axiom,(
% 11.83/2.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f23,plain,(
% 11.83/2.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 11.83/2.00    inference(ennf_transformation,[],[f2])).
% 11.83/2.00  
% 11.83/2.00  fof(f24,plain,(
% 11.83/2.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 11.83/2.00    inference(flattening,[],[f23])).
% 11.83/2.00  
% 11.83/2.00  fof(f57,plain,(
% 11.83/2.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f24])).
% 11.83/2.00  
% 11.83/2.00  fof(f4,axiom,(
% 11.83/2.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f60,plain,(
% 11.83/2.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.83/2.00    inference(cnf_transformation,[],[f4])).
% 11.83/2.00  
% 11.83/2.00  fof(f16,axiom,(
% 11.83/2.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f78,plain,(
% 11.83/2.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f16])).
% 11.83/2.00  
% 11.83/2.00  fof(f94,plain,(
% 11.83/2.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 11.83/2.00    inference(definition_unfolding,[],[f60,f78])).
% 11.83/2.00  
% 11.83/2.00  fof(f56,plain,(
% 11.83/2.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f24])).
% 11.83/2.00  
% 11.83/2.00  fof(f1,axiom,(
% 11.83/2.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f55,plain,(
% 11.83/2.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f1])).
% 11.83/2.00  
% 11.83/2.00  fof(f92,plain,(
% 11.83/2.00    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 11.83/2.00    inference(definition_unfolding,[],[f55,f78])).
% 11.83/2.00  
% 11.83/2.00  fof(f13,axiom,(
% 11.83/2.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f21,plain,(
% 11.83/2.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.83/2.00    inference(pure_predicate_removal,[],[f13])).
% 11.83/2.00  
% 11.83/2.00  fof(f75,plain,(
% 11.83/2.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f21])).
% 11.83/2.00  
% 11.83/2.00  fof(f66,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f5,axiom,(
% 11.83/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 11.83/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f26,plain,(
% 11.83/2.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.83/2.00    inference(ennf_transformation,[],[f5])).
% 11.83/2.00  
% 11.83/2.00  fof(f27,plain,(
% 11.83/2.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.83/2.00    inference(flattening,[],[f26])).
% 11.83/2.00  
% 11.83/2.00  fof(f62,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f27])).
% 11.83/2.00  
% 11.83/2.00  fof(f95,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.83/2.00    inference(definition_unfolding,[],[f62,f78])).
% 11.83/2.00  
% 11.83/2.00  fof(f61,plain,(
% 11.83/2.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.83/2.00    inference(cnf_transformation,[],[f4])).
% 11.83/2.00  
% 11.83/2.00  fof(f93,plain,(
% 11.83/2.00    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 11.83/2.00    inference(definition_unfolding,[],[f61,f78])).
% 11.83/2.00  
% 11.83/2.00  fof(f69,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f34])).
% 11.83/2.00  
% 11.83/2.00  cnf(c_28,negated_conjecture,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.83/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1044,plain,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_21,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_funct_1(X3)
% 11.83/2.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1050,plain,
% 11.83/2.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.83/2.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.83/2.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | v1_funct_1(X4) != iProver_top
% 11.83/2.00      | v1_funct_1(X5) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7928,plain,
% 11.83/2.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | v1_funct_1(X2) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1044,c_1050]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_31,negated_conjecture,
% 11.83/2.00      ( v1_funct_1(sK2) ),
% 11.83/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_40,plain,
% 11.83/2.00      ( v1_funct_1(sK2) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9605,plain,
% 11.83/2.00      ( v1_funct_1(X2) != iProver_top
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2) ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_7928,c_40]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9606,plain,
% 11.83/2.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_9605]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9616,plain,
% 11.83/2.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1044,c_9606]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1557,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_funct_1(sK2)
% 11.83/2.00      | k1_partfun1(X3,X4,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_21]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1946,plain,
% 11.83/2.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.83/2.00      | ~ v1_funct_1(sK2)
% 11.83/2.00      | k1_partfun1(X2,X3,X0,X1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1557]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1948,plain,
% 11.83/2.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | ~ v1_funct_1(sK2)
% 11.83/2.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1946]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9683,plain,
% 11.83/2.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_9616,c_31,c_28,c_1948]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.83/2.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_funct_1(X3) ),
% 11.83/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1053,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.83/2.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.83/2.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 11.83/2.00      | v1_funct_1(X3) != iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9686,plain,
% 11.83/2.00      ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 11.83/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_9683,c_1053]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_43,plain,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_20682,plain,
% 11.83/2.00      ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_9686,c_40,c_43]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_27,negated_conjecture,
% 11.83/2.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1045,plain,
% 11.83/2.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_32,negated_conjecture,
% 11.83/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.83/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1040,plain,
% 11.83/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_10,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1060,plain,
% 11.83/2.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4144,plain,
% 11.83/2.00      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1040,c_1060]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_25,plain,
% 11.83/2.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.83/2.00      | ~ v1_funct_2(X3,X1,X0)
% 11.83/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.83/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.83/2.00      | ~ v1_funct_1(X2)
% 11.83/2.00      | ~ v1_funct_1(X3)
% 11.83/2.00      | ~ v2_funct_1(X2)
% 11.83/2.00      | k2_relset_1(X0,X1,X2) != X1
% 11.83/2.00      | k2_funct_1(X2) = X3
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = X1 ),
% 11.83/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_24,plain,
% 11.83/2.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.83/2.00      | ~ v1_funct_2(X3,X1,X0)
% 11.83/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.83/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.83/2.00      | ~ v1_funct_1(X2)
% 11.83/2.00      | ~ v1_funct_1(X3)
% 11.83/2.00      | v2_funct_1(X2) ),
% 11.83/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_288,plain,
% 11.83/2.00      ( ~ v1_funct_1(X3)
% 11.83/2.00      | ~ v1_funct_1(X2)
% 11.83/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.83/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.83/2.00      | ~ v1_funct_2(X3,X1,X0)
% 11.83/2.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.83/2.00      | k2_relset_1(X0,X1,X2) != X1
% 11.83/2.00      | k2_funct_1(X2) = X3
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = X1 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_25,c_24]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_289,plain,
% 11.83/2.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.83/2.00      | ~ v1_funct_2(X3,X1,X0)
% 11.83/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.83/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.83/2.00      | ~ v1_funct_1(X2)
% 11.83/2.00      | ~ v1_funct_1(X3)
% 11.83/2.00      | k2_relset_1(X0,X1,X2) != X1
% 11.83/2.00      | k2_funct_1(X2) = X3
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = X1 ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_288]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1036,plain,
% 11.83/2.00      ( k2_relset_1(X0,X1,X2) != X1
% 11.83/2.00      | k2_funct_1(X2) = X3
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = X1
% 11.83/2.00      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 11.83/2.00      | v1_funct_2(X3,X1,X0) != iProver_top
% 11.83/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 11.83/2.00      | v1_funct_1(X2) != iProver_top
% 11.83/2.00      | v1_funct_1(X3) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4670,plain,
% 11.83/2.00      ( k2_funct_1(sK1) = X0
% 11.83/2.00      | k2_relat_1(sK1) != sK0
% 11.83/2.00      | sK0 = k1_xboole_0
% 11.83/2.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 11.83/2.00      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 11.83/2.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 11.83/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top
% 11.83/2.00      | v1_funct_1(sK1) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_4144,c_1036]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_35,negated_conjecture,
% 11.83/2.00      ( v1_funct_1(sK1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_36,plain,
% 11.83/2.00      ( v1_funct_1(sK1) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_34,negated_conjecture,
% 11.83/2.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_37,plain,
% 11.83/2.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_33,negated_conjecture,
% 11.83/2.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_39,plain,
% 11.83/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_8,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1391,plain,
% 11.83/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | v1_relat_1(sK1) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9,plain,
% 11.83/2.00      ( v5_relat_1(X0,X1)
% 11.83/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.83/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1412,plain,
% 11.83/2.00      ( v5_relat_1(sK1,sK0)
% 11.83/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_13,plain,
% 11.83/2.00      ( ~ v3_funct_2(X0,X1,X2)
% 11.83/2.00      | v2_funct_2(X0,X2)
% 11.83/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | ~ v1_funct_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1488,plain,
% 11.83/2.00      ( ~ v3_funct_2(sK1,X0,X1)
% 11.83/2.00      | v2_funct_2(sK1,X1)
% 11.83/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ v1_funct_1(sK1) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1490,plain,
% 11.83/2.00      ( ~ v3_funct_2(sK1,sK0,sK0)
% 11.83/2.00      | v2_funct_2(sK1,sK0)
% 11.83/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | ~ v1_funct_1(sK1) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1488]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_17,plain,
% 11.83/2.00      ( ~ v2_funct_2(X0,X1)
% 11.83/2.00      | ~ v5_relat_1(X0,X1)
% 11.83/2.00      | ~ v1_relat_1(X0)
% 11.83/2.00      | k2_relat_1(X0) = X1 ),
% 11.83/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1728,plain,
% 11.83/2.00      ( ~ v2_funct_2(sK1,sK0)
% 11.83/2.00      | ~ v5_relat_1(sK1,sK0)
% 11.83/2.00      | ~ v1_relat_1(sK1)
% 11.83/2.00      | k2_relat_1(sK1) = sK0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4746,plain,
% 11.83/2.00      ( v1_funct_1(X0) != iProver_top
% 11.83/2.00      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 11.83/2.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 11.83/2.00      | sK0 = k1_xboole_0
% 11.83/2.00      | k2_funct_1(sK1) = X0
% 11.83/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_4670,c_35,c_36,c_37,c_33,c_32,c_39,c_1391,c_1412,
% 11.83/2.00                 c_1490,c_1728]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4747,plain,
% 11.83/2.00      ( k2_funct_1(sK1) = X0
% 11.83/2.00      | sK0 = k1_xboole_0
% 11.83/2.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) != iProver_top
% 11.83/2.00      | v1_funct_2(X0,sK0,sK0) != iProver_top
% 11.83/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_4746]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4758,plain,
% 11.83/2.00      ( k2_funct_1(sK1) = sK2
% 11.83/2.00      | sK0 = k1_xboole_0
% 11.83/2.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.83/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1045,c_4747]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30,negated_conjecture,
% 11.83/2.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4759,plain,
% 11.83/2.00      ( ~ v1_funct_2(sK2,sK0,sK0)
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | ~ v1_funct_1(sK2)
% 11.83/2.00      | k2_funct_1(sK1) = sK2
% 11.83/2.00      | sK0 = k1_xboole_0 ),
% 11.83/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_4758]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4868,plain,
% 11.83/2.00      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_4758,c_40,c_41,c_43]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4869,plain,
% 11.83/2.00      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_4868]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_22,plain,
% 11.83/2.00      ( ~ v1_funct_2(X0,X1,X1)
% 11.83/2.00      | ~ v3_funct_2(X0,X1,X1)
% 11.83/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1049,plain,
% 11.83/2.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 11.83/2.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 11.83/2.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 11.83/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 11.83/2.00      | v1_funct_1(X1) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7720,plain,
% 11.83/2.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 11.83/2.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 11.83/2.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 11.83/2.00      | v1_funct_1(sK1) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1040,c_1049]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1532,plain,
% 11.83/2.00      ( ~ v1_funct_2(sK1,X0,X0)
% 11.83/2.00      | ~ v3_funct_2(sK1,X0,X0)
% 11.83/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.83/2.00      | ~ v1_funct_1(sK1)
% 11.83/2.00      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_22]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1534,plain,
% 11.83/2.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 11.83/2.00      | ~ v3_funct_2(sK1,sK0,sK0)
% 11.83/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | ~ v1_funct_1(sK1)
% 11.83/2.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1532]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9201,plain,
% 11.83/2.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_7720,c_35,c_34,c_33,c_32,c_1534]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26,negated_conjecture,
% 11.83/2.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1046,plain,
% 11.83/2.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9204,plain,
% 11.83/2.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_9201,c_1046]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9602,plain,
% 11.83/2.00      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_4869,c_9204]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_11,plain,
% 11.83/2.00      ( r2_relset_1(X0,X1,X2,X2)
% 11.83/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 11.83/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1447,plain,
% 11.83/2.00      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1448,plain,
% 11.83/2.00      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 11.83/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_1447]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14185,plain,
% 11.83/2.00      ( sK0 = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_9602,c_43,c_1448]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1057,plain,
% 11.83/2.00      ( v3_funct_2(X0,X1,X2) != iProver_top
% 11.83/2.00      | v2_funct_2(X0,X2) = iProver_top
% 11.83/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5909,plain,
% 11.83/2.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.83/2.00      | v2_funct_2(sK2,sK0) = iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1044,c_1057]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_29,negated_conjecture,
% 11.83/2.00      ( v3_funct_2(sK2,sK0,sK0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_42,plain,
% 11.83/2.00      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1483,plain,
% 11.83/2.00      ( ~ v3_funct_2(sK2,X0,X1)
% 11.83/2.00      | v2_funct_2(sK2,X1)
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ v1_funct_1(sK2) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1484,plain,
% 11.83/2.00      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 11.83/2.00      | v2_funct_2(sK2,X1) = iProver_top
% 11.83/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1486,plain,
% 11.83/2.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.83/2.00      | v2_funct_2(sK2,sK0) = iProver_top
% 11.83/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1484]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6097,plain,
% 11.83/2.00      ( v2_funct_2(sK2,sK0) = iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_5909,c_40,c_42,c_43,c_1486]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1054,plain,
% 11.83/2.00      ( k2_relat_1(X0) = X1
% 11.83/2.00      | v2_funct_2(X0,X1) != iProver_top
% 11.83/2.00      | v5_relat_1(X0,X1) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6102,plain,
% 11.83/2.00      ( k2_relat_1(sK2) = sK0
% 11.83/2.00      | v5_relat_1(sK2,sK0) != iProver_top
% 11.83/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_6097,c_1054]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1388,plain,
% 11.83/2.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | v1_relat_1(sK2) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1409,plain,
% 11.83/2.00      ( v5_relat_1(sK2,sK0)
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1485,plain,
% 11.83/2.00      ( ~ v3_funct_2(sK2,sK0,sK0)
% 11.83/2.00      | v2_funct_2(sK2,sK0)
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | ~ v1_funct_1(sK2) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1483]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1722,plain,
% 11.83/2.00      ( ~ v2_funct_2(sK2,sK0)
% 11.83/2.00      | ~ v5_relat_1(sK2,sK0)
% 11.83/2.00      | ~ v1_relat_1(sK2)
% 11.83/2.00      | k2_relat_1(sK2) = sK0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14956,plain,
% 11.83/2.00      ( k2_relat_1(sK2) = sK0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_6102,c_31,c_29,c_28,c_1388,c_1409,c_1485,c_1722]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14958,plain,
% 11.83/2.00      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_14956,c_14185]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1,plain,
% 11.83/2.00      ( ~ v1_relat_1(X0)
% 11.83/2.00      | k2_relat_1(X0) != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1067,plain,
% 11.83/2.00      ( k2_relat_1(X0) != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14962,plain,
% 11.83/2.00      ( sK2 = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_14958,c_1067]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1389,plain,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_relat_1(sK2) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_16692,plain,
% 11.83/2.00      ( sK2 = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_14962,c_43,c_1389]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_20686,plain,
% 11.83/2.00      ( m1_subset_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.83/2.00      inference(light_normalisation,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_20682,c_14185,c_16692]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6,plain,
% 11.83/2.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2,plain,
% 11.83/2.00      ( ~ v1_relat_1(X0)
% 11.83/2.00      | k1_relat_1(X0) != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1066,plain,
% 11.83/2.00      ( k1_relat_1(X0) != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2761,plain,
% 11.83/2.00      ( k6_partfun1(X0) = k1_xboole_0
% 11.83/2.00      | k1_xboole_0 != X0
% 11.83/2.00      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_6,c_1066]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_0,plain,
% 11.83/2.00      ( v1_relat_1(k6_partfun1(X0)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_115,plain,
% 11.83/2.00      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3379,plain,
% 11.83/2.00      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_2761,c_115]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3380,plain,
% 11.83/2.00      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_3379]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3384,plain,
% 11.83/2.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 11.83/2.00      inference(equality_resolution,[status(thm)],[c_3380]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_20,plain,
% 11.83/2.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.83/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1051,plain,
% 11.83/2.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3387,plain,
% 11.83/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_3384,c_1051]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_12,plain,
% 11.83/2.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.83/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | X3 = X2 ),
% 11.83/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1058,plain,
% 11.83/2.00      ( X0 = X1
% 11.83/2.00      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 11.83/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.83/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5934,plain,
% 11.83/2.00      ( k1_xboole_0 = X0
% 11.83/2.00      | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) != iProver_top
% 11.83/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_3387,c_1058]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_20699,plain,
% 11.83/2.00      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 11.83/2.00      | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_20686,c_5934]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9617,plain,
% 11.83/2.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 11.83/2.00      | v1_funct_1(sK1) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1040,c_9606]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1562,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_funct_1(sK1)
% 11.83/2.00      | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_21]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1956,plain,
% 11.83/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.83/2.00      | ~ v1_funct_1(sK1)
% 11.83/2.00      | ~ v1_funct_1(sK2)
% 11.83/2.00      | k1_partfun1(X0,X1,X2,X3,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1562]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1958,plain,
% 11.83/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.83/2.00      | ~ v1_funct_1(sK1)
% 11.83/2.00      | ~ v1_funct_1(sK2)
% 11.83/2.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1956]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9719,plain,
% 11.83/2.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_9617,c_35,c_32,c_31,c_28,c_1958]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9722,plain,
% 11.83/2.00      ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_9719,c_1045]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14193,plain,
% 11.83/2.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK2),k6_partfun1(k1_xboole_0)) = iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_14185,c_9722]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14285,plain,
% 11.83/2.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK2),k1_xboole_0) = iProver_top ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_14193,c_3384]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5910,plain,
% 11.83/2.00      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 11.83/2.00      | v2_funct_2(sK1,sK0) = iProver_top
% 11.83/2.00      | v1_funct_1(sK1) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1040,c_1057]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_38,plain,
% 11.83/2.00      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1489,plain,
% 11.83/2.00      ( v3_funct_2(sK1,X0,X1) != iProver_top
% 11.83/2.00      | v2_funct_2(sK1,X1) = iProver_top
% 11.83/2.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | v1_funct_1(sK1) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1491,plain,
% 11.83/2.00      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 11.83/2.00      | v2_funct_2(sK1,sK0) = iProver_top
% 11.83/2.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_funct_1(sK1) != iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1489]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6476,plain,
% 11.83/2.00      ( v2_funct_2(sK1,sK0) = iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_5910,c_36,c_38,c_39,c_1491]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6481,plain,
% 11.83/2.00      ( k2_relat_1(sK1) = sK0
% 11.83/2.00      | v5_relat_1(sK1,sK0) != iProver_top
% 11.83/2.00      | v1_relat_1(sK1) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_6476,c_1054]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18528,plain,
% 11.83/2.00      ( k2_relat_1(sK1) = sK0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_6481,c_35,c_33,c_32,c_1391,c_1412,c_1490,c_1728]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18530,plain,
% 11.83/2.00      ( k2_relat_1(sK1) = k1_xboole_0 ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_18528,c_14185]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18534,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0 | v1_relat_1(sK1) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_18530,c_1067]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1392,plain,
% 11.83/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_relat_1(sK1) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18720,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_18534,c_39,c_1392]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_28817,plain,
% 11.83/2.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 11.83/2.00      inference(light_normalisation,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_14285,c_16692,c_18720]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_20698,plain,
% 11.83/2.00      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = X0
% 11.83/2.00      | r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),X0) != iProver_top
% 11.83/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_20686,c_1058]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_28820,plain,
% 11.83/2.00      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 11.83/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_28817,c_20698]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_28823,plain,
% 11.83/2.00      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_20699,c_3387,c_28820]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7,plain,
% 11.83/2.00      ( ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_funct_1(X1)
% 11.83/2.00      | ~ v2_funct_1(X1)
% 11.83/2.00      | ~ v1_relat_1(X1)
% 11.83/2.00      | ~ v1_relat_1(X0)
% 11.83/2.00      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 11.83/2.00      | k2_funct_1(X1) = X0
% 11.83/2.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1063,plain,
% 11.83/2.00      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 11.83/2.00      | k2_funct_1(X1) = X0
% 11.83/2.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 11.83/2.00      | v1_funct_1(X0) != iProver_top
% 11.83/2.00      | v1_funct_1(X1) != iProver_top
% 11.83/2.00      | v2_funct_1(X1) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top
% 11.83/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_28839,plain,
% 11.83/2.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 11.83/2.00      | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
% 11.83/2.00      | k6_partfun1(k2_relat_1(k1_xboole_0)) != k1_xboole_0
% 11.83/2.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.83/2.00      | v2_funct_1(k1_xboole_0) != iProver_top
% 11.83/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_28823,c_1063]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3389,plain,
% 11.83/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_3384,c_6]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5,plain,
% 11.83/2.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3390,plain,
% 11.83/2.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_3384,c_5]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_28840,plain,
% 11.83/2.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 11.83/2.00      | k1_xboole_0 != k1_xboole_0
% 11.83/2.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.83/2.00      | v2_funct_1(k1_xboole_0) != iProver_top
% 11.83/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(light_normalisation,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_28839,c_3384,c_3389,c_3390]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_28841,plain,
% 11.83/2.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 11.83/2.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.83/2.00      | v2_funct_1(k1_xboole_0) != iProver_top
% 11.83/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(equality_resolution_simp,[status(thm)],[c_28840]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1068,plain,
% 11.83/2.00      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3388,plain,
% 11.83/2.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_3384,c_1068]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14,plain,
% 11.83/2.00      ( ~ v3_funct_2(X0,X1,X2)
% 11.83/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | v2_funct_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1056,plain,
% 11.83/2.00      ( v3_funct_2(X0,X1,X2) != iProver_top
% 11.83/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top
% 11.83/2.00      | v2_funct_1(X0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5209,plain,
% 11.83/2.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top
% 11.83/2.00      | v2_funct_1(sK2) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1044,c_1056]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1453,plain,
% 11.83/2.00      ( ~ v3_funct_2(sK2,X0,X1)
% 11.83/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.83/2.00      | ~ v1_funct_1(sK2)
% 11.83/2.00      | v2_funct_1(sK2) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_14]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1454,plain,
% 11.83/2.00      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 11.83/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top
% 11.83/2.00      | v2_funct_1(sK2) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_1453]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1456,plain,
% 11.83/2.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 11.83/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top
% 11.83/2.00      | v2_funct_1(sK2) = iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1454]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6091,plain,
% 11.83/2.00      ( v2_funct_1(sK2) = iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_5209,c_40,c_42,c_43,c_1456]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_16699,plain,
% 11.83/2.00      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_16692,c_6091]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1041,plain,
% 11.83/2.00      ( v1_funct_1(sK2) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_16702,plain,
% 11.83/2.00      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_16692,c_1041]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_31444,plain,
% 11.83/2.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_28841,c_3388,c_16699,c_16702]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14197,plain,
% 11.83/2.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_14185,c_9204]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18868,plain,
% 11.83/2.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(light_normalisation,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_14197,c_16692,c_18720]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_31447,plain,
% 11.83/2.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_31444,c_18868]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1059,plain,
% 11.83/2.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3983,plain,
% 11.83/2.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_3387,c_1059]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(contradiction,plain,
% 11.83/2.00      ( $false ),
% 11.83/2.00      inference(minisat,[status(thm)],[c_31447,c_3983]) ).
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  ------                               Statistics
% 11.83/2.00  
% 11.83/2.00  ------ Selected
% 11.83/2.00  
% 11.83/2.00  total_time:                             1.37
% 11.83/2.00  
%------------------------------------------------------------------------------
