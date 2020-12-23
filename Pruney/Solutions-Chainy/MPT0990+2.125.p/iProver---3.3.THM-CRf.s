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
% DateTime   : Thu Dec  3 12:03:23 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  223 (1015 expanded)
%              Number of clauses        :  140 ( 361 expanded)
%              Number of leaves         :   20 ( 211 expanded)
%              Depth                    :   24
%              Number of atoms          :  670 (6321 expanded)
%              Number of equality atoms :  261 (2314 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f21])).

fof(f23,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f55,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f59,f58])).

fof(f91,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f74,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f88,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f52,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f100,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f68,f85])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f97,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_762,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1279,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_781,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1264,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_1542,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1264])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1401,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_1495,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1496,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_780,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1533,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_1534,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_1634,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1542,c_39,c_1496,c_1534])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_760,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1281,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_1543,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_1264])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_51))
    | ~ v1_relat_1(X0_51)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_1412,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_1424,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_1425,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1424])).

cnf(c_1667,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1543,c_37,c_1412,c_1425])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_483,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_484,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_486,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_35])).

cnf(c_753,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_486])).

cnf(c_1288,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_1631,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1288,c_34,c_753,c_1411,c_1424])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_767,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),k2_relat_1(X0_51))))
    | ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1278,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),k2_relat_1(X0_51)))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_2400,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_1278])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_772,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1273,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_2013,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1281,c_1273])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_763,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2015,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2013,c_763])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_469,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_470,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_472,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_35])).

cnf(c_754,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_472])).

cnf(c_1287,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_1608,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1287,c_34,c_754,c_1411,c_1424])).

cnf(c_2018,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2015,c_1608])).

cnf(c_2403,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2400,c_2018])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_774,plain,
    ( ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_funct_1(X0_51))
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_839,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_841,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_773,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | v1_relat_1(k2_funct_1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_842,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(k2_funct_1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_844,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_5876,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2403,c_36,c_37,c_841,c_844,c_1412,c_1425])).

cnf(c_5885,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5876,c_1264])).

cnf(c_6140,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5885,c_36,c_37,c_844,c_1412,c_1425])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_777,plain,
    ( ~ v1_relat_1(X0_51)
    | ~ v1_relat_1(X1_51)
    | ~ v1_relat_1(X2_51)
    | k5_relat_1(k5_relat_1(X0_51,X1_51),X2_51) = k5_relat_1(X0_51,k5_relat_1(X1_51,X2_51)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1268,plain,
    ( k5_relat_1(k5_relat_1(X0_51,X1_51),X2_51) = k5_relat_1(X0_51,k5_relat_1(X1_51,X2_51))
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_6149,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_51,X1_51)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_51),X1_51)
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6140,c_1268])).

cnf(c_11513,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_51) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_51))
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_6149])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_455,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_456,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_458,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_35])).

cnf(c_755,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_1286,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_1734,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1286,c_34,c_755,c_1411,c_1424])).

cnf(c_2017,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2015,c_1734])).

cnf(c_11522,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_51)) = k5_relat_1(k6_partfun1(sK1),X0_51)
    | v1_relat_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11513,c_2017])).

cnf(c_11604,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1634,c_11522])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51) = k5_relat_1(X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1277,plain,
    ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X0_51,X1_51) = k5_relat_1(X0_51,X1_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_2641,plain,
    ( k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1277])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2830,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2641,c_38])).

cnf(c_2831,plain,
    ( k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2830])).

cnf(c_2837,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_2831])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_382,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_22,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_50,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_384,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_50])).

cnf(c_757,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_384])).

cnf(c_1284,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
    | m1_subset_1(k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1342,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1785,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1284,c_35,c_34,c_33,c_32,c_757,c_1342])).

cnf(c_2841,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2837,c_1785])).

cnf(c_3620,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2841,c_36])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_360,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_2])).

cnf(c_758,plain,
    ( r1_tarski(k1_relat_1(X0_51),X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_1283,plain,
    ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_823,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_865,plain,
    ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_1402,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1401])).

cnf(c_3994,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1283,c_823,c_865,c_1402])).

cnf(c_3995,plain,
    ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3994])).

cnf(c_4000,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_3995])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_776,plain,
    ( ~ r1_tarski(k1_relat_1(X0_51),X0_52)
    | ~ v1_relat_1(X0_51)
    | k5_relat_1(k6_partfun1(X0_52),X0_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1269,plain,
    ( k5_relat_1(k6_partfun1(X0_52),X0_51) = X0_51
    | r1_tarski(k1_relat_1(X0_51),X0_52) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_4515,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4000,c_1269])).

cnf(c_2001,plain,
    ( r1_tarski(k1_relat_1(sK3),X0_52)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_3678,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_1727,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0_52)
    | ~ v1_relat_1(sK3)
    | k5_relat_1(k6_partfun1(X0_52),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_4398,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_4733,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4515,c_32,c_1495,c_1533,c_3678,c_4398])).

cnf(c_4001,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_3995])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_775,plain,
    ( ~ r1_tarski(k2_relat_1(X0_51),X0_52)
    | ~ v1_relat_1(X0_51)
    | k5_relat_1(X0_51,k6_partfun1(X0_52)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1270,plain,
    ( k5_relat_1(X0_51,k6_partfun1(X0_52)) = X0_51
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_2390,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_1270])).

cnf(c_4846,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2390,c_36,c_37,c_844,c_1412,c_1425])).

cnf(c_4847,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4846])).

cnf(c_4852,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_4001,c_4847])).

cnf(c_11611,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_11604,c_3620,c_4733,c_4852])).

cnf(c_26,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_766,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11611,c_766])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.93/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.01  
% 3.93/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/1.01  
% 3.93/1.01  ------  iProver source info
% 3.93/1.01  
% 3.93/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.93/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/1.01  git: non_committed_changes: false
% 3.93/1.01  git: last_make_outside_of_git: false
% 3.93/1.01  
% 3.93/1.01  ------ 
% 3.93/1.01  
% 3.93/1.01  ------ Input Options
% 3.93/1.01  
% 3.93/1.01  --out_options                           all
% 3.93/1.01  --tptp_safe_out                         true
% 3.93/1.01  --problem_path                          ""
% 3.93/1.01  --include_path                          ""
% 3.93/1.01  --clausifier                            res/vclausify_rel
% 3.93/1.01  --clausifier_options                    ""
% 3.93/1.01  --stdin                                 false
% 3.93/1.01  --stats_out                             all
% 3.93/1.01  
% 3.93/1.01  ------ General Options
% 3.93/1.01  
% 3.93/1.01  --fof                                   false
% 3.93/1.01  --time_out_real                         305.
% 3.93/1.01  --time_out_virtual                      -1.
% 3.93/1.01  --symbol_type_check                     false
% 3.93/1.01  --clausify_out                          false
% 3.93/1.01  --sig_cnt_out                           false
% 3.93/1.01  --trig_cnt_out                          false
% 3.93/1.01  --trig_cnt_out_tolerance                1.
% 3.93/1.01  --trig_cnt_out_sk_spl                   false
% 3.93/1.01  --abstr_cl_out                          false
% 3.93/1.01  
% 3.93/1.01  ------ Global Options
% 3.93/1.01  
% 3.93/1.01  --schedule                              default
% 3.93/1.01  --add_important_lit                     false
% 3.93/1.01  --prop_solver_per_cl                    1000
% 3.93/1.01  --min_unsat_core                        false
% 3.93/1.01  --soft_assumptions                      false
% 3.93/1.01  --soft_lemma_size                       3
% 3.93/1.01  --prop_impl_unit_size                   0
% 3.93/1.01  --prop_impl_unit                        []
% 3.93/1.01  --share_sel_clauses                     true
% 3.93/1.01  --reset_solvers                         false
% 3.93/1.01  --bc_imp_inh                            [conj_cone]
% 3.93/1.01  --conj_cone_tolerance                   3.
% 3.93/1.01  --extra_neg_conj                        none
% 3.93/1.01  --large_theory_mode                     true
% 3.93/1.01  --prolific_symb_bound                   200
% 3.93/1.01  --lt_threshold                          2000
% 3.93/1.01  --clause_weak_htbl                      true
% 3.93/1.01  --gc_record_bc_elim                     false
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing Options
% 3.93/1.01  
% 3.93/1.01  --preprocessing_flag                    true
% 3.93/1.01  --time_out_prep_mult                    0.1
% 3.93/1.01  --splitting_mode                        input
% 3.93/1.01  --splitting_grd                         true
% 3.93/1.01  --splitting_cvd                         false
% 3.93/1.01  --splitting_cvd_svl                     false
% 3.93/1.01  --splitting_nvd                         32
% 3.93/1.01  --sub_typing                            true
% 3.93/1.01  --prep_gs_sim                           true
% 3.93/1.01  --prep_unflatten                        true
% 3.93/1.01  --prep_res_sim                          true
% 3.93/1.01  --prep_upred                            true
% 3.93/1.01  --prep_sem_filter                       exhaustive
% 3.93/1.01  --prep_sem_filter_out                   false
% 3.93/1.01  --pred_elim                             true
% 3.93/1.01  --res_sim_input                         true
% 3.93/1.01  --eq_ax_congr_red                       true
% 3.93/1.01  --pure_diseq_elim                       true
% 3.93/1.01  --brand_transform                       false
% 3.93/1.01  --non_eq_to_eq                          false
% 3.93/1.01  --prep_def_merge                        true
% 3.93/1.01  --prep_def_merge_prop_impl              false
% 3.93/1.01  --prep_def_merge_mbd                    true
% 3.93/1.01  --prep_def_merge_tr_red                 false
% 3.93/1.01  --prep_def_merge_tr_cl                  false
% 3.93/1.01  --smt_preprocessing                     true
% 3.93/1.01  --smt_ac_axioms                         fast
% 3.93/1.01  --preprocessed_out                      false
% 3.93/1.01  --preprocessed_stats                    false
% 3.93/1.01  
% 3.93/1.01  ------ Abstraction refinement Options
% 3.93/1.01  
% 3.93/1.01  --abstr_ref                             []
% 3.93/1.01  --abstr_ref_prep                        false
% 3.93/1.01  --abstr_ref_until_sat                   false
% 3.93/1.01  --abstr_ref_sig_restrict                funpre
% 3.93/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/1.01  --abstr_ref_under                       []
% 3.93/1.01  
% 3.93/1.01  ------ SAT Options
% 3.93/1.01  
% 3.93/1.01  --sat_mode                              false
% 3.93/1.01  --sat_fm_restart_options                ""
% 3.93/1.01  --sat_gr_def                            false
% 3.93/1.01  --sat_epr_types                         true
% 3.93/1.01  --sat_non_cyclic_types                  false
% 3.93/1.01  --sat_finite_models                     false
% 3.93/1.01  --sat_fm_lemmas                         false
% 3.93/1.01  --sat_fm_prep                           false
% 3.93/1.01  --sat_fm_uc_incr                        true
% 3.93/1.01  --sat_out_model                         small
% 3.93/1.01  --sat_out_clauses                       false
% 3.93/1.01  
% 3.93/1.01  ------ QBF Options
% 3.93/1.01  
% 3.93/1.01  --qbf_mode                              false
% 3.93/1.01  --qbf_elim_univ                         false
% 3.93/1.01  --qbf_dom_inst                          none
% 3.93/1.01  --qbf_dom_pre_inst                      false
% 3.93/1.01  --qbf_sk_in                             false
% 3.93/1.01  --qbf_pred_elim                         true
% 3.93/1.01  --qbf_split                             512
% 3.93/1.01  
% 3.93/1.01  ------ BMC1 Options
% 3.93/1.01  
% 3.93/1.01  --bmc1_incremental                      false
% 3.93/1.01  --bmc1_axioms                           reachable_all
% 3.93/1.01  --bmc1_min_bound                        0
% 3.93/1.01  --bmc1_max_bound                        -1
% 3.93/1.01  --bmc1_max_bound_default                -1
% 3.93/1.01  --bmc1_symbol_reachability              true
% 3.93/1.01  --bmc1_property_lemmas                  false
% 3.93/1.01  --bmc1_k_induction                      false
% 3.93/1.01  --bmc1_non_equiv_states                 false
% 3.93/1.01  --bmc1_deadlock                         false
% 3.93/1.01  --bmc1_ucm                              false
% 3.93/1.01  --bmc1_add_unsat_core                   none
% 3.93/1.01  --bmc1_unsat_core_children              false
% 3.93/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/1.01  --bmc1_out_stat                         full
% 3.93/1.01  --bmc1_ground_init                      false
% 3.93/1.01  --bmc1_pre_inst_next_state              false
% 3.93/1.01  --bmc1_pre_inst_state                   false
% 3.93/1.01  --bmc1_pre_inst_reach_state             false
% 3.93/1.01  --bmc1_out_unsat_core                   false
% 3.93/1.01  --bmc1_aig_witness_out                  false
% 3.93/1.01  --bmc1_verbose                          false
% 3.93/1.01  --bmc1_dump_clauses_tptp                false
% 3.93/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.93/1.01  --bmc1_dump_file                        -
% 3.93/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.93/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.93/1.01  --bmc1_ucm_extend_mode                  1
% 3.93/1.01  --bmc1_ucm_init_mode                    2
% 3.93/1.01  --bmc1_ucm_cone_mode                    none
% 3.93/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.93/1.01  --bmc1_ucm_relax_model                  4
% 3.93/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.93/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/1.01  --bmc1_ucm_layered_model                none
% 3.93/1.01  --bmc1_ucm_max_lemma_size               10
% 3.93/1.01  
% 3.93/1.01  ------ AIG Options
% 3.93/1.01  
% 3.93/1.01  --aig_mode                              false
% 3.93/1.01  
% 3.93/1.01  ------ Instantiation Options
% 3.93/1.01  
% 3.93/1.01  --instantiation_flag                    true
% 3.93/1.01  --inst_sos_flag                         true
% 3.93/1.01  --inst_sos_phase                        true
% 3.93/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/1.01  --inst_lit_sel_side                     num_symb
% 3.93/1.01  --inst_solver_per_active                1400
% 3.93/1.01  --inst_solver_calls_frac                1.
% 3.93/1.01  --inst_passive_queue_type               priority_queues
% 3.93/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/1.01  --inst_passive_queues_freq              [25;2]
% 3.93/1.01  --inst_dismatching                      true
% 3.93/1.01  --inst_eager_unprocessed_to_passive     true
% 3.93/1.01  --inst_prop_sim_given                   true
% 3.93/1.01  --inst_prop_sim_new                     false
% 3.93/1.01  --inst_subs_new                         false
% 3.93/1.01  --inst_eq_res_simp                      false
% 3.93/1.01  --inst_subs_given                       false
% 3.93/1.01  --inst_orphan_elimination               true
% 3.93/1.01  --inst_learning_loop_flag               true
% 3.93/1.01  --inst_learning_start                   3000
% 3.93/1.01  --inst_learning_factor                  2
% 3.93/1.01  --inst_start_prop_sim_after_learn       3
% 3.93/1.01  --inst_sel_renew                        solver
% 3.93/1.01  --inst_lit_activity_flag                true
% 3.93/1.01  --inst_restr_to_given                   false
% 3.93/1.01  --inst_activity_threshold               500
% 3.93/1.01  --inst_out_proof                        true
% 3.93/1.01  
% 3.93/1.01  ------ Resolution Options
% 3.93/1.01  
% 3.93/1.01  --resolution_flag                       true
% 3.93/1.01  --res_lit_sel                           adaptive
% 3.93/1.01  --res_lit_sel_side                      none
% 3.93/1.01  --res_ordering                          kbo
% 3.93/1.01  --res_to_prop_solver                    active
% 3.93/1.01  --res_prop_simpl_new                    false
% 3.93/1.01  --res_prop_simpl_given                  true
% 3.93/1.01  --res_passive_queue_type                priority_queues
% 3.93/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/1.01  --res_passive_queues_freq               [15;5]
% 3.93/1.01  --res_forward_subs                      full
% 3.93/1.01  --res_backward_subs                     full
% 3.93/1.01  --res_forward_subs_resolution           true
% 3.93/1.01  --res_backward_subs_resolution          true
% 3.93/1.01  --res_orphan_elimination                true
% 3.93/1.01  --res_time_limit                        2.
% 3.93/1.01  --res_out_proof                         true
% 3.93/1.01  
% 3.93/1.01  ------ Superposition Options
% 3.93/1.01  
% 3.93/1.01  --superposition_flag                    true
% 3.93/1.01  --sup_passive_queue_type                priority_queues
% 3.93/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.93/1.01  --demod_completeness_check              fast
% 3.93/1.01  --demod_use_ground                      true
% 3.93/1.01  --sup_to_prop_solver                    passive
% 3.93/1.01  --sup_prop_simpl_new                    true
% 3.93/1.01  --sup_prop_simpl_given                  true
% 3.93/1.01  --sup_fun_splitting                     true
% 3.93/1.01  --sup_smt_interval                      50000
% 3.93/1.01  
% 3.93/1.01  ------ Superposition Simplification Setup
% 3.93/1.01  
% 3.93/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/1.01  --sup_immed_triv                        [TrivRules]
% 3.93/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.01  --sup_immed_bw_main                     []
% 3.93/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.01  --sup_input_bw                          []
% 3.93/1.01  
% 3.93/1.01  ------ Combination Options
% 3.93/1.01  
% 3.93/1.01  --comb_res_mult                         3
% 3.93/1.01  --comb_sup_mult                         2
% 3.93/1.01  --comb_inst_mult                        10
% 3.93/1.01  
% 3.93/1.01  ------ Debug Options
% 3.93/1.01  
% 3.93/1.01  --dbg_backtrace                         false
% 3.93/1.01  --dbg_dump_prop_clauses                 false
% 3.93/1.01  --dbg_dump_prop_clauses_file            -
% 3.93/1.01  --dbg_out_stat                          false
% 3.93/1.01  ------ Parsing...
% 3.93/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/1.01  ------ Proving...
% 3.93/1.01  ------ Problem Properties 
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  clauses                                 30
% 3.93/1.01  conjectures                             8
% 3.93/1.01  EPR                                     4
% 3.93/1.01  Horn                                    30
% 3.93/1.01  unary                                   10
% 3.93/1.01  binary                                  9
% 3.93/1.01  lits                                    68
% 3.93/1.01  lits eq                                 17
% 3.93/1.01  fd_pure                                 0
% 3.93/1.01  fd_pseudo                               0
% 3.93/1.01  fd_cond                                 0
% 3.93/1.01  fd_pseudo_cond                          0
% 3.93/1.01  AC symbols                              0
% 3.93/1.01  
% 3.93/1.01  ------ Schedule dynamic 5 is on 
% 3.93/1.01  
% 3.93/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  ------ 
% 3.93/1.01  Current options:
% 3.93/1.01  ------ 
% 3.93/1.01  
% 3.93/1.01  ------ Input Options
% 3.93/1.01  
% 3.93/1.01  --out_options                           all
% 3.93/1.01  --tptp_safe_out                         true
% 3.93/1.01  --problem_path                          ""
% 3.93/1.01  --include_path                          ""
% 3.93/1.01  --clausifier                            res/vclausify_rel
% 3.93/1.01  --clausifier_options                    ""
% 3.93/1.01  --stdin                                 false
% 3.93/1.01  --stats_out                             all
% 3.93/1.01  
% 3.93/1.01  ------ General Options
% 3.93/1.01  
% 3.93/1.01  --fof                                   false
% 3.93/1.01  --time_out_real                         305.
% 3.93/1.01  --time_out_virtual                      -1.
% 3.93/1.01  --symbol_type_check                     false
% 3.93/1.01  --clausify_out                          false
% 3.93/1.01  --sig_cnt_out                           false
% 3.93/1.01  --trig_cnt_out                          false
% 3.93/1.01  --trig_cnt_out_tolerance                1.
% 3.93/1.01  --trig_cnt_out_sk_spl                   false
% 3.93/1.01  --abstr_cl_out                          false
% 3.93/1.01  
% 3.93/1.01  ------ Global Options
% 3.93/1.01  
% 3.93/1.01  --schedule                              default
% 3.93/1.01  --add_important_lit                     false
% 3.93/1.01  --prop_solver_per_cl                    1000
% 3.93/1.01  --min_unsat_core                        false
% 3.93/1.01  --soft_assumptions                      false
% 3.93/1.01  --soft_lemma_size                       3
% 3.93/1.01  --prop_impl_unit_size                   0
% 3.93/1.01  --prop_impl_unit                        []
% 3.93/1.01  --share_sel_clauses                     true
% 3.93/1.01  --reset_solvers                         false
% 3.93/1.01  --bc_imp_inh                            [conj_cone]
% 3.93/1.01  --conj_cone_tolerance                   3.
% 3.93/1.01  --extra_neg_conj                        none
% 3.93/1.01  --large_theory_mode                     true
% 3.93/1.01  --prolific_symb_bound                   200
% 3.93/1.01  --lt_threshold                          2000
% 3.93/1.01  --clause_weak_htbl                      true
% 3.93/1.01  --gc_record_bc_elim                     false
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing Options
% 3.93/1.01  
% 3.93/1.01  --preprocessing_flag                    true
% 3.93/1.01  --time_out_prep_mult                    0.1
% 3.93/1.01  --splitting_mode                        input
% 3.93/1.01  --splitting_grd                         true
% 3.93/1.01  --splitting_cvd                         false
% 3.93/1.01  --splitting_cvd_svl                     false
% 3.93/1.01  --splitting_nvd                         32
% 3.93/1.01  --sub_typing                            true
% 3.93/1.01  --prep_gs_sim                           true
% 3.93/1.01  --prep_unflatten                        true
% 3.93/1.01  --prep_res_sim                          true
% 3.93/1.01  --prep_upred                            true
% 3.93/1.01  --prep_sem_filter                       exhaustive
% 3.93/1.01  --prep_sem_filter_out                   false
% 3.93/1.01  --pred_elim                             true
% 3.93/1.01  --res_sim_input                         true
% 3.93/1.01  --eq_ax_congr_red                       true
% 3.93/1.01  --pure_diseq_elim                       true
% 3.93/1.01  --brand_transform                       false
% 3.93/1.01  --non_eq_to_eq                          false
% 3.93/1.01  --prep_def_merge                        true
% 3.93/1.01  --prep_def_merge_prop_impl              false
% 3.93/1.01  --prep_def_merge_mbd                    true
% 3.93/1.01  --prep_def_merge_tr_red                 false
% 3.93/1.01  --prep_def_merge_tr_cl                  false
% 3.93/1.01  --smt_preprocessing                     true
% 3.93/1.01  --smt_ac_axioms                         fast
% 3.93/1.01  --preprocessed_out                      false
% 3.93/1.01  --preprocessed_stats                    false
% 3.93/1.01  
% 3.93/1.01  ------ Abstraction refinement Options
% 3.93/1.01  
% 3.93/1.01  --abstr_ref                             []
% 3.93/1.01  --abstr_ref_prep                        false
% 3.93/1.01  --abstr_ref_until_sat                   false
% 3.93/1.01  --abstr_ref_sig_restrict                funpre
% 3.93/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/1.01  --abstr_ref_under                       []
% 3.93/1.01  
% 3.93/1.01  ------ SAT Options
% 3.93/1.01  
% 3.93/1.01  --sat_mode                              false
% 3.93/1.01  --sat_fm_restart_options                ""
% 3.93/1.01  --sat_gr_def                            false
% 3.93/1.01  --sat_epr_types                         true
% 3.93/1.01  --sat_non_cyclic_types                  false
% 3.93/1.01  --sat_finite_models                     false
% 3.93/1.01  --sat_fm_lemmas                         false
% 3.93/1.01  --sat_fm_prep                           false
% 3.93/1.01  --sat_fm_uc_incr                        true
% 3.93/1.01  --sat_out_model                         small
% 3.93/1.01  --sat_out_clauses                       false
% 3.93/1.01  
% 3.93/1.01  ------ QBF Options
% 3.93/1.01  
% 3.93/1.01  --qbf_mode                              false
% 3.93/1.01  --qbf_elim_univ                         false
% 3.93/1.01  --qbf_dom_inst                          none
% 3.93/1.01  --qbf_dom_pre_inst                      false
% 3.93/1.01  --qbf_sk_in                             false
% 3.93/1.01  --qbf_pred_elim                         true
% 3.93/1.01  --qbf_split                             512
% 3.93/1.01  
% 3.93/1.01  ------ BMC1 Options
% 3.93/1.01  
% 3.93/1.01  --bmc1_incremental                      false
% 3.93/1.01  --bmc1_axioms                           reachable_all
% 3.93/1.01  --bmc1_min_bound                        0
% 3.93/1.01  --bmc1_max_bound                        -1
% 3.93/1.01  --bmc1_max_bound_default                -1
% 3.93/1.01  --bmc1_symbol_reachability              true
% 3.93/1.01  --bmc1_property_lemmas                  false
% 3.93/1.01  --bmc1_k_induction                      false
% 3.93/1.01  --bmc1_non_equiv_states                 false
% 3.93/1.01  --bmc1_deadlock                         false
% 3.93/1.01  --bmc1_ucm                              false
% 3.93/1.01  --bmc1_add_unsat_core                   none
% 3.93/1.01  --bmc1_unsat_core_children              false
% 3.93/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/1.01  --bmc1_out_stat                         full
% 3.93/1.01  --bmc1_ground_init                      false
% 3.93/1.01  --bmc1_pre_inst_next_state              false
% 3.93/1.01  --bmc1_pre_inst_state                   false
% 3.93/1.01  --bmc1_pre_inst_reach_state             false
% 3.93/1.01  --bmc1_out_unsat_core                   false
% 3.93/1.01  --bmc1_aig_witness_out                  false
% 3.93/1.01  --bmc1_verbose                          false
% 3.93/1.01  --bmc1_dump_clauses_tptp                false
% 3.93/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.93/1.01  --bmc1_dump_file                        -
% 3.93/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.93/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.93/1.01  --bmc1_ucm_extend_mode                  1
% 3.93/1.01  --bmc1_ucm_init_mode                    2
% 3.93/1.01  --bmc1_ucm_cone_mode                    none
% 3.93/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.93/1.01  --bmc1_ucm_relax_model                  4
% 3.93/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.93/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/1.01  --bmc1_ucm_layered_model                none
% 3.93/1.01  --bmc1_ucm_max_lemma_size               10
% 3.93/1.01  
% 3.93/1.01  ------ AIG Options
% 3.93/1.01  
% 3.93/1.01  --aig_mode                              false
% 3.93/1.01  
% 3.93/1.01  ------ Instantiation Options
% 3.93/1.01  
% 3.93/1.01  --instantiation_flag                    true
% 3.93/1.01  --inst_sos_flag                         true
% 3.93/1.01  --inst_sos_phase                        true
% 3.93/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/1.01  --inst_lit_sel_side                     none
% 3.93/1.01  --inst_solver_per_active                1400
% 3.93/1.01  --inst_solver_calls_frac                1.
% 3.93/1.01  --inst_passive_queue_type               priority_queues
% 3.93/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/1.01  --inst_passive_queues_freq              [25;2]
% 3.93/1.01  --inst_dismatching                      true
% 3.93/1.01  --inst_eager_unprocessed_to_passive     true
% 3.93/1.01  --inst_prop_sim_given                   true
% 3.93/1.01  --inst_prop_sim_new                     false
% 3.93/1.01  --inst_subs_new                         false
% 3.93/1.01  --inst_eq_res_simp                      false
% 3.93/1.01  --inst_subs_given                       false
% 3.93/1.01  --inst_orphan_elimination               true
% 3.93/1.01  --inst_learning_loop_flag               true
% 3.93/1.01  --inst_learning_start                   3000
% 3.93/1.01  --inst_learning_factor                  2
% 3.93/1.01  --inst_start_prop_sim_after_learn       3
% 3.93/1.01  --inst_sel_renew                        solver
% 3.93/1.01  --inst_lit_activity_flag                true
% 3.93/1.01  --inst_restr_to_given                   false
% 3.93/1.01  --inst_activity_threshold               500
% 3.93/1.01  --inst_out_proof                        true
% 3.93/1.01  
% 3.93/1.01  ------ Resolution Options
% 3.93/1.01  
% 3.93/1.01  --resolution_flag                       false
% 3.93/1.01  --res_lit_sel                           adaptive
% 3.93/1.01  --res_lit_sel_side                      none
% 3.93/1.01  --res_ordering                          kbo
% 3.93/1.01  --res_to_prop_solver                    active
% 3.93/1.01  --res_prop_simpl_new                    false
% 3.93/1.01  --res_prop_simpl_given                  true
% 3.93/1.01  --res_passive_queue_type                priority_queues
% 3.93/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/1.01  --res_passive_queues_freq               [15;5]
% 3.93/1.01  --res_forward_subs                      full
% 3.93/1.01  --res_backward_subs                     full
% 3.93/1.01  --res_forward_subs_resolution           true
% 3.93/1.01  --res_backward_subs_resolution          true
% 3.93/1.01  --res_orphan_elimination                true
% 3.93/1.01  --res_time_limit                        2.
% 3.93/1.01  --res_out_proof                         true
% 3.93/1.01  
% 3.93/1.01  ------ Superposition Options
% 3.93/1.01  
% 3.93/1.01  --superposition_flag                    true
% 3.93/1.01  --sup_passive_queue_type                priority_queues
% 3.93/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.93/1.01  --demod_completeness_check              fast
% 3.93/1.01  --demod_use_ground                      true
% 3.93/1.01  --sup_to_prop_solver                    passive
% 3.93/1.01  --sup_prop_simpl_new                    true
% 3.93/1.01  --sup_prop_simpl_given                  true
% 3.93/1.01  --sup_fun_splitting                     true
% 3.93/1.01  --sup_smt_interval                      50000
% 3.93/1.01  
% 3.93/1.01  ------ Superposition Simplification Setup
% 3.93/1.01  
% 3.93/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/1.01  --sup_immed_triv                        [TrivRules]
% 3.93/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.01  --sup_immed_bw_main                     []
% 3.93/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.01  --sup_input_bw                          []
% 3.93/1.01  
% 3.93/1.01  ------ Combination Options
% 3.93/1.01  
% 3.93/1.01  --comb_res_mult                         3
% 3.93/1.01  --comb_sup_mult                         2
% 3.93/1.01  --comb_inst_mult                        10
% 3.93/1.01  
% 3.93/1.01  ------ Debug Options
% 3.93/1.01  
% 3.93/1.01  --dbg_backtrace                         false
% 3.93/1.01  --dbg_dump_prop_clauses                 false
% 3.93/1.01  --dbg_dump_prop_clauses_file            -
% 3.93/1.01  --dbg_out_stat                          false
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  ------ Proving...
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  % SZS status Theorem for theBenchmark.p
% 3.93/1.01  
% 3.93/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/1.01  
% 3.93/1.01  fof(f21,conjecture,(
% 3.93/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f22,negated_conjecture,(
% 3.93/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.93/1.01    inference(negated_conjecture,[],[f21])).
% 3.93/1.01  
% 3.93/1.01  fof(f23,plain,(
% 3.93/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.93/1.01    inference(pure_predicate_removal,[],[f22])).
% 3.93/1.01  
% 3.93/1.01  fof(f54,plain,(
% 3.93/1.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.93/1.01    inference(ennf_transformation,[],[f23])).
% 3.93/1.01  
% 3.93/1.01  fof(f55,plain,(
% 3.93/1.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.93/1.01    inference(flattening,[],[f54])).
% 3.93/1.01  
% 3.93/1.01  fof(f59,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f58,plain,(
% 3.93/1.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f60,plain,(
% 3.93/1.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.93/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f59,f58])).
% 3.93/1.01  
% 3.93/1.01  fof(f91,plain,(
% 3.93/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.93/1.01    inference(cnf_transformation,[],[f60])).
% 3.93/1.01  
% 3.93/1.01  fof(f1,axiom,(
% 3.93/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f27,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.93/1.01    inference(ennf_transformation,[],[f1])).
% 3.93/1.01  
% 3.93/1.01  fof(f61,plain,(
% 3.93/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f27])).
% 3.93/1.01  
% 3.93/1.01  fof(f3,axiom,(
% 3.93/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f64,plain,(
% 3.93/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f3])).
% 3.93/1.01  
% 3.93/1.01  fof(f89,plain,(
% 3.93/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.93/1.01    inference(cnf_transformation,[],[f60])).
% 3.93/1.01  
% 3.93/1.01  fof(f11,axiom,(
% 3.93/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f40,plain,(
% 3.93/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f11])).
% 3.93/1.01  
% 3.93/1.01  fof(f41,plain,(
% 3.93/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.93/1.01    inference(flattening,[],[f40])).
% 3.93/1.01  
% 3.93/1.01  fof(f74,plain,(
% 3.93/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f41])).
% 3.93/1.01  
% 3.93/1.01  fof(f94,plain,(
% 3.93/1.01    v2_funct_1(sK2)),
% 3.93/1.01    inference(cnf_transformation,[],[f60])).
% 3.93/1.01  
% 3.93/1.01  fof(f88,plain,(
% 3.93/1.01    v1_funct_1(sK2)),
% 3.93/1.01    inference(cnf_transformation,[],[f60])).
% 3.93/1.01  
% 3.93/1.01  fof(f20,axiom,(
% 3.93/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f24,plain,(
% 3.93/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 3.93/1.01    inference(pure_predicate_removal,[],[f20])).
% 3.93/1.01  
% 3.93/1.01  fof(f52,plain,(
% 3.93/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f24])).
% 3.93/1.01  
% 3.93/1.01  fof(f53,plain,(
% 3.93/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.93/1.01    inference(flattening,[],[f52])).
% 3.93/1.01  
% 3.93/1.01  fof(f87,plain,(
% 3.93/1.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f53])).
% 3.93/1.01  
% 3.93/1.01  fof(f14,axiom,(
% 3.93/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f45,plain,(
% 3.93/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.01    inference(ennf_transformation,[],[f14])).
% 3.93/1.01  
% 3.93/1.01  fof(f78,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f45])).
% 3.93/1.01  
% 3.93/1.01  fof(f92,plain,(
% 3.93/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.93/1.01    inference(cnf_transformation,[],[f60])).
% 3.93/1.01  
% 3.93/1.01  fof(f73,plain,(
% 3.93/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f41])).
% 3.93/1.01  
% 3.93/1.01  fof(f9,axiom,(
% 3.93/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f36,plain,(
% 3.93/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f9])).
% 3.93/1.01  
% 3.93/1.01  fof(f37,plain,(
% 3.93/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.93/1.01    inference(flattening,[],[f36])).
% 3.93/1.01  
% 3.93/1.01  fof(f71,plain,(
% 3.93/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f37])).
% 3.93/1.01  
% 3.93/1.01  fof(f70,plain,(
% 3.93/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f37])).
% 3.93/1.01  
% 3.93/1.01  fof(f6,axiom,(
% 3.93/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f31,plain,(
% 3.93/1.01    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.93/1.01    inference(ennf_transformation,[],[f6])).
% 3.93/1.01  
% 3.93/1.01  fof(f67,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f31])).
% 3.93/1.01  
% 3.93/1.01  fof(f12,axiom,(
% 3.93/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f42,plain,(
% 3.93/1.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f12])).
% 3.93/1.01  
% 3.93/1.01  fof(f43,plain,(
% 3.93/1.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.93/1.01    inference(flattening,[],[f42])).
% 3.93/1.01  
% 3.93/1.01  fof(f76,plain,(
% 3.93/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f43])).
% 3.93/1.01  
% 3.93/1.01  fof(f19,axiom,(
% 3.93/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f85,plain,(
% 3.93/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f19])).
% 3.93/1.01  
% 3.93/1.01  fof(f100,plain,(
% 3.93/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.01    inference(definition_unfolding,[],[f76,f85])).
% 3.93/1.01  
% 3.93/1.01  fof(f18,axiom,(
% 3.93/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f50,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.93/1.01    inference(ennf_transformation,[],[f18])).
% 3.93/1.01  
% 3.93/1.01  fof(f51,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.93/1.01    inference(flattening,[],[f50])).
% 3.93/1.01  
% 3.93/1.01  fof(f84,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f51])).
% 3.93/1.01  
% 3.93/1.01  fof(f90,plain,(
% 3.93/1.01    v1_funct_1(sK3)),
% 3.93/1.01    inference(cnf_transformation,[],[f60])).
% 3.93/1.01  
% 3.93/1.01  fof(f15,axiom,(
% 3.93/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f46,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.93/1.01    inference(ennf_transformation,[],[f15])).
% 3.93/1.01  
% 3.93/1.01  fof(f47,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.01    inference(flattening,[],[f46])).
% 3.93/1.01  
% 3.93/1.01  fof(f57,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.01    inference(nnf_transformation,[],[f47])).
% 3.93/1.01  
% 3.93/1.01  fof(f79,plain,(
% 3.93/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f57])).
% 3.93/1.01  
% 3.93/1.01  fof(f93,plain,(
% 3.93/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.93/1.01    inference(cnf_transformation,[],[f60])).
% 3.93/1.01  
% 3.93/1.01  fof(f17,axiom,(
% 3.93/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f25,plain,(
% 3.93/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.93/1.01    inference(pure_predicate_removal,[],[f17])).
% 3.93/1.01  
% 3.93/1.01  fof(f83,plain,(
% 3.93/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f25])).
% 3.93/1.01  
% 3.93/1.01  fof(f16,axiom,(
% 3.93/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f48,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.93/1.01    inference(ennf_transformation,[],[f16])).
% 3.93/1.01  
% 3.93/1.01  fof(f49,plain,(
% 3.93/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.93/1.01    inference(flattening,[],[f48])).
% 3.93/1.01  
% 3.93/1.01  fof(f82,plain,(
% 3.93/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f49])).
% 3.93/1.01  
% 3.93/1.01  fof(f13,axiom,(
% 3.93/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f26,plain,(
% 3.93/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.93/1.01    inference(pure_predicate_removal,[],[f13])).
% 3.93/1.01  
% 3.93/1.01  fof(f44,plain,(
% 3.93/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.01    inference(ennf_transformation,[],[f26])).
% 3.93/1.01  
% 3.93/1.01  fof(f77,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f44])).
% 3.93/1.01  
% 3.93/1.01  fof(f2,axiom,(
% 3.93/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f28,plain,(
% 3.93/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.93/1.01    inference(ennf_transformation,[],[f2])).
% 3.93/1.01  
% 3.93/1.01  fof(f56,plain,(
% 3.93/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.93/1.01    inference(nnf_transformation,[],[f28])).
% 3.93/1.01  
% 3.93/1.01  fof(f62,plain,(
% 3.93/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f56])).
% 3.93/1.01  
% 3.93/1.01  fof(f7,axiom,(
% 3.93/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f32,plain,(
% 3.93/1.01    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.93/1.01    inference(ennf_transformation,[],[f7])).
% 3.93/1.01  
% 3.93/1.01  fof(f33,plain,(
% 3.93/1.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.93/1.01    inference(flattening,[],[f32])).
% 3.93/1.01  
% 3.93/1.01  fof(f68,plain,(
% 3.93/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f33])).
% 3.93/1.01  
% 3.93/1.01  fof(f98,plain,(
% 3.93/1.01    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.93/1.01    inference(definition_unfolding,[],[f68,f85])).
% 3.93/1.01  
% 3.93/1.01  fof(f8,axiom,(
% 3.93/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f34,plain,(
% 3.93/1.01    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.93/1.01    inference(ennf_transformation,[],[f8])).
% 3.93/1.01  
% 3.93/1.01  fof(f35,plain,(
% 3.93/1.01    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.93/1.01    inference(flattening,[],[f34])).
% 3.93/1.01  
% 3.93/1.01  fof(f69,plain,(
% 3.93/1.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f35])).
% 3.93/1.01  
% 3.93/1.01  fof(f99,plain,(
% 3.93/1.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.93/1.01    inference(definition_unfolding,[],[f69,f85])).
% 3.93/1.01  
% 3.93/1.01  fof(f97,plain,(
% 3.93/1.01    k2_funct_1(sK2) != sK3),
% 3.93/1.01    inference(cnf_transformation,[],[f60])).
% 3.93/1.01  
% 3.93/1.01  cnf(c_32,negated_conjecture,
% 3.93/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.93/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_762,negated_conjecture,
% 3.93/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_32]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1279,plain,
% 3.93/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_0,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.93/1.01      | ~ v1_relat_1(X1)
% 3.93/1.01      | v1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_781,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 3.93/1.01      | ~ v1_relat_1(X1_51)
% 3.93/1.01      | v1_relat_1(X0_51) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1264,plain,
% 3.93/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 3.93/1.01      | v1_relat_1(X1_51) != iProver_top
% 3.93/1.01      | v1_relat_1(X0_51) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1542,plain,
% 3.93/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.93/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_1279,c_1264]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_39,plain,
% 3.93/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1401,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.93/1.01      | v1_relat_1(X0_51)
% 3.93/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_781]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1495,plain,
% 3.93/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.93/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.93/1.01      | v1_relat_1(sK3) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1496,plain,
% 3.93/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.93/1.01      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.93/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_1495]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_3,plain,
% 3.93/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.93/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_780,plain,
% 3.93/1.01      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1533,plain,
% 3.93/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_780]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1534,plain,
% 3.93/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_1533]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1634,plain,
% 3.93/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_1542,c_39,c_1496,c_1534]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_34,negated_conjecture,
% 3.93/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.93/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_760,negated_conjecture,
% 3.93/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_34]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1281,plain,
% 3.93/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1543,plain,
% 3.93/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.93/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_1281,c_1264]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_37,plain,
% 3.93/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1330,plain,
% 3.93/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_51))
% 3.93/1.01      | ~ v1_relat_1(X0_51)
% 3.93/1.01      | v1_relat_1(sK2) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_781]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1367,plain,
% 3.93/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.93/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52))
% 3.93/1.01      | v1_relat_1(sK2) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_1330]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1411,plain,
% 3.93/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.93/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.93/1.01      | v1_relat_1(sK2) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_1367]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1412,plain,
% 3.93/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.93/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.93/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1424,plain,
% 3.93/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_780]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1425,plain,
% 3.93/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_1424]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1667,plain,
% 3.93/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_1543,c_37,c_1412,c_1425]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12,plain,
% 3.93/1.01      ( ~ v2_funct_1(X0)
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_29,negated_conjecture,
% 3.93/1.01      ( v2_funct_1(sK2) ),
% 3.93/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_483,plain,
% 3.93/1.01      ( ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.93/1.01      | sK2 != X0 ),
% 3.93/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_484,plain,
% 3.93/1.01      ( ~ v1_funct_1(sK2)
% 3.93/1.01      | ~ v1_relat_1(sK2)
% 3.93/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.93/1.01      inference(unflattening,[status(thm)],[c_483]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_35,negated_conjecture,
% 3.93/1.01      ( v1_funct_1(sK2) ),
% 3.93/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_486,plain,
% 3.93/1.01      ( ~ v1_relat_1(sK2)
% 3.93/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_484,c_35]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_753,plain,
% 3.93/1.01      ( ~ v1_relat_1(sK2)
% 3.93/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_486]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1288,plain,
% 3.93/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.93/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1631,plain,
% 3.93/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_1288,c_34,c_753,c_1411,c_1424]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_24,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_767,plain,
% 3.93/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),k2_relat_1(X0_51))))
% 3.93/1.01      | ~ v1_funct_1(X0_51)
% 3.93/1.01      | ~ v1_relat_1(X0_51) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1278,plain,
% 3.93/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),k2_relat_1(X0_51)))) = iProver_top
% 3.93/1.01      | v1_funct_1(X0_51) != iProver_top
% 3.93/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_2400,plain,
% 3.93/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.93/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.93/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_1631,c_1278]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_17,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_772,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.93/1.01      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1273,plain,
% 3.93/1.01      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 3.93/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_2013,plain,
% 3.93/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_1281,c_1273]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_31,negated_conjecture,
% 3.93/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.93/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_763,negated_conjecture,
% 3.93/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_31]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_2015,plain,
% 3.93/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.93/1.01      inference(light_normalisation,[status(thm)],[c_2013,c_763]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_13,plain,
% 3.93/1.01      ( ~ v2_funct_1(X0)
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_469,plain,
% 3.93/1.01      ( ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.93/1.01      | sK2 != X0 ),
% 3.93/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_470,plain,
% 3.93/1.01      ( ~ v1_funct_1(sK2)
% 3.93/1.01      | ~ v1_relat_1(sK2)
% 3.93/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.93/1.01      inference(unflattening,[status(thm)],[c_469]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_472,plain,
% 3.93/1.01      ( ~ v1_relat_1(sK2)
% 3.93/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_470,c_35]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_754,plain,
% 3.93/1.01      ( ~ v1_relat_1(sK2)
% 3.93/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_472]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1287,plain,
% 3.93/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.93/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1608,plain,
% 3.93/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_1287,c_34,c_754,c_1411,c_1424]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_2018,plain,
% 3.93/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.93/1.01      inference(demodulation,[status(thm)],[c_2015,c_1608]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_2403,plain,
% 3.93/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.93/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.93/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.93/1.01      inference(light_normalisation,[status(thm)],[c_2400,c_2018]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_36,plain,
% 3.93/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_9,plain,
% 3.93/1.01      ( ~ v1_funct_1(X0)
% 3.93/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.93/1.01      | ~ v1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_774,plain,
% 3.93/1.01      ( ~ v1_funct_1(X0_51)
% 3.93/1.01      | v1_funct_1(k2_funct_1(X0_51))
% 3.93/1.01      | ~ v1_relat_1(X0_51) ),
% 3.93/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_839,plain,
% 3.93/1.01      ( v1_funct_1(X0_51) != iProver_top
% 3.93/1.01      | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
% 3.93/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_841,plain,
% 3.93/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.93/1.01      | v1_funct_1(sK2) != iProver_top
% 3.93/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_839]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_10,plain,
% 3.93/1.01      ( ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | v1_relat_1(k2_funct_1(X0)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_773,plain,
% 3.93/1.02      ( ~ v1_funct_1(X0_51)
% 3.93/1.02      | ~ v1_relat_1(X0_51)
% 3.93/1.02      | v1_relat_1(k2_funct_1(X0_51)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_842,plain,
% 3.93/1.02      ( v1_funct_1(X0_51) != iProver_top
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top
% 3.93/1.02      | v1_relat_1(k2_funct_1(X0_51)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_844,plain,
% 3.93/1.02      ( v1_funct_1(sK2) != iProver_top
% 3.93/1.02      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.93/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_842]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5876,plain,
% 3.93/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_2403,c_36,c_37,c_841,c_844,c_1412,c_1425]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_5885,plain,
% 3.93/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
% 3.93/1.02      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_5876,c_1264]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_6140,plain,
% 3.93/1.02      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_5885,c_36,c_37,c_844,c_1412,c_1425]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_6,plain,
% 3.93/1.02      ( ~ v1_relat_1(X0)
% 3.93/1.02      | ~ v1_relat_1(X1)
% 3.93/1.02      | ~ v1_relat_1(X2)
% 3.93/1.02      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_777,plain,
% 3.93/1.02      ( ~ v1_relat_1(X0_51)
% 3.93/1.02      | ~ v1_relat_1(X1_51)
% 3.93/1.02      | ~ v1_relat_1(X2_51)
% 3.93/1.02      | k5_relat_1(k5_relat_1(X0_51,X1_51),X2_51) = k5_relat_1(X0_51,k5_relat_1(X1_51,X2_51)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1268,plain,
% 3.93/1.02      ( k5_relat_1(k5_relat_1(X0_51,X1_51),X2_51) = k5_relat_1(X0_51,k5_relat_1(X1_51,X2_51))
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top
% 3.93/1.02      | v1_relat_1(X1_51) != iProver_top
% 3.93/1.02      | v1_relat_1(X2_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_6149,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_51,X1_51)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_51),X1_51)
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top
% 3.93/1.02      | v1_relat_1(X1_51) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_6140,c_1268]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_11513,plain,
% 3.93/1.02      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_51) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_51))
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1667,c_6149]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_14,plain,
% 3.93/1.02      ( ~ v2_funct_1(X0)
% 3.93/1.02      | ~ v1_funct_1(X0)
% 3.93/1.02      | ~ v1_relat_1(X0)
% 3.93/1.02      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f100]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_455,plain,
% 3.93/1.02      ( ~ v1_funct_1(X0)
% 3.93/1.02      | ~ v1_relat_1(X0)
% 3.93/1.02      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.93/1.02      | sK2 != X0 ),
% 3.93/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_456,plain,
% 3.93/1.02      ( ~ v1_funct_1(sK2)
% 3.93/1.02      | ~ v1_relat_1(sK2)
% 3.93/1.02      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.93/1.02      inference(unflattening,[status(thm)],[c_455]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_458,plain,
% 3.93/1.02      ( ~ v1_relat_1(sK2)
% 3.93/1.02      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_456,c_35]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_755,plain,
% 3.93/1.02      ( ~ v1_relat_1(sK2)
% 3.93/1.02      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_458]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1286,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.93/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1734,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_1286,c_34,c_755,c_1411,c_1424]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2017,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.93/1.02      inference(demodulation,[status(thm)],[c_2015,c_1734]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_11522,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_51)) = k5_relat_1(k6_partfun1(sK1),X0_51)
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(light_normalisation,[status(thm)],[c_11513,c_2017]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_11604,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1634,c_11522]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_23,plain,
% 3.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.93/1.02      | ~ v1_funct_1(X0)
% 3.93/1.02      | ~ v1_funct_1(X3)
% 3.93/1.02      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.93/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_768,plain,
% 3.93/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.93/1.02      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
% 3.93/1.02      | ~ v1_funct_1(X0_51)
% 3.93/1.02      | ~ v1_funct_1(X1_51)
% 3.93/1.02      | k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51) = k5_relat_1(X1_51,X0_51) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_23]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1277,plain,
% 3.93/1.02      ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X0_51,X1_51) = k5_relat_1(X0_51,X1_51)
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.93/1.02      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 3.93/1.02      | v1_funct_1(X1_51) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2641,plain,
% 3.93/1.02      ( k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3)
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top
% 3.93/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1279,c_1277]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_33,negated_conjecture,
% 3.93/1.02      ( v1_funct_1(sK3) ),
% 3.93/1.02      inference(cnf_transformation,[],[f90]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_38,plain,
% 3.93/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2830,plain,
% 3.93/1.02      ( v1_funct_1(X0_51) != iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.93/1.02      | k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_2641,c_38]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2831,plain,
% 3.93/1.02      ( k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3)
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.93/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(renaming,[status(thm)],[c_2830]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2837,plain,
% 3.93/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.93/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1281,c_2831]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_19,plain,
% 3.93/1.02      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.93/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.93/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.93/1.02      | X3 = X2 ),
% 3.93/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_30,negated_conjecture,
% 3.93/1.02      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.93/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_381,plain,
% 3.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.02      | X3 = X0
% 3.93/1.02      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.93/1.02      | k6_partfun1(sK0) != X3
% 3.93/1.02      | sK0 != X2
% 3.93/1.02      | sK0 != X1 ),
% 3.93/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_382,plain,
% 3.93/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.93/1.02      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.93/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.93/1.02      inference(unflattening,[status(thm)],[c_381]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_22,plain,
% 3.93/1.02      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.93/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_50,plain,
% 3.93/1.02      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_22]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_384,plain,
% 3.93/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.93/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_382,c_50]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_757,plain,
% 3.93/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.93/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_384]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1284,plain,
% 3.93/1.02      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.93/1.02      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_20,plain,
% 3.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.93/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.93/1.02      | ~ v1_funct_1(X0)
% 3.93/1.02      | ~ v1_funct_1(X3) ),
% 3.93/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_771,plain,
% 3.93/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.93/1.02      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
% 3.93/1.02      | m1_subset_1(k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
% 3.93/1.02      | ~ v1_funct_1(X0_51)
% 3.93/1.02      | ~ v1_funct_1(X1_51) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_20]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1342,plain,
% 3.93/1.02      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.93/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.93/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.93/1.02      | ~ v1_funct_1(sK3)
% 3.93/1.02      | ~ v1_funct_1(sK2) ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_771]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1785,plain,
% 3.93/1.02      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_1284,c_35,c_34,c_33,c_32,c_757,c_1342]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2841,plain,
% 3.93/1.02      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.93/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.93/1.02      inference(light_normalisation,[status(thm)],[c_2837,c_1785]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_3620,plain,
% 3.93/1.02      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_2841,c_36]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_16,plain,
% 3.93/1.02      ( v4_relat_1(X0,X1)
% 3.93/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.93/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 3.93/1.02      | ~ v4_relat_1(X0,X1)
% 3.93/1.02      | ~ v1_relat_1(X0) ),
% 3.93/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_360,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 3.93/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.02      | ~ v1_relat_1(X0) ),
% 3.93/1.02      inference(resolution,[status(thm)],[c_16,c_2]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_758,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(X0_51),X0_52)
% 3.93/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.93/1.02      | ~ v1_relat_1(X0_51) ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_360]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1283,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_823,plain,
% 3.93/1.02      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) = iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_865,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1402,plain,
% 3.93/1.02      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.93/1.02      | v1_relat_1(X0_51) = iProver_top
% 3.93/1.02      | v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_1401]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_3994,plain,
% 3.93/1.02      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.93/1.02      | r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_1283,c_823,c_865,c_1402]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_3995,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
% 3.93/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.93/1.02      inference(renaming,[status(thm)],[c_3994]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4000,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1279,c_3995]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_7,plain,
% 3.93/1.02      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.93/1.02      | ~ v1_relat_1(X0)
% 3.93/1.02      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 3.93/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_776,plain,
% 3.93/1.02      ( ~ r1_tarski(k1_relat_1(X0_51),X0_52)
% 3.93/1.02      | ~ v1_relat_1(X0_51)
% 3.93/1.02      | k5_relat_1(k6_partfun1(X0_52),X0_51) = X0_51 ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1269,plain,
% 3.93/1.02      ( k5_relat_1(k6_partfun1(X0_52),X0_51) = X0_51
% 3.93/1.02      | r1_tarski(k1_relat_1(X0_51),X0_52) != iProver_top
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4515,plain,
% 3.93/1.02      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 3.93/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_4000,c_1269]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2001,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(sK3),X0_52)
% 3.93/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.93/1.02      | ~ v1_relat_1(sK3) ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_758]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_3678,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(sK3),sK1)
% 3.93/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.93/1.02      | ~ v1_relat_1(sK3) ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_2001]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1727,plain,
% 3.93/1.02      ( ~ r1_tarski(k1_relat_1(sK3),X0_52)
% 3.93/1.02      | ~ v1_relat_1(sK3)
% 3.93/1.02      | k5_relat_1(k6_partfun1(X0_52),sK3) = sK3 ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_776]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4398,plain,
% 3.93/1.02      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
% 3.93/1.02      | ~ v1_relat_1(sK3)
% 3.93/1.02      | k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 3.93/1.02      inference(instantiation,[status(thm)],[c_1727]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4733,plain,
% 3.93/1.02      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_4515,c_32,c_1495,c_1533,c_3678,c_4398]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4001,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1281,c_3995]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_8,plain,
% 3.93/1.02      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.93/1.02      | ~ v1_relat_1(X0)
% 3.93/1.02      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 3.93/1.02      inference(cnf_transformation,[],[f99]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_775,plain,
% 3.93/1.02      ( ~ r1_tarski(k2_relat_1(X0_51),X0_52)
% 3.93/1.02      | ~ v1_relat_1(X0_51)
% 3.93/1.02      | k5_relat_1(X0_51,k6_partfun1(X0_52)) = X0_51 ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_1270,plain,
% 3.93/1.02      ( k5_relat_1(X0_51,k6_partfun1(X0_52)) = X0_51
% 3.93/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.93/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.93/1.02      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_2390,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2)
% 3.93/1.02      | r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top
% 3.93/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_1631,c_1270]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4846,plain,
% 3.93/1.02      ( r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top
% 3.93/1.02      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2) ),
% 3.93/1.02      inference(global_propositional_subsumption,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_2390,c_36,c_37,c_844,c_1412,c_1425]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4847,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2)
% 3.93/1.02      | r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top ),
% 3.93/1.02      inference(renaming,[status(thm)],[c_4846]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_4852,plain,
% 3.93/1.02      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 3.93/1.02      inference(superposition,[status(thm)],[c_4001,c_4847]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_11611,plain,
% 3.93/1.02      ( k2_funct_1(sK2) = sK3 ),
% 3.93/1.02      inference(light_normalisation,
% 3.93/1.02                [status(thm)],
% 3.93/1.02                [c_11604,c_3620,c_4733,c_4852]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_26,negated_conjecture,
% 3.93/1.02      ( k2_funct_1(sK2) != sK3 ),
% 3.93/1.02      inference(cnf_transformation,[],[f97]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(c_766,negated_conjecture,
% 3.93/1.02      ( k2_funct_1(sK2) != sK3 ),
% 3.93/1.02      inference(subtyping,[status(esa)],[c_26]) ).
% 3.93/1.02  
% 3.93/1.02  cnf(contradiction,plain,
% 3.93/1.02      ( $false ),
% 3.93/1.02      inference(minisat,[status(thm)],[c_11611,c_766]) ).
% 3.93/1.02  
% 3.93/1.02  
% 3.93/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.02  
% 3.93/1.02  ------                               Statistics
% 3.93/1.02  
% 3.93/1.02  ------ General
% 3.93/1.02  
% 3.93/1.02  abstr_ref_over_cycles:                  0
% 3.93/1.02  abstr_ref_under_cycles:                 0
% 3.93/1.02  gc_basic_clause_elim:                   0
% 3.93/1.02  forced_gc_time:                         0
% 3.93/1.02  parsing_time:                           0.01
% 3.93/1.02  unif_index_cands_time:                  0.
% 3.93/1.02  unif_index_add_time:                    0.
% 3.93/1.02  orderings_time:                         0.
% 3.93/1.02  out_proof_time:                         0.016
% 3.93/1.02  total_time:                             0.44
% 3.93/1.02  num_of_symbols:                         57
% 3.93/1.02  num_of_terms:                           16114
% 3.93/1.02  
% 3.93/1.02  ------ Preprocessing
% 3.93/1.02  
% 3.93/1.02  num_of_splits:                          0
% 3.93/1.02  num_of_split_atoms:                     0
% 3.93/1.02  num_of_reused_defs:                     0
% 3.93/1.02  num_eq_ax_congr_red:                    6
% 3.93/1.02  num_of_sem_filtered_clauses:            1
% 3.93/1.02  num_of_subtypes:                        3
% 3.93/1.02  monotx_restored_types:                  1
% 3.93/1.02  sat_num_of_epr_types:                   0
% 3.93/1.02  sat_num_of_non_cyclic_types:            0
% 3.93/1.02  sat_guarded_non_collapsed_types:        0
% 3.93/1.02  num_pure_diseq_elim:                    0
% 3.93/1.02  simp_replaced_by:                       0
% 3.93/1.02  res_preprocessed:                       166
% 3.93/1.02  prep_upred:                             0
% 3.93/1.02  prep_unflattend:                        15
% 3.93/1.02  smt_new_axioms:                         0
% 3.93/1.02  pred_elim_cands:                        4
% 3.93/1.02  pred_elim:                              3
% 3.93/1.02  pred_elim_cl:                           5
% 3.93/1.02  pred_elim_cycles:                       6
% 3.93/1.02  merged_defs:                            0
% 3.93/1.02  merged_defs_ncl:                        0
% 3.93/1.02  bin_hyper_res:                          0
% 3.93/1.02  prep_cycles:                            4
% 3.93/1.02  pred_elim_time:                         0.003
% 3.93/1.02  splitting_time:                         0.
% 3.93/1.02  sem_filter_time:                        0.
% 3.93/1.02  monotx_time:                            0.001
% 3.93/1.02  subtype_inf_time:                       0.001
% 3.93/1.02  
% 3.93/1.02  ------ Problem properties
% 3.93/1.02  
% 3.93/1.02  clauses:                                30
% 3.93/1.02  conjectures:                            8
% 3.93/1.02  epr:                                    4
% 3.93/1.02  horn:                                   30
% 3.93/1.02  ground:                                 13
% 3.93/1.02  unary:                                  10
% 3.93/1.02  binary:                                 9
% 3.93/1.02  lits:                                   68
% 3.93/1.02  lits_eq:                                17
% 3.93/1.02  fd_pure:                                0
% 3.93/1.02  fd_pseudo:                              0
% 3.93/1.02  fd_cond:                                0
% 3.93/1.02  fd_pseudo_cond:                         0
% 3.93/1.02  ac_symbols:                             0
% 3.93/1.02  
% 3.93/1.02  ------ Propositional Solver
% 3.93/1.02  
% 3.93/1.02  prop_solver_calls:                      33
% 3.93/1.02  prop_fast_solver_calls:                 1375
% 3.93/1.02  smt_solver_calls:                       0
% 3.93/1.02  smt_fast_solver_calls:                  0
% 3.93/1.02  prop_num_of_clauses:                    5147
% 3.93/1.02  prop_preprocess_simplified:             13546
% 3.93/1.02  prop_fo_subsumed:                       90
% 3.93/1.02  prop_solver_time:                       0.
% 3.93/1.02  smt_solver_time:                        0.
% 3.93/1.02  smt_fast_solver_time:                   0.
% 3.93/1.02  prop_fast_solver_time:                  0.
% 3.93/1.02  prop_unsat_core_time:                   0.
% 3.93/1.02  
% 3.93/1.02  ------ QBF
% 3.93/1.02  
% 3.93/1.02  qbf_q_res:                              0
% 3.93/1.02  qbf_num_tautologies:                    0
% 3.93/1.02  qbf_prep_cycles:                        0
% 3.93/1.02  
% 3.93/1.02  ------ BMC1
% 3.93/1.02  
% 3.93/1.02  bmc1_current_bound:                     -1
% 3.93/1.02  bmc1_last_solved_bound:                 -1
% 3.93/1.02  bmc1_unsat_core_size:                   -1
% 3.93/1.02  bmc1_unsat_core_parents_size:           -1
% 3.93/1.02  bmc1_merge_next_fun:                    0
% 3.93/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.93/1.02  
% 3.93/1.02  ------ Instantiation
% 3.93/1.02  
% 3.93/1.02  inst_num_of_clauses:                    1560
% 3.93/1.02  inst_num_in_passive:                    138
% 3.93/1.02  inst_num_in_active:                     1019
% 3.93/1.02  inst_num_in_unprocessed:                406
% 3.93/1.02  inst_num_of_loops:                      1110
% 3.93/1.02  inst_num_of_learning_restarts:          0
% 3.93/1.02  inst_num_moves_active_passive:          86
% 3.93/1.02  inst_lit_activity:                      0
% 3.93/1.02  inst_lit_activity_moves:                1
% 3.93/1.02  inst_num_tautologies:                   0
% 3.93/1.02  inst_num_prop_implied:                  0
% 3.93/1.02  inst_num_existing_simplified:           0
% 3.93/1.02  inst_num_eq_res_simplified:             0
% 3.93/1.02  inst_num_child_elim:                    0
% 3.93/1.02  inst_num_of_dismatching_blockings:      1283
% 3.93/1.02  inst_num_of_non_proper_insts:           2474
% 3.93/1.02  inst_num_of_duplicates:                 0
% 3.93/1.02  inst_inst_num_from_inst_to_res:         0
% 3.93/1.02  inst_dismatching_checking_time:         0.
% 3.93/1.02  
% 3.93/1.02  ------ Resolution
% 3.93/1.02  
% 3.93/1.02  res_num_of_clauses:                     0
% 3.93/1.02  res_num_in_passive:                     0
% 3.93/1.02  res_num_in_active:                      0
% 3.93/1.02  res_num_of_loops:                       170
% 3.93/1.02  res_forward_subset_subsumed:            160
% 3.93/1.02  res_backward_subset_subsumed:           16
% 3.93/1.02  res_forward_subsumed:                   0
% 3.93/1.02  res_backward_subsumed:                  0
% 3.93/1.02  res_forward_subsumption_resolution:     0
% 3.93/1.02  res_backward_subsumption_resolution:    0
% 3.93/1.02  res_clause_to_clause_subsumption:       1036
% 3.93/1.02  res_orphan_elimination:                 0
% 3.93/1.02  res_tautology_del:                      143
% 3.93/1.02  res_num_eq_res_simplified:              0
% 3.93/1.02  res_num_sel_changes:                    0
% 3.93/1.02  res_moves_from_active_to_pass:          0
% 3.93/1.02  
% 3.93/1.02  ------ Superposition
% 3.93/1.02  
% 3.93/1.02  sup_time_total:                         0.
% 3.93/1.02  sup_time_generating:                    0.
% 3.93/1.02  sup_time_sim_full:                      0.
% 3.93/1.02  sup_time_sim_immed:                     0.
% 3.93/1.02  
% 3.93/1.02  sup_num_of_clauses:                     545
% 3.93/1.02  sup_num_in_active:                      217
% 3.93/1.02  sup_num_in_passive:                     328
% 3.93/1.02  sup_num_of_loops:                       220
% 3.93/1.02  sup_fw_superposition:                   383
% 3.93/1.02  sup_bw_superposition:                   180
% 3.93/1.02  sup_immediate_simplified:               123
% 3.93/1.02  sup_given_eliminated:                   1
% 3.93/1.02  comparisons_done:                       0
% 3.93/1.02  comparisons_avoided:                    0
% 3.93/1.02  
% 3.93/1.02  ------ Simplifications
% 3.93/1.02  
% 3.93/1.02  
% 3.93/1.02  sim_fw_subset_subsumed:                 10
% 3.93/1.02  sim_bw_subset_subsumed:                 4
% 3.93/1.02  sim_fw_subsumed:                        6
% 3.93/1.02  sim_bw_subsumed:                        2
% 3.93/1.02  sim_fw_subsumption_res:                 0
% 3.93/1.02  sim_bw_subsumption_res:                 0
% 3.93/1.02  sim_tautology_del:                      1
% 3.93/1.02  sim_eq_tautology_del:                   10
% 3.93/1.02  sim_eq_res_simp:                        0
% 3.93/1.02  sim_fw_demodulated:                     2
% 3.93/1.02  sim_bw_demodulated:                     7
% 3.93/1.02  sim_light_normalised:                   113
% 3.93/1.02  sim_joinable_taut:                      0
% 3.93/1.02  sim_joinable_simp:                      0
% 3.93/1.02  sim_ac_normalised:                      0
% 3.93/1.02  sim_smt_subsumption:                    0
% 3.93/1.02  
%------------------------------------------------------------------------------
