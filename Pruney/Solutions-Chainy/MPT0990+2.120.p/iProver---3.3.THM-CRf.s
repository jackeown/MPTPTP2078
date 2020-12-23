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
% DateTime   : Thu Dec  3 12:03:22 EST 2020

% Result     : Theorem 35.54s
% Output     : CNFRefutation 35.54s
% Verified   : 
% Statistics : Number of formulae       :  325 (18363 expanded)
%              Number of clauses        :  209 (5777 expanded)
%              Number of leaves         :   30 (4179 expanded)
%              Depth                    :   39
%              Number of atoms          :  844 (121698 expanded)
%              Number of equality atoms :  396 (45989 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f98,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f31,plain,(
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
    inference(pure_predicate_removal,[],[f30])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f68,plain,(
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
    inference(flattening,[],[f67])).

fof(f73,plain,(
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

fof(f72,plain,
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

fof(f74,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f68,f73,f72])).

fof(f118,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f112,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f113,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f92,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f65,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f65])).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f97,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f116,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

fof(f115,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f63])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f114,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f59])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f117,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f24,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f129,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f105,f109])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f61])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f12,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f124,plain,(
    ! [X0] : k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f89,f109,f109])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f122,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f88,f109])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f69])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f130,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f90,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f125,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f90,f109])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f91,f109])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f99,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f128,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f99,f109])).

fof(f100,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f127,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f100,f109])).

fof(f121,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_520,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_39])).

cnf(c_521,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_523,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_45])).

cnf(c_1394,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1490,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1577,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_1695,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1730,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1841,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1394,c_45,c_44,c_521,c_1695,c_1730])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_552,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_553,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_555,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_45])).

cnf(c_1392,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_1775,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1392,c_45,c_44,c_553,c_1695,c_1730])).

cnf(c_1843,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1841,c_1775])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1404,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2652,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_1404])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_506,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_507,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_509,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_45])).

cnf(c_1395,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_1964,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1395,c_45,c_44,c_507,c_1695,c_1730])).

cnf(c_1966,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1964,c_1775])).

cnf(c_2654,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2652,c_1966])).

cnf(c_46,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_1696,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1695])).

cnf(c_1731,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1730])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2039,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2047,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2039])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1411,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3584,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1411])).

cnf(c_10491,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2654,c_46,c_47,c_1696,c_1731,c_2047,c_3584])).

cnf(c_1401,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1409,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2753,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1401,c_1409])).

cnf(c_41,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2754,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2753,c_41])).

cnf(c_1421,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3703,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1421])).

cnf(c_3790,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3703,c_47,c_1696,c_1731])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1403,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_3702,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1421])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_1679,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1894,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_1895,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_2118,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2119,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_3714,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3702,c_49,c_1895,c_2119])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1415,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4251,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3714,c_1415])).

cnf(c_7145,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3790,c_4251])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1405,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5455,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1405])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_48,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5746,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5455,c_48])).

cnf(c_5747,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5746])).

cnf(c_5756,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_5747])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_40,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_40])).

cnf(c_462,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_30,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_66,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_464,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_66])).

cnf(c_1398,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1482,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2152,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1398,c_45,c_44,c_43,c_42,c_66,c_462,c_1482])).

cnf(c_5759,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5756,c_2152])).

cnf(c_6647,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5759,c_46])).

cnf(c_7149,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_7145,c_6647])).

cnf(c_14,plain,
    ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_7150,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_7149,c_14])).

cnf(c_9,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1416,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8823,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2))) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7150,c_1416])).

cnf(c_8824,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8823,c_1843])).

cnf(c_12,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_8825,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8824,c_12])).

cnf(c_2015,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2027,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_9736,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8825,c_47,c_49,c_1696,c_1731,c_1895,c_2027,c_2047,c_2119])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_566,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_567,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_571,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_45])).

cnf(c_1391,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_9741,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9736,c_1391])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1418,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3795,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3790,c_1418])).

cnf(c_3799,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3795,c_2754])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1422,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1772,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1391])).

cnf(c_2422,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1772,c_47,c_1696,c_1731])).

cnf(c_3898,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3799,c_2422])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_26,c_8])).

cnf(c_1399,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_2156,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1399])).

cnf(c_2419,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2156,c_47,c_1696,c_1731])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1417,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3794,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_3790,c_1417])).

cnf(c_4621,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2419,c_3794])).

cnf(c_4625,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4621,c_2754])).

cnf(c_9742,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9741,c_3898,c_4625])).

cnf(c_9836,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9742,c_47,c_1696,c_1731])).

cnf(c_10495,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10491,c_2754,c_9836])).

cnf(c_10497,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10495,c_1421])).

cnf(c_10677,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10497,c_47,c_1696,c_1731,c_2047])).

cnf(c_1420,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1413,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2516,plain,
    ( k5_relat_1(k4_relat_1(X0),k6_partfun1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1413])).

cnf(c_10686,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(k2_relat_1(k4_relat_1(k4_relat_1(sK2))))) = k4_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_10677,c_2516])).

cnf(c_1419,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1408,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3700,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_1421])).

cnf(c_6910,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_3700])).

cnf(c_10689,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(sK2)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10677,c_1415])).

cnf(c_22991,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k4_relat_1(k6_partfun1(X0))) = k4_relat_1(k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_6910,c_10689])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1412,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2642,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(X1)) = k7_relat_1(k4_relat_1(X1),X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1412])).

cnf(c_8706,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k7_relat_1(k4_relat_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_3790,c_2642])).

cnf(c_23007,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(X0)) = k4_relat_1(k7_relat_1(k4_relat_1(sK2),X0)) ),
    inference(light_normalisation,[status(thm)],[c_22991,c_14,c_8706])).

cnf(c_112082,plain,
    ( k4_relat_1(k7_relat_1(k4_relat_1(sK2),k2_relat_1(k4_relat_1(k4_relat_1(sK2))))) = k4_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_10686,c_23007])).

cnf(c_112085,plain,
    ( v1_relat_1(k7_relat_1(k4_relat_1(sK2),k2_relat_1(k4_relat_1(k4_relat_1(sK2))))) != iProver_top
    | v1_relat_1(k4_relat_1(k4_relat_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_112082,c_1420])).

cnf(c_2227,plain,
    ( v1_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2235,plain,
    ( v1_relat_1(k4_relat_1(k4_relat_1(sK2))) = iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2227])).

cnf(c_113576,plain,
    ( v1_relat_1(k4_relat_1(k4_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_112085,c_47,c_1696,c_1731,c_2047,c_2235])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1414,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4375,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_1414])).

cnf(c_10684,plain,
    ( k5_relat_1(k5_relat_1(sK2,k4_relat_1(sK2)),X0) = k5_relat_1(sK2,k5_relat_1(k4_relat_1(sK2),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10677,c_4375])).

cnf(c_25,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_478,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_479,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_481,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_45])).

cnf(c_1397,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_2059,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1397,c_45,c_44,c_479,c_1695,c_1730])).

cnf(c_2061,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2059,c_1775])).

cnf(c_9849,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_9836,c_2061])).

cnf(c_10703,plain,
    ( k5_relat_1(sK2,k5_relat_1(k4_relat_1(sK2),X0)) = k5_relat_1(k6_partfun1(sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10684,c_9849])).

cnf(c_116863,plain,
    ( k5_relat_1(sK2,k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2)))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(k4_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_113576,c_10703])).

cnf(c_3796,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_3790,c_1413])).

cnf(c_3798,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3796,c_2754])).

cnf(c_4250,plain,
    ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_1415])).

cnf(c_10687,plain,
    ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2))) = k4_relat_1(k5_relat_1(k4_relat_1(sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_10677,c_4250])).

cnf(c_24,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_492,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_493,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_495,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_45])).

cnf(c_1396,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2055,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1396,c_45,c_44,c_493,c_1695,c_1730])).

cnf(c_2057,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2055,c_1775])).

cnf(c_2914,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2754,c_2057])).

cnf(c_10701,plain,
    ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2))) = k4_relat_1(k6_partfun1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_10687,c_2914])).

cnf(c_10702,plain,
    ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2))) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_10701,c_14])).

cnf(c_116890,plain,
    ( k5_relat_1(k6_partfun1(sK0),k4_relat_1(k4_relat_1(sK2))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_116863,c_3798,c_10702])).

cnf(c_6918,plain,
    ( k5_relat_1(k4_relat_1(k6_partfun1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_partfun1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6910,c_1415])).

cnf(c_6926,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_partfun1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6918,c_14])).

cnf(c_10693,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(k4_relat_1(sK2))) = k4_relat_1(k5_relat_1(k4_relat_1(sK2),k6_partfun1(X0))) ),
    inference(superposition,[status(thm)],[c_10677,c_6926])).

cnf(c_10694,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(k4_relat_1(sK2))) = k7_relat_1(k4_relat_1(k4_relat_1(sK2)),X0) ),
    inference(superposition,[status(thm)],[c_10677,c_2642])).

cnf(c_10696,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK2),k6_partfun1(X0))) = k7_relat_1(k4_relat_1(k4_relat_1(sK2)),X0) ),
    inference(demodulation,[status(thm)],[c_10693,c_10694])).

cnf(c_6916,plain,
    ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k6_partfun1(X0))) = k4_relat_1(k5_relat_1(k6_partfun1(X0),sK2)) ),
    inference(superposition,[status(thm)],[c_6910,c_4250])).

cnf(c_3797,plain,
    ( k5_relat_1(k6_partfun1(X0),sK2) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_3790,c_1412])).

cnf(c_6927,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(X0)) = k4_relat_1(k7_relat_1(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6916,c_14,c_3797])).

cnf(c_10697,plain,
    ( k7_relat_1(k4_relat_1(k4_relat_1(sK2)),X0) = k4_relat_1(k4_relat_1(k7_relat_1(sK2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_10696,c_6927])).

cnf(c_10698,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(k4_relat_1(sK2))) = k4_relat_1(k4_relat_1(k7_relat_1(sK2,X0))) ),
    inference(demodulation,[status(thm)],[c_10697,c_10694])).

cnf(c_117438,plain,
    ( k4_relat_1(k4_relat_1(k7_relat_1(sK2,sK0))) = sK2 ),
    inference(superposition,[status(thm)],[c_116890,c_10698])).

cnf(c_117439,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_117438,c_2419])).

cnf(c_10688,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10677,c_1414])).

cnf(c_113580,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2))),X0) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(k4_relat_1(k4_relat_1(sK2)),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_113576,c_10688])).

cnf(c_113737,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(k4_relat_1(k4_relat_1(sK2)),X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_113580,c_10702])).

cnf(c_113891,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(k4_relat_1(k4_relat_1(sK2)),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3714,c_113737])).

cnf(c_2155,plain,
    ( k7_relat_1(sK3,sK1) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1399])).

cnf(c_2349,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2155,c_49,c_1895,c_2119])).

cnf(c_3721,plain,
    ( k5_relat_1(k6_partfun1(X0),sK3) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3714,c_1412])).

cnf(c_113930,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(k4_relat_1(k4_relat_1(sK2)),sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_113891,c_2349,c_3721])).

cnf(c_117752,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_117439,c_113930])).

cnf(c_6656,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3790,c_2516])).

cnf(c_6658,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6656,c_1843])).

cnf(c_17773,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6658,c_6658,c_9836])).

cnf(c_117783,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_117752,c_6647,c_17773])).

cnf(c_36,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1777,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_1775,c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_117783,c_1777])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.54/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.54/4.99  
% 35.54/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.54/4.99  
% 35.54/4.99  ------  iProver source info
% 35.54/4.99  
% 35.54/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.54/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.54/4.99  git: non_committed_changes: false
% 35.54/4.99  git: last_make_outside_of_git: false
% 35.54/4.99  
% 35.54/4.99  ------ 
% 35.54/4.99  
% 35.54/4.99  ------ Input Options
% 35.54/4.99  
% 35.54/4.99  --out_options                           all
% 35.54/4.99  --tptp_safe_out                         true
% 35.54/4.99  --problem_path                          ""
% 35.54/4.99  --include_path                          ""
% 35.54/4.99  --clausifier                            res/vclausify_rel
% 35.54/4.99  --clausifier_options                    ""
% 35.54/4.99  --stdin                                 false
% 35.54/4.99  --stats_out                             all
% 35.54/4.99  
% 35.54/4.99  ------ General Options
% 35.54/4.99  
% 35.54/4.99  --fof                                   false
% 35.54/4.99  --time_out_real                         305.
% 35.54/4.99  --time_out_virtual                      -1.
% 35.54/4.99  --symbol_type_check                     false
% 35.54/4.99  --clausify_out                          false
% 35.54/4.99  --sig_cnt_out                           false
% 35.54/4.99  --trig_cnt_out                          false
% 35.54/4.99  --trig_cnt_out_tolerance                1.
% 35.54/4.99  --trig_cnt_out_sk_spl                   false
% 35.54/4.99  --abstr_cl_out                          false
% 35.54/4.99  
% 35.54/4.99  ------ Global Options
% 35.54/4.99  
% 35.54/4.99  --schedule                              default
% 35.54/4.99  --add_important_lit                     false
% 35.54/4.99  --prop_solver_per_cl                    1000
% 35.54/4.99  --min_unsat_core                        false
% 35.54/4.99  --soft_assumptions                      false
% 35.54/4.99  --soft_lemma_size                       3
% 35.54/4.99  --prop_impl_unit_size                   0
% 35.54/4.99  --prop_impl_unit                        []
% 35.54/4.99  --share_sel_clauses                     true
% 35.54/4.99  --reset_solvers                         false
% 35.54/4.99  --bc_imp_inh                            [conj_cone]
% 35.54/4.99  --conj_cone_tolerance                   3.
% 35.54/4.99  --extra_neg_conj                        none
% 35.54/4.99  --large_theory_mode                     true
% 35.54/4.99  --prolific_symb_bound                   200
% 35.54/4.99  --lt_threshold                          2000
% 35.54/4.99  --clause_weak_htbl                      true
% 35.54/4.99  --gc_record_bc_elim                     false
% 35.54/4.99  
% 35.54/4.99  ------ Preprocessing Options
% 35.54/4.99  
% 35.54/4.99  --preprocessing_flag                    true
% 35.54/4.99  --time_out_prep_mult                    0.1
% 35.54/4.99  --splitting_mode                        input
% 35.54/4.99  --splitting_grd                         true
% 35.54/4.99  --splitting_cvd                         false
% 35.54/4.99  --splitting_cvd_svl                     false
% 35.54/4.99  --splitting_nvd                         32
% 35.54/4.99  --sub_typing                            true
% 35.54/4.99  --prep_gs_sim                           true
% 35.54/4.99  --prep_unflatten                        true
% 35.54/4.99  --prep_res_sim                          true
% 35.54/4.99  --prep_upred                            true
% 35.54/4.99  --prep_sem_filter                       exhaustive
% 35.54/4.99  --prep_sem_filter_out                   false
% 35.54/4.99  --pred_elim                             true
% 35.54/4.99  --res_sim_input                         true
% 35.54/4.99  --eq_ax_congr_red                       true
% 35.54/4.99  --pure_diseq_elim                       true
% 35.54/4.99  --brand_transform                       false
% 35.54/4.99  --non_eq_to_eq                          false
% 35.54/4.99  --prep_def_merge                        true
% 35.54/4.99  --prep_def_merge_prop_impl              false
% 35.54/4.99  --prep_def_merge_mbd                    true
% 35.54/4.99  --prep_def_merge_tr_red                 false
% 35.54/4.99  --prep_def_merge_tr_cl                  false
% 35.54/4.99  --smt_preprocessing                     true
% 35.54/4.99  --smt_ac_axioms                         fast
% 35.54/4.99  --preprocessed_out                      false
% 35.54/4.99  --preprocessed_stats                    false
% 35.54/4.99  
% 35.54/4.99  ------ Abstraction refinement Options
% 35.54/4.99  
% 35.54/4.99  --abstr_ref                             []
% 35.54/4.99  --abstr_ref_prep                        false
% 35.54/4.99  --abstr_ref_until_sat                   false
% 35.54/4.99  --abstr_ref_sig_restrict                funpre
% 35.54/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.54/4.99  --abstr_ref_under                       []
% 35.54/4.99  
% 35.54/4.99  ------ SAT Options
% 35.54/4.99  
% 35.54/4.99  --sat_mode                              false
% 35.54/4.99  --sat_fm_restart_options                ""
% 35.54/4.99  --sat_gr_def                            false
% 35.54/4.99  --sat_epr_types                         true
% 35.54/4.99  --sat_non_cyclic_types                  false
% 35.54/4.99  --sat_finite_models                     false
% 35.54/4.99  --sat_fm_lemmas                         false
% 35.54/4.99  --sat_fm_prep                           false
% 35.54/4.99  --sat_fm_uc_incr                        true
% 35.54/4.99  --sat_out_model                         small
% 35.54/4.99  --sat_out_clauses                       false
% 35.54/4.99  
% 35.54/4.99  ------ QBF Options
% 35.54/4.99  
% 35.54/4.99  --qbf_mode                              false
% 35.54/4.99  --qbf_elim_univ                         false
% 35.54/4.99  --qbf_dom_inst                          none
% 35.54/4.99  --qbf_dom_pre_inst                      false
% 35.54/4.99  --qbf_sk_in                             false
% 35.54/4.99  --qbf_pred_elim                         true
% 35.54/4.99  --qbf_split                             512
% 35.54/4.99  
% 35.54/4.99  ------ BMC1 Options
% 35.54/4.99  
% 35.54/4.99  --bmc1_incremental                      false
% 35.54/4.99  --bmc1_axioms                           reachable_all
% 35.54/4.99  --bmc1_min_bound                        0
% 35.54/4.99  --bmc1_max_bound                        -1
% 35.54/4.99  --bmc1_max_bound_default                -1
% 35.54/4.99  --bmc1_symbol_reachability              true
% 35.54/4.99  --bmc1_property_lemmas                  false
% 35.54/4.99  --bmc1_k_induction                      false
% 35.54/4.99  --bmc1_non_equiv_states                 false
% 35.54/4.99  --bmc1_deadlock                         false
% 35.54/4.99  --bmc1_ucm                              false
% 35.54/4.99  --bmc1_add_unsat_core                   none
% 35.54/4.99  --bmc1_unsat_core_children              false
% 35.54/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.54/4.99  --bmc1_out_stat                         full
% 35.54/4.99  --bmc1_ground_init                      false
% 35.54/4.99  --bmc1_pre_inst_next_state              false
% 35.54/4.99  --bmc1_pre_inst_state                   false
% 35.54/4.99  --bmc1_pre_inst_reach_state             false
% 35.54/4.99  --bmc1_out_unsat_core                   false
% 35.54/4.99  --bmc1_aig_witness_out                  false
% 35.54/4.99  --bmc1_verbose                          false
% 35.54/4.99  --bmc1_dump_clauses_tptp                false
% 35.54/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.54/4.99  --bmc1_dump_file                        -
% 35.54/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.54/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.54/4.99  --bmc1_ucm_extend_mode                  1
% 35.54/4.99  --bmc1_ucm_init_mode                    2
% 35.54/4.99  --bmc1_ucm_cone_mode                    none
% 35.54/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.54/4.99  --bmc1_ucm_relax_model                  4
% 35.54/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.54/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.54/4.99  --bmc1_ucm_layered_model                none
% 35.54/4.99  --bmc1_ucm_max_lemma_size               10
% 35.54/4.99  
% 35.54/4.99  ------ AIG Options
% 35.54/4.99  
% 35.54/4.99  --aig_mode                              false
% 35.54/4.99  
% 35.54/4.99  ------ Instantiation Options
% 35.54/4.99  
% 35.54/4.99  --instantiation_flag                    true
% 35.54/4.99  --inst_sos_flag                         true
% 35.54/4.99  --inst_sos_phase                        true
% 35.54/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.54/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.54/4.99  --inst_lit_sel_side                     num_symb
% 35.54/4.99  --inst_solver_per_active                1400
% 35.54/4.99  --inst_solver_calls_frac                1.
% 35.54/4.99  --inst_passive_queue_type               priority_queues
% 35.54/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.54/4.99  --inst_passive_queues_freq              [25;2]
% 35.54/4.99  --inst_dismatching                      true
% 35.54/4.99  --inst_eager_unprocessed_to_passive     true
% 35.54/4.99  --inst_prop_sim_given                   true
% 35.54/4.99  --inst_prop_sim_new                     false
% 35.54/4.99  --inst_subs_new                         false
% 35.54/4.99  --inst_eq_res_simp                      false
% 35.54/4.99  --inst_subs_given                       false
% 35.54/4.99  --inst_orphan_elimination               true
% 35.54/4.99  --inst_learning_loop_flag               true
% 35.54/4.99  --inst_learning_start                   3000
% 35.54/4.99  --inst_learning_factor                  2
% 35.54/4.99  --inst_start_prop_sim_after_learn       3
% 35.54/4.99  --inst_sel_renew                        solver
% 35.54/4.99  --inst_lit_activity_flag                true
% 35.54/4.99  --inst_restr_to_given                   false
% 35.54/4.99  --inst_activity_threshold               500
% 35.54/4.99  --inst_out_proof                        true
% 35.54/4.99  
% 35.54/4.99  ------ Resolution Options
% 35.54/4.99  
% 35.54/4.99  --resolution_flag                       true
% 35.54/4.99  --res_lit_sel                           adaptive
% 35.54/4.99  --res_lit_sel_side                      none
% 35.54/4.99  --res_ordering                          kbo
% 35.54/4.99  --res_to_prop_solver                    active
% 35.54/4.99  --res_prop_simpl_new                    false
% 35.54/4.99  --res_prop_simpl_given                  true
% 35.54/4.99  --res_passive_queue_type                priority_queues
% 35.54/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.54/4.99  --res_passive_queues_freq               [15;5]
% 35.54/4.99  --res_forward_subs                      full
% 35.54/4.99  --res_backward_subs                     full
% 35.54/4.99  --res_forward_subs_resolution           true
% 35.54/4.99  --res_backward_subs_resolution          true
% 35.54/4.99  --res_orphan_elimination                true
% 35.54/4.99  --res_time_limit                        2.
% 35.54/4.99  --res_out_proof                         true
% 35.54/4.99  
% 35.54/4.99  ------ Superposition Options
% 35.54/4.99  
% 35.54/4.99  --superposition_flag                    true
% 35.54/4.99  --sup_passive_queue_type                priority_queues
% 35.54/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.54/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.54/4.99  --demod_completeness_check              fast
% 35.54/4.99  --demod_use_ground                      true
% 35.54/4.99  --sup_to_prop_solver                    passive
% 35.54/4.99  --sup_prop_simpl_new                    true
% 35.54/4.99  --sup_prop_simpl_given                  true
% 35.54/4.99  --sup_fun_splitting                     true
% 35.54/4.99  --sup_smt_interval                      50000
% 35.54/4.99  
% 35.54/4.99  ------ Superposition Simplification Setup
% 35.54/4.99  
% 35.54/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.54/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.54/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.54/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.54/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.54/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.54/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.54/4.99  --sup_immed_triv                        [TrivRules]
% 35.54/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.54/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.54/4.99  --sup_immed_bw_main                     []
% 35.54/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.54/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.54/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.54/4.99  --sup_input_bw                          []
% 35.54/4.99  
% 35.54/4.99  ------ Combination Options
% 35.54/4.99  
% 35.54/4.99  --comb_res_mult                         3
% 35.54/4.99  --comb_sup_mult                         2
% 35.54/4.99  --comb_inst_mult                        10
% 35.54/4.99  
% 35.54/4.99  ------ Debug Options
% 35.54/4.99  
% 35.54/4.99  --dbg_backtrace                         false
% 35.54/4.99  --dbg_dump_prop_clauses                 false
% 35.54/4.99  --dbg_dump_prop_clauses_file            -
% 35.54/4.99  --dbg_out_stat                          false
% 35.54/4.99  ------ Parsing...
% 35.54/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.54/4.99  
% 35.54/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 35.54/4.99  
% 35.54/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.54/4.99  
% 35.54/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.54/4.99  ------ Proving...
% 35.54/4.99  ------ Problem Properties 
% 35.54/4.99  
% 35.54/4.99  
% 35.54/4.99  clauses                                 40
% 35.54/4.99  conjectures                             8
% 35.54/4.99  EPR                                     6
% 35.54/4.99  Horn                                    40
% 35.54/4.99  unary                                   14
% 35.54/4.99  binary                                  13
% 35.54/4.99  lits                                    86
% 35.54/4.99  lits eq                                 25
% 35.54/4.99  fd_pure                                 0
% 35.54/4.99  fd_pseudo                               0
% 35.54/4.99  fd_cond                                 0
% 35.54/4.99  fd_pseudo_cond                          1
% 35.54/4.99  AC symbols                              0
% 35.54/4.99  
% 35.54/4.99  ------ Schedule dynamic 5 is on 
% 35.54/4.99  
% 35.54/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.54/4.99  
% 35.54/4.99  
% 35.54/4.99  ------ 
% 35.54/4.99  Current options:
% 35.54/4.99  ------ 
% 35.54/4.99  
% 35.54/4.99  ------ Input Options
% 35.54/4.99  
% 35.54/4.99  --out_options                           all
% 35.54/4.99  --tptp_safe_out                         true
% 35.54/4.99  --problem_path                          ""
% 35.54/4.99  --include_path                          ""
% 35.54/4.99  --clausifier                            res/vclausify_rel
% 35.54/4.99  --clausifier_options                    ""
% 35.54/4.99  --stdin                                 false
% 35.54/4.99  --stats_out                             all
% 35.54/4.99  
% 35.54/4.99  ------ General Options
% 35.54/4.99  
% 35.54/4.99  --fof                                   false
% 35.54/4.99  --time_out_real                         305.
% 35.54/4.99  --time_out_virtual                      -1.
% 35.54/4.99  --symbol_type_check                     false
% 35.54/4.99  --clausify_out                          false
% 35.54/4.99  --sig_cnt_out                           false
% 35.54/4.99  --trig_cnt_out                          false
% 35.54/4.99  --trig_cnt_out_tolerance                1.
% 35.54/4.99  --trig_cnt_out_sk_spl                   false
% 35.54/4.99  --abstr_cl_out                          false
% 35.54/4.99  
% 35.54/4.99  ------ Global Options
% 35.54/4.99  
% 35.54/4.99  --schedule                              default
% 35.54/4.99  --add_important_lit                     false
% 35.54/4.99  --prop_solver_per_cl                    1000
% 35.54/4.99  --min_unsat_core                        false
% 35.54/4.99  --soft_assumptions                      false
% 35.54/4.99  --soft_lemma_size                       3
% 35.54/4.99  --prop_impl_unit_size                   0
% 35.54/4.99  --prop_impl_unit                        []
% 35.54/4.99  --share_sel_clauses                     true
% 35.54/4.99  --reset_solvers                         false
% 35.54/4.99  --bc_imp_inh                            [conj_cone]
% 35.54/4.99  --conj_cone_tolerance                   3.
% 35.54/4.99  --extra_neg_conj                        none
% 35.54/4.99  --large_theory_mode                     true
% 35.54/4.99  --prolific_symb_bound                   200
% 35.54/4.99  --lt_threshold                          2000
% 35.54/4.99  --clause_weak_htbl                      true
% 35.54/4.99  --gc_record_bc_elim                     false
% 35.54/4.99  
% 35.54/4.99  ------ Preprocessing Options
% 35.54/4.99  
% 35.54/4.99  --preprocessing_flag                    true
% 35.54/4.99  --time_out_prep_mult                    0.1
% 35.54/4.99  --splitting_mode                        input
% 35.54/4.99  --splitting_grd                         true
% 35.54/4.99  --splitting_cvd                         false
% 35.54/4.99  --splitting_cvd_svl                     false
% 35.54/4.99  --splitting_nvd                         32
% 35.54/4.99  --sub_typing                            true
% 35.54/4.99  --prep_gs_sim                           true
% 35.54/4.99  --prep_unflatten                        true
% 35.54/4.99  --prep_res_sim                          true
% 35.54/4.99  --prep_upred                            true
% 35.54/4.99  --prep_sem_filter                       exhaustive
% 35.54/4.99  --prep_sem_filter_out                   false
% 35.54/4.99  --pred_elim                             true
% 35.54/4.99  --res_sim_input                         true
% 35.54/4.99  --eq_ax_congr_red                       true
% 35.54/4.99  --pure_diseq_elim                       true
% 35.54/4.99  --brand_transform                       false
% 35.54/4.99  --non_eq_to_eq                          false
% 35.54/4.99  --prep_def_merge                        true
% 35.54/4.99  --prep_def_merge_prop_impl              false
% 35.54/4.99  --prep_def_merge_mbd                    true
% 35.54/4.99  --prep_def_merge_tr_red                 false
% 35.54/4.99  --prep_def_merge_tr_cl                  false
% 35.54/4.99  --smt_preprocessing                     true
% 35.54/4.99  --smt_ac_axioms                         fast
% 35.54/4.99  --preprocessed_out                      false
% 35.54/4.99  --preprocessed_stats                    false
% 35.54/4.99  
% 35.54/4.99  ------ Abstraction refinement Options
% 35.54/4.99  
% 35.54/4.99  --abstr_ref                             []
% 35.54/4.99  --abstr_ref_prep                        false
% 35.54/4.99  --abstr_ref_until_sat                   false
% 35.54/4.99  --abstr_ref_sig_restrict                funpre
% 35.54/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.54/4.99  --abstr_ref_under                       []
% 35.54/4.99  
% 35.54/4.99  ------ SAT Options
% 35.54/4.99  
% 35.54/4.99  --sat_mode                              false
% 35.54/4.99  --sat_fm_restart_options                ""
% 35.54/4.99  --sat_gr_def                            false
% 35.54/4.99  --sat_epr_types                         true
% 35.54/4.99  --sat_non_cyclic_types                  false
% 35.54/4.99  --sat_finite_models                     false
% 35.54/4.99  --sat_fm_lemmas                         false
% 35.54/4.99  --sat_fm_prep                           false
% 35.54/4.99  --sat_fm_uc_incr                        true
% 35.54/4.99  --sat_out_model                         small
% 35.54/4.99  --sat_out_clauses                       false
% 35.54/4.99  
% 35.54/4.99  ------ QBF Options
% 35.54/4.99  
% 35.54/4.99  --qbf_mode                              false
% 35.54/4.99  --qbf_elim_univ                         false
% 35.54/4.99  --qbf_dom_inst                          none
% 35.54/4.99  --qbf_dom_pre_inst                      false
% 35.54/4.99  --qbf_sk_in                             false
% 35.54/4.99  --qbf_pred_elim                         true
% 35.54/4.99  --qbf_split                             512
% 35.54/4.99  
% 35.54/4.99  ------ BMC1 Options
% 35.54/4.99  
% 35.54/4.99  --bmc1_incremental                      false
% 35.54/4.99  --bmc1_axioms                           reachable_all
% 35.54/4.99  --bmc1_min_bound                        0
% 35.54/4.99  --bmc1_max_bound                        -1
% 35.54/4.99  --bmc1_max_bound_default                -1
% 35.54/4.99  --bmc1_symbol_reachability              true
% 35.54/4.99  --bmc1_property_lemmas                  false
% 35.54/4.99  --bmc1_k_induction                      false
% 35.54/4.99  --bmc1_non_equiv_states                 false
% 35.54/4.99  --bmc1_deadlock                         false
% 35.54/4.99  --bmc1_ucm                              false
% 35.54/4.99  --bmc1_add_unsat_core                   none
% 35.54/4.99  --bmc1_unsat_core_children              false
% 35.54/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.54/4.99  --bmc1_out_stat                         full
% 35.54/4.99  --bmc1_ground_init                      false
% 35.54/4.99  --bmc1_pre_inst_next_state              false
% 35.54/4.99  --bmc1_pre_inst_state                   false
% 35.54/4.99  --bmc1_pre_inst_reach_state             false
% 35.54/4.99  --bmc1_out_unsat_core                   false
% 35.54/4.99  --bmc1_aig_witness_out                  false
% 35.54/4.99  --bmc1_verbose                          false
% 35.54/4.99  --bmc1_dump_clauses_tptp                false
% 35.54/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.54/4.99  --bmc1_dump_file                        -
% 35.54/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.54/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.54/4.99  --bmc1_ucm_extend_mode                  1
% 35.54/4.99  --bmc1_ucm_init_mode                    2
% 35.54/4.99  --bmc1_ucm_cone_mode                    none
% 35.54/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.54/4.99  --bmc1_ucm_relax_model                  4
% 35.54/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.54/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.54/4.99  --bmc1_ucm_layered_model                none
% 35.54/4.99  --bmc1_ucm_max_lemma_size               10
% 35.54/4.99  
% 35.54/4.99  ------ AIG Options
% 35.54/4.99  
% 35.54/4.99  --aig_mode                              false
% 35.54/4.99  
% 35.54/4.99  ------ Instantiation Options
% 35.54/4.99  
% 35.54/4.99  --instantiation_flag                    true
% 35.54/4.99  --inst_sos_flag                         true
% 35.54/4.99  --inst_sos_phase                        true
% 35.54/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.54/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.54/4.99  --inst_lit_sel_side                     none
% 35.54/4.99  --inst_solver_per_active                1400
% 35.54/4.99  --inst_solver_calls_frac                1.
% 35.54/4.99  --inst_passive_queue_type               priority_queues
% 35.54/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.54/4.99  --inst_passive_queues_freq              [25;2]
% 35.54/4.99  --inst_dismatching                      true
% 35.54/4.99  --inst_eager_unprocessed_to_passive     true
% 35.54/4.99  --inst_prop_sim_given                   true
% 35.54/4.99  --inst_prop_sim_new                     false
% 35.54/4.99  --inst_subs_new                         false
% 35.54/4.99  --inst_eq_res_simp                      false
% 35.54/4.99  --inst_subs_given                       false
% 35.54/4.99  --inst_orphan_elimination               true
% 35.54/4.99  --inst_learning_loop_flag               true
% 35.54/4.99  --inst_learning_start                   3000
% 35.54/4.99  --inst_learning_factor                  2
% 35.54/4.99  --inst_start_prop_sim_after_learn       3
% 35.54/4.99  --inst_sel_renew                        solver
% 35.54/4.99  --inst_lit_activity_flag                true
% 35.54/4.99  --inst_restr_to_given                   false
% 35.54/4.99  --inst_activity_threshold               500
% 35.54/4.99  --inst_out_proof                        true
% 35.54/4.99  
% 35.54/4.99  ------ Resolution Options
% 35.54/4.99  
% 35.54/4.99  --resolution_flag                       false
% 35.54/4.99  --res_lit_sel                           adaptive
% 35.54/4.99  --res_lit_sel_side                      none
% 35.54/4.99  --res_ordering                          kbo
% 35.54/4.99  --res_to_prop_solver                    active
% 35.54/4.99  --res_prop_simpl_new                    false
% 35.54/4.99  --res_prop_simpl_given                  true
% 35.54/4.99  --res_passive_queue_type                priority_queues
% 35.54/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.54/4.99  --res_passive_queues_freq               [15;5]
% 35.54/4.99  --res_forward_subs                      full
% 35.54/4.99  --res_backward_subs                     full
% 35.54/4.99  --res_forward_subs_resolution           true
% 35.54/4.99  --res_backward_subs_resolution          true
% 35.54/4.99  --res_orphan_elimination                true
% 35.54/4.99  --res_time_limit                        2.
% 35.54/4.99  --res_out_proof                         true
% 35.54/4.99  
% 35.54/4.99  ------ Superposition Options
% 35.54/4.99  
% 35.54/4.99  --superposition_flag                    true
% 35.54/4.99  --sup_passive_queue_type                priority_queues
% 35.54/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.54/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.54/4.99  --demod_completeness_check              fast
% 35.54/4.99  --demod_use_ground                      true
% 35.54/4.99  --sup_to_prop_solver                    passive
% 35.54/4.99  --sup_prop_simpl_new                    true
% 35.54/4.99  --sup_prop_simpl_given                  true
% 35.54/4.99  --sup_fun_splitting                     true
% 35.54/4.99  --sup_smt_interval                      50000
% 35.54/4.99  
% 35.54/4.99  ------ Superposition Simplification Setup
% 35.54/4.99  
% 35.54/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.54/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.54/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.54/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.54/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.54/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.54/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.54/4.99  --sup_immed_triv                        [TrivRules]
% 35.54/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.54/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.54/4.99  --sup_immed_bw_main                     []
% 35.54/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.54/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.54/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.54/4.99  --sup_input_bw                          []
% 35.54/4.99  
% 35.54/4.99  ------ Combination Options
% 35.54/4.99  
% 35.54/4.99  --comb_res_mult                         3
% 35.54/4.99  --comb_sup_mult                         2
% 35.54/4.99  --comb_inst_mult                        10
% 35.54/4.99  
% 35.54/4.99  ------ Debug Options
% 35.54/4.99  
% 35.54/4.99  --dbg_backtrace                         false
% 35.54/4.99  --dbg_dump_prop_clauses                 false
% 35.54/4.99  --dbg_dump_prop_clauses_file            -
% 35.54/4.99  --dbg_out_stat                          false
% 35.54/4.99  
% 35.54/4.99  
% 35.54/4.99  
% 35.54/4.99  
% 35.54/4.99  ------ Proving...
% 35.54/4.99  
% 35.54/4.99  
% 35.54/4.99  % SZS status Theorem for theBenchmark.p
% 35.54/4.99  
% 35.54/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.54/4.99  
% 35.54/4.99  fof(f19,axiom,(
% 35.54/4.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f53,plain,(
% 35.54/4.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.54/4.99    inference(ennf_transformation,[],[f19])).
% 35.54/4.99  
% 35.54/4.99  fof(f54,plain,(
% 35.54/4.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(flattening,[],[f53])).
% 35.54/4.99  
% 35.54/4.99  fof(f98,plain,(
% 35.54/4.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f54])).
% 35.54/4.99  
% 35.54/4.99  fof(f29,conjecture,(
% 35.54/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f30,negated_conjecture,(
% 35.54/4.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.54/4.99    inference(negated_conjecture,[],[f29])).
% 35.54/4.99  
% 35.54/4.99  fof(f31,plain,(
% 35.54/4.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.54/4.99    inference(pure_predicate_removal,[],[f30])).
% 35.54/4.99  
% 35.54/4.99  fof(f67,plain,(
% 35.54/4.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 35.54/4.99    inference(ennf_transformation,[],[f31])).
% 35.54/4.99  
% 35.54/4.99  fof(f68,plain,(
% 35.54/4.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 35.54/4.99    inference(flattening,[],[f67])).
% 35.54/4.99  
% 35.54/4.99  fof(f73,plain,(
% 35.54/4.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 35.54/4.99    introduced(choice_axiom,[])).
% 35.54/4.99  
% 35.54/4.99  fof(f72,plain,(
% 35.54/4.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 35.54/4.99    introduced(choice_axiom,[])).
% 35.54/4.99  
% 35.54/4.99  fof(f74,plain,(
% 35.54/4.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 35.54/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f68,f73,f72])).
% 35.54/4.99  
% 35.54/4.99  fof(f118,plain,(
% 35.54/4.99    v2_funct_1(sK2)),
% 35.54/4.99    inference(cnf_transformation,[],[f74])).
% 35.54/4.99  
% 35.54/4.99  fof(f112,plain,(
% 35.54/4.99    v1_funct_1(sK2)),
% 35.54/4.99    inference(cnf_transformation,[],[f74])).
% 35.54/4.99  
% 35.54/4.99  fof(f113,plain,(
% 35.54/4.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 35.54/4.99    inference(cnf_transformation,[],[f74])).
% 35.54/4.99  
% 35.54/4.99  fof(f2,axiom,(
% 35.54/4.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f34,plain,(
% 35.54/4.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(ennf_transformation,[],[f2])).
% 35.54/4.99  
% 35.54/4.99  fof(f78,plain,(
% 35.54/4.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f34])).
% 35.54/4.99  
% 35.54/4.99  fof(f4,axiom,(
% 35.54/4.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f80,plain,(
% 35.54/4.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 35.54/4.99    inference(cnf_transformation,[],[f4])).
% 35.54/4.99  
% 35.54/4.99  fof(f15,axiom,(
% 35.54/4.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f45,plain,(
% 35.54/4.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.54/4.99    inference(ennf_transformation,[],[f15])).
% 35.54/4.99  
% 35.54/4.99  fof(f46,plain,(
% 35.54/4.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(flattening,[],[f45])).
% 35.54/4.99  
% 35.54/4.99  fof(f92,plain,(
% 35.54/4.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f46])).
% 35.54/4.99  
% 35.54/4.99  fof(f28,axiom,(
% 35.54/4.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f32,plain,(
% 35.54/4.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 35.54/4.99    inference(pure_predicate_removal,[],[f28])).
% 35.54/4.99  
% 35.54/4.99  fof(f65,plain,(
% 35.54/4.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.54/4.99    inference(ennf_transformation,[],[f32])).
% 35.54/4.99  
% 35.54/4.99  fof(f66,plain,(
% 35.54/4.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(flattening,[],[f65])).
% 35.54/4.99  
% 35.54/4.99  fof(f111,plain,(
% 35.54/4.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f66])).
% 35.54/4.99  
% 35.54/4.99  fof(f97,plain,(
% 35.54/4.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f54])).
% 35.54/4.99  
% 35.54/4.99  fof(f3,axiom,(
% 35.54/4.99    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f35,plain,(
% 35.54/4.99    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(ennf_transformation,[],[f3])).
% 35.54/4.99  
% 35.54/4.99  fof(f79,plain,(
% 35.54/4.99    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f35])).
% 35.54/4.99  
% 35.54/4.99  fof(f16,axiom,(
% 35.54/4.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f47,plain,(
% 35.54/4.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.54/4.99    inference(ennf_transformation,[],[f16])).
% 35.54/4.99  
% 35.54/4.99  fof(f48,plain,(
% 35.54/4.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(flattening,[],[f47])).
% 35.54/4.99  
% 35.54/4.99  fof(f94,plain,(
% 35.54/4.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f48])).
% 35.54/4.99  
% 35.54/4.99  fof(f22,axiom,(
% 35.54/4.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f58,plain,(
% 35.54/4.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.54/4.99    inference(ennf_transformation,[],[f22])).
% 35.54/4.99  
% 35.54/4.99  fof(f102,plain,(
% 35.54/4.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.54/4.99    inference(cnf_transformation,[],[f58])).
% 35.54/4.99  
% 35.54/4.99  fof(f116,plain,(
% 35.54/4.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 35.54/4.99    inference(cnf_transformation,[],[f74])).
% 35.54/4.99  
% 35.54/4.99  fof(f115,plain,(
% 35.54/4.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 35.54/4.99    inference(cnf_transformation,[],[f74])).
% 35.54/4.99  
% 35.54/4.99  fof(f9,axiom,(
% 35.54/4.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f41,plain,(
% 35.54/4.99    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(ennf_transformation,[],[f9])).
% 35.54/4.99  
% 35.54/4.99  fof(f85,plain,(
% 35.54/4.99    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f41])).
% 35.54/4.99  
% 35.54/4.99  fof(f26,axiom,(
% 35.54/4.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f63,plain,(
% 35.54/4.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.54/4.99    inference(ennf_transformation,[],[f26])).
% 35.54/4.99  
% 35.54/4.99  fof(f64,plain,(
% 35.54/4.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.54/4.99    inference(flattening,[],[f63])).
% 35.54/4.99  
% 35.54/4.99  fof(f108,plain,(
% 35.54/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f64])).
% 35.54/4.99  
% 35.54/4.99  fof(f114,plain,(
% 35.54/4.99    v1_funct_1(sK3)),
% 35.54/4.99    inference(cnf_transformation,[],[f74])).
% 35.54/4.99  
% 35.54/4.99  fof(f23,axiom,(
% 35.54/4.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f59,plain,(
% 35.54/4.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 35.54/4.99    inference(ennf_transformation,[],[f23])).
% 35.54/4.99  
% 35.54/4.99  fof(f60,plain,(
% 35.54/4.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.54/4.99    inference(flattening,[],[f59])).
% 35.54/4.99  
% 35.54/4.99  fof(f71,plain,(
% 35.54/4.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.54/4.99    inference(nnf_transformation,[],[f60])).
% 35.54/4.99  
% 35.54/4.99  fof(f103,plain,(
% 35.54/4.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.54/4.99    inference(cnf_transformation,[],[f71])).
% 35.54/4.99  
% 35.54/4.99  fof(f117,plain,(
% 35.54/4.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 35.54/4.99    inference(cnf_transformation,[],[f74])).
% 35.54/4.99  
% 35.54/4.99  fof(f24,axiom,(
% 35.54/4.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f105,plain,(
% 35.54/4.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.54/4.99    inference(cnf_transformation,[],[f24])).
% 35.54/4.99  
% 35.54/4.99  fof(f27,axiom,(
% 35.54/4.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f109,plain,(
% 35.54/4.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f27])).
% 35.54/4.99  
% 35.54/4.99  fof(f129,plain,(
% 35.54/4.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.54/4.99    inference(definition_unfolding,[],[f105,f109])).
% 35.54/4.99  
% 35.54/4.99  fof(f25,axiom,(
% 35.54/4.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f61,plain,(
% 35.54/4.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.54/4.99    inference(ennf_transformation,[],[f25])).
% 35.54/4.99  
% 35.54/4.99  fof(f62,plain,(
% 35.54/4.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.54/4.99    inference(flattening,[],[f61])).
% 35.54/4.99  
% 35.54/4.99  fof(f107,plain,(
% 35.54/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f62])).
% 35.54/4.99  
% 35.54/4.99  fof(f12,axiom,(
% 35.54/4.99    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f89,plain,(
% 35.54/4.99    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f12])).
% 35.54/4.99  
% 35.54/4.99  fof(f124,plain,(
% 35.54/4.99    ( ! [X0] : (k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 35.54/4.99    inference(definition_unfolding,[],[f89,f109,f109])).
% 35.54/4.99  
% 35.54/4.99  fof(f8,axiom,(
% 35.54/4.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f40,plain,(
% 35.54/4.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(ennf_transformation,[],[f8])).
% 35.54/4.99  
% 35.54/4.99  fof(f84,plain,(
% 35.54/4.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f40])).
% 35.54/4.99  
% 35.54/4.99  fof(f11,axiom,(
% 35.54/4.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f88,plain,(
% 35.54/4.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 35.54/4.99    inference(cnf_transformation,[],[f11])).
% 35.54/4.99  
% 35.54/4.99  fof(f122,plain,(
% 35.54/4.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 35.54/4.99    inference(definition_unfolding,[],[f88,f109])).
% 35.54/4.99  
% 35.54/4.99  fof(f18,axiom,(
% 35.54/4.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f51,plain,(
% 35.54/4.99    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 35.54/4.99    inference(ennf_transformation,[],[f18])).
% 35.54/4.99  
% 35.54/4.99  fof(f52,plain,(
% 35.54/4.99    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 35.54/4.99    inference(flattening,[],[f51])).
% 35.54/4.99  
% 35.54/4.99  fof(f96,plain,(
% 35.54/4.99    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f52])).
% 35.54/4.99  
% 35.54/4.99  fof(f5,axiom,(
% 35.54/4.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f36,plain,(
% 35.54/4.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(ennf_transformation,[],[f5])).
% 35.54/4.99  
% 35.54/4.99  fof(f81,plain,(
% 35.54/4.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f36])).
% 35.54/4.99  
% 35.54/4.99  fof(f1,axiom,(
% 35.54/4.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f69,plain,(
% 35.54/4.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.54/4.99    inference(nnf_transformation,[],[f1])).
% 35.54/4.99  
% 35.54/4.99  fof(f70,plain,(
% 35.54/4.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.54/4.99    inference(flattening,[],[f69])).
% 35.54/4.99  
% 35.54/4.99  fof(f76,plain,(
% 35.54/4.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 35.54/4.99    inference(cnf_transformation,[],[f70])).
% 35.54/4.99  
% 35.54/4.99  fof(f130,plain,(
% 35.54/4.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.54/4.99    inference(equality_resolution,[],[f76])).
% 35.54/4.99  
% 35.54/4.99  fof(f21,axiom,(
% 35.54/4.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f33,plain,(
% 35.54/4.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 35.54/4.99    inference(pure_predicate_removal,[],[f21])).
% 35.54/4.99  
% 35.54/4.99  fof(f57,plain,(
% 35.54/4.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.54/4.99    inference(ennf_transformation,[],[f33])).
% 35.54/4.99  
% 35.54/4.99  fof(f101,plain,(
% 35.54/4.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.54/4.99    inference(cnf_transformation,[],[f57])).
% 35.54/4.99  
% 35.54/4.99  fof(f7,axiom,(
% 35.54/4.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f38,plain,(
% 35.54/4.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 35.54/4.99    inference(ennf_transformation,[],[f7])).
% 35.54/4.99  
% 35.54/4.99  fof(f39,plain,(
% 35.54/4.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 35.54/4.99    inference(flattening,[],[f38])).
% 35.54/4.99  
% 35.54/4.99  fof(f83,plain,(
% 35.54/4.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f39])).
% 35.54/4.99  
% 35.54/4.99  fof(f6,axiom,(
% 35.54/4.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f37,plain,(
% 35.54/4.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 35.54/4.99    inference(ennf_transformation,[],[f6])).
% 35.54/4.99  
% 35.54/4.99  fof(f82,plain,(
% 35.54/4.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f37])).
% 35.54/4.99  
% 35.54/4.99  fof(f13,axiom,(
% 35.54/4.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f43,plain,(
% 35.54/4.99    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 35.54/4.99    inference(ennf_transformation,[],[f13])).
% 35.54/4.99  
% 35.54/4.99  fof(f90,plain,(
% 35.54/4.99    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f43])).
% 35.54/4.99  
% 35.54/4.99  fof(f125,plain,(
% 35.54/4.99    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(definition_unfolding,[],[f90,f109])).
% 35.54/4.99  
% 35.54/4.99  fof(f14,axiom,(
% 35.54/4.99    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f44,plain,(
% 35.54/4.99    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 35.54/4.99    inference(ennf_transformation,[],[f14])).
% 35.54/4.99  
% 35.54/4.99  fof(f91,plain,(
% 35.54/4.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f44])).
% 35.54/4.99  
% 35.54/4.99  fof(f126,plain,(
% 35.54/4.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 35.54/4.99    inference(definition_unfolding,[],[f91,f109])).
% 35.54/4.99  
% 35.54/4.99  fof(f10,axiom,(
% 35.54/4.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f42,plain,(
% 35.54/4.99    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(ennf_transformation,[],[f10])).
% 35.54/4.99  
% 35.54/4.99  fof(f86,plain,(
% 35.54/4.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f42])).
% 35.54/4.99  
% 35.54/4.99  fof(f20,axiom,(
% 35.54/4.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 35.54/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.54/4.99  
% 35.54/4.99  fof(f55,plain,(
% 35.54/4.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.54/4.99    inference(ennf_transformation,[],[f20])).
% 35.54/4.99  
% 35.54/4.99  fof(f56,plain,(
% 35.54/4.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.54/4.99    inference(flattening,[],[f55])).
% 35.54/4.99  
% 35.54/4.99  fof(f99,plain,(
% 35.54/4.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f56])).
% 35.54/4.99  
% 35.54/4.99  fof(f128,plain,(
% 35.54/4.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(definition_unfolding,[],[f99,f109])).
% 35.54/4.99  
% 35.54/4.99  fof(f100,plain,(
% 35.54/4.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(cnf_transformation,[],[f56])).
% 35.54/4.99  
% 35.54/4.99  fof(f127,plain,(
% 35.54/4.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.54/4.99    inference(definition_unfolding,[],[f100,f109])).
% 35.54/4.99  
% 35.54/4.99  fof(f121,plain,(
% 35.54/4.99    k2_funct_1(sK2) != sK3),
% 35.54/4.99    inference(cnf_transformation,[],[f74])).
% 35.54/4.99  
% 35.54/4.99  cnf(c_22,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v2_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f98]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_39,negated_conjecture,
% 35.54/4.99      ( v2_funct_1(sK2) ),
% 35.54/4.99      inference(cnf_transformation,[],[f118]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_520,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 35.54/4.99      | sK2 != X0 ),
% 35.54/4.99      inference(resolution_lifted,[status(thm)],[c_22,c_39]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_521,plain,
% 35.54/4.99      ( ~ v1_funct_1(sK2)
% 35.54/4.99      | ~ v1_relat_1(sK2)
% 35.54/4.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 35.54/4.99      inference(unflattening,[status(thm)],[c_520]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_45,negated_conjecture,
% 35.54/4.99      ( v1_funct_1(sK2) ),
% 35.54/4.99      inference(cnf_transformation,[],[f112]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_523,plain,
% 35.54/4.99      ( ~ v1_relat_1(sK2)
% 35.54/4.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_521,c_45]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1394,plain,
% 35.54/4.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_44,negated_conjecture,
% 35.54/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 35.54/4.99      inference(cnf_transformation,[],[f113]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3,plain,
% 35.54/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.54/4.99      | ~ v1_relat_1(X1)
% 35.54/4.99      | v1_relat_1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f78]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1490,plain,
% 35.54/4.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | v1_relat_1(sK2) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_3]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1577,plain,
% 35.54/4.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.54/4.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 35.54/4.99      | v1_relat_1(sK2) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_1490]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1695,plain,
% 35.54/4.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.54/4.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 35.54/4.99      | v1_relat_1(sK2) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_1577]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_5,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 35.54/4.99      inference(cnf_transformation,[],[f80]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1730,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_5]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1841,plain,
% 35.54/4.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_1394,c_45,c_44,c_521,c_1695,c_1730]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_17,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v2_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f92]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_552,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 35.54/4.99      | sK2 != X0 ),
% 35.54/4.99      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_553,plain,
% 35.54/4.99      ( ~ v1_funct_1(sK2)
% 35.54/4.99      | ~ v1_relat_1(sK2)
% 35.54/4.99      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 35.54/4.99      inference(unflattening,[status(thm)],[c_552]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_555,plain,
% 35.54/4.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_553,c_45]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1392,plain,
% 35.54/4.99      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1775,plain,
% 35.54/4.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_1392,c_45,c_44,c_553,c_1695,c_1730]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1843,plain,
% 35.54/4.99      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_1841,c_1775]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_34,plain,
% 35.54/4.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 35.54/4.99      | ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f111]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1404,plain,
% 35.54/4.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 35.54/4.99      | v1_funct_1(X0) != iProver_top
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2652,plain,
% 35.54/4.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 35.54/4.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1843,c_1404]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_23,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v2_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f97]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_506,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 35.54/4.99      | sK2 != X0 ),
% 35.54/4.99      inference(resolution_lifted,[status(thm)],[c_23,c_39]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_507,plain,
% 35.54/4.99      ( ~ v1_funct_1(sK2)
% 35.54/4.99      | ~ v1_relat_1(sK2)
% 35.54/4.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 35.54/4.99      inference(unflattening,[status(thm)],[c_506]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_509,plain,
% 35.54/4.99      ( ~ v1_relat_1(sK2)
% 35.54/4.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_507,c_45]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1395,plain,
% 35.54/4.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1964,plain,
% 35.54/4.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_1395,c_45,c_44,c_507,c_1695,c_1730]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1966,plain,
% 35.54/4.99      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_1964,c_1775]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2654,plain,
% 35.54/4.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 35.54/4.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_2652,c_1966]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_46,plain,
% 35.54/4.99      ( v1_funct_1(sK2) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_47,plain,
% 35.54/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1696,plain,
% 35.54/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.54/4.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 35.54/4.99      | v1_relat_1(sK2) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_1695]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1731,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_1730]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_4,plain,
% 35.54/4.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 35.54/4.99      inference(cnf_transformation,[],[f79]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2039,plain,
% 35.54/4.99      ( v1_relat_1(k4_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2047,plain,
% 35.54/4.99      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_2039]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_18,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | v1_funct_1(k2_funct_1(X0))
% 35.54/4.99      | ~ v1_relat_1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f94]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1411,plain,
% 35.54/4.99      ( v1_funct_1(X0) != iProver_top
% 35.54/4.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3584,plain,
% 35.54/4.99      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 35.54/4.99      | v1_funct_1(sK2) != iProver_top
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1775,c_1411]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10491,plain,
% 35.54/4.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_2654,c_46,c_47,c_1696,c_1731,c_2047,c_3584]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1401,plain,
% 35.54/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_27,plain,
% 35.54/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.54/4.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f102]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1409,plain,
% 35.54/4.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 35.54/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2753,plain,
% 35.54/4.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1401,c_1409]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_41,negated_conjecture,
% 35.54/4.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 35.54/4.99      inference(cnf_transformation,[],[f116]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2754,plain,
% 35.54/4.99      ( k2_relat_1(sK2) = sK1 ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_2753,c_41]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1421,plain,
% 35.54/4.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.54/4.99      | v1_relat_1(X1) != iProver_top
% 35.54/4.99      | v1_relat_1(X0) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3703,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 35.54/4.99      | v1_relat_1(sK2) = iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1401,c_1421]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3790,plain,
% 35.54/4.99      ( v1_relat_1(sK2) = iProver_top ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_3703,c_47,c_1696,c_1731]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_42,negated_conjecture,
% 35.54/4.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 35.54/4.99      inference(cnf_transformation,[],[f115]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1403,plain,
% 35.54/4.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3702,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 35.54/4.99      | v1_relat_1(sK3) = iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1403,c_1421]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_49,plain,
% 35.54/4.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1679,plain,
% 35.54/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.54/4.99      | v1_relat_1(X0)
% 35.54/4.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_3]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1894,plain,
% 35.54/4.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.54/4.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 35.54/4.99      | v1_relat_1(sK3) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_1679]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1895,plain,
% 35.54/4.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.54/4.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 35.54/4.99      | v1_relat_1(sK3) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2118,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_5]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2119,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3714,plain,
% 35.54/4.99      ( v1_relat_1(sK3) = iProver_top ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_3702,c_49,c_1895,c_2119]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10,plain,
% 35.54/4.99      ( ~ v1_relat_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X1)
% 35.54/4.99      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 35.54/4.99      inference(cnf_transformation,[],[f85]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1415,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 35.54/4.99      | v1_relat_1(X1) != iProver_top
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_4251,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3714,c_1415]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_7145,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_4251]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_33,plain,
% 35.54/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.54/4.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.54/4.99      | ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v1_funct_1(X3)
% 35.54/4.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f108]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1405,plain,
% 35.54/4.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 35.54/4.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 35.54/4.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.54/4.99      | v1_funct_1(X5) != iProver_top
% 35.54/4.99      | v1_funct_1(X4) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_5455,plain,
% 35.54/4.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.54/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.54/4.99      | v1_funct_1(X2) != iProver_top
% 35.54/4.99      | v1_funct_1(sK3) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1403,c_1405]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_43,negated_conjecture,
% 35.54/4.99      ( v1_funct_1(sK3) ),
% 35.54/4.99      inference(cnf_transformation,[],[f114]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_48,plain,
% 35.54/4.99      ( v1_funct_1(sK3) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_5746,plain,
% 35.54/4.99      ( v1_funct_1(X2) != iProver_top
% 35.54/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.54/4.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_5455,c_48]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_5747,plain,
% 35.54/4.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.54/4.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.54/4.99      | v1_funct_1(X2) != iProver_top ),
% 35.54/4.99      inference(renaming,[status(thm)],[c_5746]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_5756,plain,
% 35.54/4.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 35.54/4.99      | v1_funct_1(sK2) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1401,c_5747]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_29,plain,
% 35.54/4.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 35.54/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.54/4.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.54/4.99      | X3 = X2 ),
% 35.54/4.99      inference(cnf_transformation,[],[f103]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_40,negated_conjecture,
% 35.54/4.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 35.54/4.99      inference(cnf_transformation,[],[f117]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_461,plain,
% 35.54/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.54/4.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.54/4.99      | X3 = X0
% 35.54/4.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 35.54/4.99      | k6_partfun1(sK0) != X3
% 35.54/4.99      | sK0 != X2
% 35.54/4.99      | sK0 != X1 ),
% 35.54/4.99      inference(resolution_lifted,[status(thm)],[c_29,c_40]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_462,plain,
% 35.54/4.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.54/4.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.54/4.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.54/4.99      inference(unflattening,[status(thm)],[c_461]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_30,plain,
% 35.54/4.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 35.54/4.99      inference(cnf_transformation,[],[f129]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_66,plain,
% 35.54/4.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_30]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_464,plain,
% 35.54/4.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.54/4.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_462,c_66]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1398,plain,
% 35.54/4.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.54/4.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_31,plain,
% 35.54/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.54/4.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.54/4.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 35.54/4.99      | ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v1_funct_1(X3) ),
% 35.54/4.99      inference(cnf_transformation,[],[f107]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1482,plain,
% 35.54/4.99      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.54/4.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.54/4.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.54/4.99      | ~ v1_funct_1(sK3)
% 35.54/4.99      | ~ v1_funct_1(sK2) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_31]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2152,plain,
% 35.54/4.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_1398,c_45,c_44,c_43,c_42,c_66,c_462,c_1482]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_5759,plain,
% 35.54/4.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 35.54/4.99      | v1_funct_1(sK2) != iProver_top ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_5756,c_2152]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6647,plain,
% 35.54/4.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_5759,c_46]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_7149,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_7145,c_6647]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_14,plain,
% 35.54/4.99      ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f124]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_7150,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_7149,c_14]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_9,plain,
% 35.54/4.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X1) ),
% 35.54/4.99      inference(cnf_transformation,[],[f84]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1416,plain,
% 35.54/4.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 35.54/4.99      | v1_relat_1(X0) != iProver_top
% 35.54/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_8823,plain,
% 35.54/4.99      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2))) = iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_7150,c_1416]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_8824,plain,
% 35.54/4.99      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_8823,c_1843]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_12,plain,
% 35.54/4.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 35.54/4.99      inference(cnf_transformation,[],[f122]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_8825,plain,
% 35.54/4.99      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_8824,c_12]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2015,plain,
% 35.54/4.99      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2027,plain,
% 35.54/4.99      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 35.54/4.99      | v1_relat_1(sK3) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_9736,plain,
% 35.54/4.99      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_8825,c_47,c_49,c_1696,c_1731,c_1895,c_2027,c_2047,
% 35.54/4.99                 c_2119]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_21,plain,
% 35.54/4.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 35.54/4.99      | ~ v1_funct_1(X1)
% 35.54/4.99      | ~ v2_funct_1(X1)
% 35.54/4.99      | ~ v1_relat_1(X1)
% 35.54/4.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 35.54/4.99      inference(cnf_transformation,[],[f96]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_566,plain,
% 35.54/4.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 35.54/4.99      | ~ v1_funct_1(X1)
% 35.54/4.99      | ~ v1_relat_1(X1)
% 35.54/4.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 35.54/4.99      | sK2 != X1 ),
% 35.54/4.99      inference(resolution_lifted,[status(thm)],[c_21,c_39]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_567,plain,
% 35.54/4.99      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 35.54/4.99      | ~ v1_funct_1(sK2)
% 35.54/4.99      | ~ v1_relat_1(sK2)
% 35.54/4.99      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 35.54/4.99      inference(unflattening,[status(thm)],[c_566]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_571,plain,
% 35.54/4.99      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 35.54/4.99      | ~ v1_relat_1(sK2)
% 35.54/4.99      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_567,c_45]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1391,plain,
% 35.54/4.99      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 35.54/4.99      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_9741,plain,
% 35.54/4.99      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_9736,c_1391]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6,plain,
% 35.54/4.99      ( ~ v1_relat_1(X0)
% 35.54/4.99      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f81]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1418,plain,
% 35.54/4.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3795,plain,
% 35.54/4.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_1418]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3799,plain,
% 35.54/4.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_3795,c_2754]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1,plain,
% 35.54/4.99      ( r1_tarski(X0,X0) ),
% 35.54/4.99      inference(cnf_transformation,[],[f130]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1422,plain,
% 35.54/4.99      ( r1_tarski(X0,X0) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1772,plain,
% 35.54/4.99      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1422,c_1391]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2422,plain,
% 35.54/4.99      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_1772,c_47,c_1696,c_1731]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3898,plain,
% 35.54/4.99      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_3799,c_2422]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_26,plain,
% 35.54/4.99      ( v4_relat_1(X0,X1)
% 35.54/4.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 35.54/4.99      inference(cnf_transformation,[],[f101]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_8,plain,
% 35.54/4.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 35.54/4.99      inference(cnf_transformation,[],[f83]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_441,plain,
% 35.54/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k7_relat_1(X0,X1) = X0 ),
% 35.54/4.99      inference(resolution,[status(thm)],[c_26,c_8]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1399,plain,
% 35.54/4.99      ( k7_relat_1(X0,X1) = X0
% 35.54/4.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2156,plain,
% 35.54/4.99      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1401,c_1399]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2419,plain,
% 35.54/4.99      ( k7_relat_1(sK2,sK0) = sK2 ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_2156,c_47,c_1696,c_1731]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_7,plain,
% 35.54/4.99      ( ~ v1_relat_1(X0)
% 35.54/4.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 35.54/4.99      inference(cnf_transformation,[],[f82]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1417,plain,
% 35.54/4.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3794,plain,
% 35.54/4.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_1417]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_4621,plain,
% 35.54/4.99      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_2419,c_3794]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_4625,plain,
% 35.54/4.99      ( k9_relat_1(sK2,sK0) = sK1 ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_4621,c_2754]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_9742,plain,
% 35.54/4.99      ( k1_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_9741,c_3898,c_4625]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_9836,plain,
% 35.54/4.99      ( k1_relat_1(sK2) = sK0 ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_9742,c_47,c_1696,c_1731]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10495,plain,
% 35.54/4.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.54/4.99      inference(light_normalisation,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_10491,c_2754,c_9836]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10497,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10495,c_1421]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10677,plain,
% 35.54/4.99      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_10497,c_47,c_1696,c_1731,c_2047]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1420,plain,
% 35.54/4.99      ( v1_relat_1(X0) != iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_15,plain,
% 35.54/4.99      ( ~ v1_relat_1(X0)
% 35.54/4.99      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 35.54/4.99      inference(cnf_transformation,[],[f125]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1413,plain,
% 35.54/4.99      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2516,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(X0),k6_partfun1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1420,c_1413]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10686,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(k2_relat_1(k4_relat_1(k4_relat_1(sK2))))) = k4_relat_1(k4_relat_1(sK2)) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10677,c_2516]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1419,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1408,plain,
% 35.54/4.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3700,plain,
% 35.54/4.99      ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
% 35.54/4.99      | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1408,c_1421]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6910,plain,
% 35.54/4.99      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1419,c_3700]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10689,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(sK2)))
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10677,c_1415]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_22991,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k4_relat_1(k6_partfun1(X0))) = k4_relat_1(k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2))) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_6910,c_10689]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_16,plain,
% 35.54/4.99      ( ~ v1_relat_1(X0)
% 35.54/4.99      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 35.54/4.99      inference(cnf_transformation,[],[f126]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1412,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0)
% 35.54/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2642,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(X1)) = k7_relat_1(k4_relat_1(X1),X0)
% 35.54/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1420,c_1412]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_8706,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k7_relat_1(k4_relat_1(sK2),X0) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_2642]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_23007,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(X0)) = k4_relat_1(k7_relat_1(k4_relat_1(sK2),X0)) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_22991,c_14,c_8706]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_112082,plain,
% 35.54/4.99      ( k4_relat_1(k7_relat_1(k4_relat_1(sK2),k2_relat_1(k4_relat_1(k4_relat_1(sK2))))) = k4_relat_1(k4_relat_1(sK2)) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10686,c_23007]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_112085,plain,
% 35.54/4.99      ( v1_relat_1(k7_relat_1(k4_relat_1(sK2),k2_relat_1(k4_relat_1(k4_relat_1(sK2))))) != iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(k4_relat_1(sK2))) = iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_112082,c_1420]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2227,plain,
% 35.54/4.99      ( v1_relat_1(k4_relat_1(k4_relat_1(sK2)))
% 35.54/4.99      | ~ v1_relat_1(k4_relat_1(sK2)) ),
% 35.54/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2235,plain,
% 35.54/4.99      ( v1_relat_1(k4_relat_1(k4_relat_1(sK2))) = iProver_top
% 35.54/4.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_2227]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_113576,plain,
% 35.54/4.99      ( v1_relat_1(k4_relat_1(k4_relat_1(sK2))) = iProver_top ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_112085,c_47,c_1696,c_1731,c_2047,c_2235]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_11,plain,
% 35.54/4.99      ( ~ v1_relat_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X1)
% 35.54/4.99      | ~ v1_relat_1(X2)
% 35.54/4.99      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 35.54/4.99      inference(cnf_transformation,[],[f86]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1414,plain,
% 35.54/4.99      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 35.54/4.99      | v1_relat_1(X0) != iProver_top
% 35.54/4.99      | v1_relat_1(X1) != iProver_top
% 35.54/4.99      | v1_relat_1(X2) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_4375,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
% 35.54/4.99      | v1_relat_1(X0) != iProver_top
% 35.54/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_1414]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10684,plain,
% 35.54/4.99      ( k5_relat_1(k5_relat_1(sK2,k4_relat_1(sK2)),X0) = k5_relat_1(sK2,k5_relat_1(k4_relat_1(sK2),X0))
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10677,c_4375]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_25,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v2_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 35.54/4.99      inference(cnf_transformation,[],[f128]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_478,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 35.54/4.99      | sK2 != X0 ),
% 35.54/4.99      inference(resolution_lifted,[status(thm)],[c_25,c_39]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_479,plain,
% 35.54/4.99      ( ~ v1_funct_1(sK2)
% 35.54/4.99      | ~ v1_relat_1(sK2)
% 35.54/4.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 35.54/4.99      inference(unflattening,[status(thm)],[c_478]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_481,plain,
% 35.54/4.99      ( ~ v1_relat_1(sK2)
% 35.54/4.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_479,c_45]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1397,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2059,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_1397,c_45,c_44,c_479,c_1695,c_1730]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2061,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_2059,c_1775]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_9849,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_9836,c_2061]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10703,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k5_relat_1(k4_relat_1(sK2),X0)) = k5_relat_1(k6_partfun1(sK0),X0)
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_10684,c_9849]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_116863,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2)))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(k4_relat_1(sK2))) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_113576,c_10703]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3796,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_1413]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3798,plain,
% 35.54/4.99      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_3796,c_2754]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_4250,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK2))
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_1415]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10687,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2))) = k4_relat_1(k5_relat_1(k4_relat_1(sK2),sK2)) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10677,c_4250]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_24,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v2_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 35.54/4.99      inference(cnf_transformation,[],[f127]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_492,plain,
% 35.54/4.99      ( ~ v1_funct_1(X0)
% 35.54/4.99      | ~ v1_relat_1(X0)
% 35.54/4.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 35.54/4.99      | sK2 != X0 ),
% 35.54/4.99      inference(resolution_lifted,[status(thm)],[c_24,c_39]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_493,plain,
% 35.54/4.99      ( ~ v1_funct_1(sK2)
% 35.54/4.99      | ~ v1_relat_1(sK2)
% 35.54/4.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 35.54/4.99      inference(unflattening,[status(thm)],[c_492]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_495,plain,
% 35.54/4.99      ( ~ v1_relat_1(sK2)
% 35.54/4.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_493,c_45]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1396,plain,
% 35.54/4.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 35.54/4.99      | v1_relat_1(sK2) != iProver_top ),
% 35.54/4.99      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2055,plain,
% 35.54/4.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_1396,c_45,c_44,c_493,c_1695,c_1730]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2057,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_2055,c_1775]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2914,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_2754,c_2057]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10701,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2))) = k4_relat_1(k6_partfun1(sK1)) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_10687,c_2914]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10702,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2))) = k6_partfun1(sK1) ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_10701,c_14]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_116890,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(sK0),k4_relat_1(k4_relat_1(sK2))) = sK2 ),
% 35.54/4.99      inference(light_normalisation,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_116863,c_3798,c_10702]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6918,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(k6_partfun1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_partfun1(X0)))
% 35.54/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_6910,c_1415]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6926,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_partfun1(X0)))
% 35.54/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_6918,c_14]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10693,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(k4_relat_1(sK2))) = k4_relat_1(k5_relat_1(k4_relat_1(sK2),k6_partfun1(X0))) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10677,c_6926]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10694,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(k4_relat_1(sK2))) = k7_relat_1(k4_relat_1(k4_relat_1(sK2)),X0) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10677,c_2642]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10696,plain,
% 35.54/4.99      ( k4_relat_1(k5_relat_1(k4_relat_1(sK2),k6_partfun1(X0))) = k7_relat_1(k4_relat_1(k4_relat_1(sK2)),X0) ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_10693,c_10694]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6916,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k6_partfun1(X0))) = k4_relat_1(k5_relat_1(k6_partfun1(X0),sK2)) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_6910,c_4250]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3797,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),sK2) = k7_relat_1(sK2,X0) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_1412]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6927,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(X0)) = k4_relat_1(k7_relat_1(sK2,X0)) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_6916,c_14,c_3797]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10697,plain,
% 35.54/4.99      ( k7_relat_1(k4_relat_1(k4_relat_1(sK2)),X0) = k4_relat_1(k4_relat_1(k7_relat_1(sK2,X0))) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_10696,c_6927]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10698,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(k4_relat_1(sK2))) = k4_relat_1(k4_relat_1(k7_relat_1(sK2,X0))) ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_10697,c_10694]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_117438,plain,
% 35.54/4.99      ( k4_relat_1(k4_relat_1(k7_relat_1(sK2,sK0))) = sK2 ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_116890,c_10698]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_117439,plain,
% 35.54/4.99      ( k4_relat_1(k4_relat_1(sK2)) = sK2 ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_117438,c_2419]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_10688,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
% 35.54/4.99      | v1_relat_1(X0) != iProver_top
% 35.54/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_10677,c_1414]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_113580,plain,
% 35.54/4.99      ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),k4_relat_1(k4_relat_1(sK2))),X0) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(k4_relat_1(k4_relat_1(sK2)),X0))
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_113576,c_10688]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_113737,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(k4_relat_1(k4_relat_1(sK2)),X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 35.54/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_113580,c_10702]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_113891,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(k4_relat_1(k4_relat_1(sK2)),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3714,c_113737]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2155,plain,
% 35.54/4.99      ( k7_relat_1(sK3,sK1) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_1403,c_1399]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_2349,plain,
% 35.54/4.99      ( k7_relat_1(sK3,sK1) = sK3 ),
% 35.54/4.99      inference(global_propositional_subsumption,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_2155,c_49,c_1895,c_2119]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_3721,plain,
% 35.54/4.99      ( k5_relat_1(k6_partfun1(X0),sK3) = k7_relat_1(sK3,X0) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3714,c_1412]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_113930,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(k4_relat_1(k4_relat_1(sK2)),sK3)) = sK3 ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_113891,c_2349,c_3721]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_117752,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = sK3 ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_117439,c_113930]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6656,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) = k4_relat_1(sK2) ),
% 35.54/4.99      inference(superposition,[status(thm)],[c_3790,c_2516]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_6658,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k4_relat_1(sK2) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_6656,c_1843]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_17773,plain,
% 35.54/4.99      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k4_relat_1(sK2) ),
% 35.54/4.99      inference(light_normalisation,[status(thm)],[c_6658,c_6658,c_9836]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_117783,plain,
% 35.54/4.99      ( k4_relat_1(sK2) = sK3 ),
% 35.54/4.99      inference(light_normalisation,
% 35.54/4.99                [status(thm)],
% 35.54/4.99                [c_117752,c_6647,c_17773]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_36,negated_conjecture,
% 35.54/4.99      ( k2_funct_1(sK2) != sK3 ),
% 35.54/4.99      inference(cnf_transformation,[],[f121]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(c_1777,plain,
% 35.54/4.99      ( k4_relat_1(sK2) != sK3 ),
% 35.54/4.99      inference(demodulation,[status(thm)],[c_1775,c_36]) ).
% 35.54/4.99  
% 35.54/4.99  cnf(contradiction,plain,
% 35.54/4.99      ( $false ),
% 35.54/4.99      inference(minisat,[status(thm)],[c_117783,c_1777]) ).
% 35.54/4.99  
% 35.54/4.99  
% 35.54/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.54/4.99  
% 35.54/4.99  ------                               Statistics
% 35.54/4.99  
% 35.54/4.99  ------ General
% 35.54/4.99  
% 35.54/4.99  abstr_ref_over_cycles:                  0
% 35.54/4.99  abstr_ref_under_cycles:                 0
% 35.54/4.99  gc_basic_clause_elim:                   0
% 35.54/4.99  forced_gc_time:                         0
% 35.54/4.99  parsing_time:                           0.009
% 35.54/4.99  unif_index_cands_time:                  0.
% 35.54/4.99  unif_index_add_time:                    0.
% 35.54/4.99  orderings_time:                         0.
% 35.54/4.99  out_proof_time:                         0.039
% 35.54/4.99  total_time:                             4.471
% 35.54/4.99  num_of_symbols:                         56
% 35.54/4.99  num_of_terms:                           138265
% 35.54/4.99  
% 35.54/4.99  ------ Preprocessing
% 35.54/4.99  
% 35.54/4.99  num_of_splits:                          0
% 35.54/4.99  num_of_split_atoms:                     0
% 35.54/4.99  num_of_reused_defs:                     0
% 35.54/4.99  num_eq_ax_congr_red:                    9
% 35.54/4.99  num_of_sem_filtered_clauses:            1
% 35.54/4.99  num_of_subtypes:                        0
% 35.54/4.99  monotx_restored_types:                  0
% 35.54/4.99  sat_num_of_epr_types:                   0
% 35.54/4.99  sat_num_of_non_cyclic_types:            0
% 35.54/4.99  sat_guarded_non_collapsed_types:        0
% 35.54/4.99  num_pure_diseq_elim:                    0
% 35.54/4.99  simp_replaced_by:                       0
% 35.54/4.99  res_preprocessed:                       201
% 35.54/4.99  prep_upred:                             0
% 35.54/4.99  prep_unflattend:                        15
% 35.54/4.99  smt_new_axioms:                         0
% 35.54/4.99  pred_elim_cands:                        4
% 35.54/4.99  pred_elim:                              3
% 35.54/4.99  pred_elim_cl:                           4
% 35.54/4.99  pred_elim_cycles:                       5
% 35.54/4.99  merged_defs:                            0
% 35.54/4.99  merged_defs_ncl:                        0
% 35.54/4.99  bin_hyper_res:                          0
% 35.54/4.99  prep_cycles:                            4
% 35.54/4.99  pred_elim_time:                         0.002
% 35.54/4.99  splitting_time:                         0.
% 35.54/4.99  sem_filter_time:                        0.
% 35.54/4.99  monotx_time:                            0.
% 35.54/4.99  subtype_inf_time:                       0.
% 35.54/4.99  
% 35.54/4.99  ------ Problem properties
% 35.54/4.99  
% 35.54/4.99  clauses:                                40
% 35.54/4.99  conjectures:                            8
% 35.54/4.99  epr:                                    6
% 35.54/4.99  horn:                                   40
% 35.54/4.99  ground:                                 14
% 35.54/4.99  unary:                                  14
% 35.54/4.99  binary:                                 13
% 35.54/4.99  lits:                                   86
% 35.54/4.99  lits_eq:                                25
% 35.54/4.99  fd_pure:                                0
% 35.54/4.99  fd_pseudo:                              0
% 35.54/4.99  fd_cond:                                0
% 35.54/4.99  fd_pseudo_cond:                         1
% 35.54/4.99  ac_symbols:                             0
% 35.54/4.99  
% 35.54/4.99  ------ Propositional Solver
% 35.54/4.99  
% 35.54/4.99  prop_solver_calls:                      60
% 35.54/4.99  prop_fast_solver_calls:                 3941
% 35.54/4.99  smt_solver_calls:                       0
% 35.54/4.99  smt_fast_solver_calls:                  0
% 35.54/4.99  prop_num_of_clauses:                    59467
% 35.54/4.99  prop_preprocess_simplified:             103090
% 35.54/4.99  prop_fo_subsumed:                       607
% 35.54/4.99  prop_solver_time:                       0.
% 35.54/4.99  smt_solver_time:                        0.
% 35.54/4.99  smt_fast_solver_time:                   0.
% 35.54/4.99  prop_fast_solver_time:                  0.
% 35.54/4.99  prop_unsat_core_time:                   0.011
% 35.54/4.99  
% 35.54/4.99  ------ QBF
% 35.54/4.99  
% 35.54/4.99  qbf_q_res:                              0
% 35.54/4.99  qbf_num_tautologies:                    0
% 35.54/4.99  qbf_prep_cycles:                        0
% 35.54/4.99  
% 35.54/4.99  ------ BMC1
% 35.54/4.99  
% 35.54/4.99  bmc1_current_bound:                     -1
% 35.54/4.99  bmc1_last_solved_bound:                 -1
% 35.54/4.99  bmc1_unsat_core_size:                   -1
% 35.54/4.99  bmc1_unsat_core_parents_size:           -1
% 35.54/4.99  bmc1_merge_next_fun:                    0
% 35.54/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.54/4.99  
% 35.54/4.99  ------ Instantiation
% 35.54/4.99  
% 35.54/4.99  inst_num_of_clauses:                    6395
% 35.54/4.99  inst_num_in_passive:                    2690
% 35.54/4.99  inst_num_in_active:                     5115
% 35.54/4.99  inst_num_in_unprocessed:                1323
% 35.54/4.99  inst_num_of_loops:                      5429
% 35.54/4.99  inst_num_of_learning_restarts:          1
% 35.54/4.99  inst_num_moves_active_passive:          306
% 35.54/4.99  inst_lit_activity:                      0
% 35.54/4.99  inst_lit_activity_moves:                7
% 35.54/4.99  inst_num_tautologies:                   0
% 35.54/4.99  inst_num_prop_implied:                  0
% 35.54/4.99  inst_num_existing_simplified:           0
% 35.54/4.99  inst_num_eq_res_simplified:             0
% 35.54/4.99  inst_num_child_elim:                    0
% 35.54/4.99  inst_num_of_dismatching_blockings:      7567
% 35.54/4.99  inst_num_of_non_proper_insts:           16108
% 35.54/4.99  inst_num_of_duplicates:                 0
% 35.54/4.99  inst_inst_num_from_inst_to_res:         0
% 35.54/4.99  inst_dismatching_checking_time:         0.
% 35.54/4.99  
% 35.54/4.99  ------ Resolution
% 35.54/4.99  
% 35.54/4.99  res_num_of_clauses:                     58
% 35.54/4.99  res_num_in_passive:                     58
% 35.54/4.99  res_num_in_active:                      0
% 35.54/4.99  res_num_of_loops:                       205
% 35.54/4.99  res_forward_subset_subsumed:            824
% 35.54/4.99  res_backward_subset_subsumed:           0
% 35.54/4.99  res_forward_subsumed:                   0
% 35.54/4.99  res_backward_subsumed:                  0
% 35.54/4.99  res_forward_subsumption_resolution:     0
% 35.54/4.99  res_backward_subsumption_resolution:    0
% 35.54/4.99  res_clause_to_clause_subsumption:       11227
% 35.54/4.99  res_orphan_elimination:                 0
% 35.54/4.99  res_tautology_del:                      1006
% 35.54/4.99  res_num_eq_res_simplified:              0
% 35.54/4.99  res_num_sel_changes:                    0
% 35.54/4.99  res_moves_from_active_to_pass:          0
% 35.54/4.99  
% 35.54/4.99  ------ Superposition
% 35.54/4.99  
% 35.54/4.99  sup_time_total:                         0.
% 35.54/4.99  sup_time_generating:                    0.
% 35.54/4.99  sup_time_sim_full:                      0.
% 35.54/4.99  sup_time_sim_immed:                     0.
% 35.54/4.99  
% 35.54/4.99  sup_num_of_clauses:                     5297
% 35.54/4.99  sup_num_in_active:                      895
% 35.54/4.99  sup_num_in_passive:                     4402
% 35.54/4.99  sup_num_of_loops:                       1085
% 35.54/4.99  sup_fw_superposition:                   3908
% 35.54/4.99  sup_bw_superposition:                   2580
% 35.54/4.99  sup_immediate_simplified:               1938
% 35.54/4.99  sup_given_eliminated:                   1
% 35.54/4.99  comparisons_done:                       0
% 35.54/4.99  comparisons_avoided:                    0
% 35.54/4.99  
% 35.54/4.99  ------ Simplifications
% 35.54/4.99  
% 35.54/4.99  
% 35.54/4.99  sim_fw_subset_subsumed:                 104
% 35.54/4.99  sim_bw_subset_subsumed:                 273
% 35.54/4.99  sim_fw_subsumed:                        143
% 35.54/4.99  sim_bw_subsumed:                        1
% 35.54/4.99  sim_fw_subsumption_res:                 0
% 35.54/4.99  sim_bw_subsumption_res:                 0
% 35.54/4.99  sim_tautology_del:                      21
% 35.54/4.99  sim_eq_tautology_del:                   302
% 35.54/4.99  sim_eq_res_simp:                        0
% 35.54/4.99  sim_fw_demodulated:                     485
% 35.54/4.99  sim_bw_demodulated:                     126
% 35.54/4.99  sim_light_normalised:                   1401
% 35.54/4.99  sim_joinable_taut:                      0
% 35.54/4.99  sim_joinable_simp:                      0
% 35.54/4.99  sim_ac_normalised:                      0
% 35.54/4.99  sim_smt_subsumption:                    0
% 35.54/4.99  
%------------------------------------------------------------------------------
