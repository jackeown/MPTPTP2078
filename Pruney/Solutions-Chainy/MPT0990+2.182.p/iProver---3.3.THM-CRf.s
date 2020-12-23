%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:35 EST 2020

% Result     : Theorem 11.43s
% Output     : CNFRefutation 11.43s
% Verified   : 
% Statistics : Number of formulae       :  216 (1332 expanded)
%              Number of clauses        :  130 ( 392 expanded)
%              Number of leaves         :   23 ( 340 expanded)
%              Depth                    :   20
%              Number of atoms          :  824 (10764 expanded)
%              Number of equality atoms :  404 (3962 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,conjecture,(
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

fof(f34,negated_conjecture,(
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
    inference(negated_conjecture,[],[f33])).

fof(f73,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f74,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f73])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK4
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & k2_relset_1(sK1,sK2,sK3) = sK2
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f74,f79,f78])).

fof(f130,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f94,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f132,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f80])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f136,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f80])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f69])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f131,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f80])).

fof(f138,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

fof(f140,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f80])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f28,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f119,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f144,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f92,f119])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f104,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f135,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f80])).

fof(f27,axiom,(
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
    inference(ennf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f63])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f133,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

fof(f24,axiom,(
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
    inference(ennf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f59])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f137,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f80])).

fof(f26,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f117,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f65])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f134,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f80])).

fof(f139,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f80])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f148,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f99,f119])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f67])).

fof(f123,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f108,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f151,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f108,f119])).

fof(f141,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_59,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1764,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1796,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1803,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1766,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4965,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_1804])).

cnf(c_5268,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_4965])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1800,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7747,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_1800])).

cnf(c_21012,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_7747])).

cnf(c_21506,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21012,c_5268])).

cnf(c_21507,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_21506])).

cnf(c_21515,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK3),sK3),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5268,c_21507])).

cnf(c_53,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1774,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1808,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1807,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3416,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1808,c_1807])).

cnf(c_5765,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1774,c_3416])).

cnf(c_5769,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_53,c_5765])).

cnf(c_58,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_51,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_49,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_1879,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_1974,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_2157,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_7012,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5769,c_59,c_58,c_57,c_53,c_51,c_49,c_2157])).

cnf(c_21520,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21515,c_7012])).

cnf(c_21659,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK2),k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_21520])).

cnf(c_23551,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK2),k2_funct_1(sK3))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_21659])).

cnf(c_44,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1773,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_4971,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1773,c_3416])).

cnf(c_4975,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK2 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_53,c_4971])).

cnf(c_1880,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_2010,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1880])).

cnf(c_2170,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_5211,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4975,c_59,c_58,c_57,c_53,c_51,c_49,c_2170])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_1799,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4380,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_1799])).

cnf(c_11550,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_4380])).

cnf(c_1770,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_24,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1789,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5160,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_1789])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1783,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3975,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1766,c_1783])).

cnf(c_3976,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3975,c_53])).

cnf(c_5161,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5160,c_3976])).

cnf(c_60,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_5271,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5161,c_60,c_5268])).

cnf(c_11553,plain,
    ( k5_relat_1(k6_partfun1(sK2),k2_funct_1(sK3)) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11550,c_5271])).

cnf(c_12012,plain,
    ( k5_relat_1(k6_partfun1(sK2),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11553,c_5268])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1769,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_4964,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_1804])).

cnf(c_5214,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_4964])).

cnf(c_21662,plain,
    ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,sK4)) = k5_relat_1(k6_partfun1(sK2),sK4) ),
    inference(superposition,[status(thm)],[c_5214,c_21520])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1779,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8220,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_1779])).

cnf(c_56,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_63,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_8377,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8220,c_63])).

cnf(c_8378,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8377])).

cnf(c_8387,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_8378])).

cnf(c_33,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_52,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_52])).

cnf(c_618,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_36,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_626,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_618,c_36])).

cnf(c_1762,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2280,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2853,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1762,c_59,c_57,c_56,c_54,c_626,c_2280])).

cnf(c_8390,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8387,c_2853])).

cnf(c_10266,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8390,c_60])).

cnf(c_38,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_630,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_52])).

cnf(c_631,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_733,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_631])).

cnf(c_1761,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_2333,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1761])).

cnf(c_61,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_62,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_55,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_64,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_65,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_2860,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2333,c_60,c_61,c_62,c_63,c_64,c_65])).

cnf(c_4976,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_4971])).

cnf(c_50,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_1897,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1006,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1947,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_2302,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK1 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_3679,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3680,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3679])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1777,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_9507,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | o_0_0_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1777,c_3416])).

cnf(c_9509,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_53,c_9507])).

cnf(c_9819,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | o_0_0_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9509,c_60,c_61,c_62])).

cnf(c_9820,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9819])).

cnf(c_9825,plain,
    ( sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_9820])).

cnf(c_12236,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4976,c_63,c_64,c_65,c_50,c_0,c_1897,c_2302,c_3680,c_9825])).

cnf(c_10166,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9825,c_63,c_64,c_65,c_50,c_0,c_1897,c_2302,c_3680])).

cnf(c_28,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_1785,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10176,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10166,c_1785])).

cnf(c_10982,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10176,c_63,c_5214])).

cnf(c_12238,plain,
    ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK2) ),
    inference(demodulation,[status(thm)],[c_12236,c_10982])).

cnf(c_5354,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK4)),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_5214,c_1799])).

cnf(c_13813,plain,
    ( k5_relat_1(k6_partfun1(sK2),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_12238,c_5354])).

cnf(c_21668,plain,
    ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(sK1)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_21662,c_10266,c_13813])).

cnf(c_23555,plain,
    ( k2_funct_1(sK3) = sK4
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23551,c_5211,c_12012,c_21668])).

cnf(c_48,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f141])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23555,c_5268,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:27:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.43/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.43/1.98  
% 11.43/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.43/1.98  
% 11.43/1.98  ------  iProver source info
% 11.43/1.98  
% 11.43/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.43/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.43/1.98  git: non_committed_changes: false
% 11.43/1.98  git: last_make_outside_of_git: false
% 11.43/1.98  
% 11.43/1.98  ------ 
% 11.43/1.98  
% 11.43/1.98  ------ Input Options
% 11.43/1.98  
% 11.43/1.98  --out_options                           all
% 11.43/1.98  --tptp_safe_out                         true
% 11.43/1.98  --problem_path                          ""
% 11.43/1.98  --include_path                          ""
% 11.43/1.98  --clausifier                            res/vclausify_rel
% 11.43/1.98  --clausifier_options                    ""
% 11.43/1.98  --stdin                                 false
% 11.43/1.98  --stats_out                             all
% 11.43/1.98  
% 11.43/1.98  ------ General Options
% 11.43/1.98  
% 11.43/1.98  --fof                                   false
% 11.43/1.98  --time_out_real                         305.
% 11.43/1.98  --time_out_virtual                      -1.
% 11.43/1.98  --symbol_type_check                     false
% 11.43/1.98  --clausify_out                          false
% 11.43/1.98  --sig_cnt_out                           false
% 11.43/1.98  --trig_cnt_out                          false
% 11.43/1.98  --trig_cnt_out_tolerance                1.
% 11.43/1.98  --trig_cnt_out_sk_spl                   false
% 11.43/1.98  --abstr_cl_out                          false
% 11.43/1.98  
% 11.43/1.98  ------ Global Options
% 11.43/1.98  
% 11.43/1.98  --schedule                              default
% 11.43/1.98  --add_important_lit                     false
% 11.43/1.98  --prop_solver_per_cl                    1000
% 11.43/1.98  --min_unsat_core                        false
% 11.43/1.98  --soft_assumptions                      false
% 11.43/1.98  --soft_lemma_size                       3
% 11.43/1.98  --prop_impl_unit_size                   0
% 11.43/1.98  --prop_impl_unit                        []
% 11.43/1.98  --share_sel_clauses                     true
% 11.43/1.98  --reset_solvers                         false
% 11.43/1.98  --bc_imp_inh                            [conj_cone]
% 11.43/1.98  --conj_cone_tolerance                   3.
% 11.43/1.98  --extra_neg_conj                        none
% 11.43/1.98  --large_theory_mode                     true
% 11.43/1.98  --prolific_symb_bound                   200
% 11.43/1.98  --lt_threshold                          2000
% 11.43/1.98  --clause_weak_htbl                      true
% 11.43/1.98  --gc_record_bc_elim                     false
% 11.43/1.98  
% 11.43/1.98  ------ Preprocessing Options
% 11.43/1.98  
% 11.43/1.98  --preprocessing_flag                    true
% 11.43/1.98  --time_out_prep_mult                    0.1
% 11.43/1.98  --splitting_mode                        input
% 11.43/1.98  --splitting_grd                         true
% 11.43/1.98  --splitting_cvd                         false
% 11.43/1.98  --splitting_cvd_svl                     false
% 11.43/1.98  --splitting_nvd                         32
% 11.43/1.98  --sub_typing                            true
% 11.43/1.98  --prep_gs_sim                           true
% 11.43/1.98  --prep_unflatten                        true
% 11.43/1.98  --prep_res_sim                          true
% 11.43/1.98  --prep_upred                            true
% 11.43/1.98  --prep_sem_filter                       exhaustive
% 11.43/1.98  --prep_sem_filter_out                   false
% 11.43/1.98  --pred_elim                             true
% 11.43/1.98  --res_sim_input                         true
% 11.43/1.98  --eq_ax_congr_red                       true
% 11.43/1.98  --pure_diseq_elim                       true
% 11.43/1.98  --brand_transform                       false
% 11.43/1.98  --non_eq_to_eq                          false
% 11.43/1.98  --prep_def_merge                        true
% 11.43/1.98  --prep_def_merge_prop_impl              false
% 11.43/1.98  --prep_def_merge_mbd                    true
% 11.43/1.98  --prep_def_merge_tr_red                 false
% 11.43/1.98  --prep_def_merge_tr_cl                  false
% 11.43/1.98  --smt_preprocessing                     true
% 11.43/1.98  --smt_ac_axioms                         fast
% 11.43/1.98  --preprocessed_out                      false
% 11.43/1.98  --preprocessed_stats                    false
% 11.43/1.98  
% 11.43/1.98  ------ Abstraction refinement Options
% 11.43/1.98  
% 11.43/1.98  --abstr_ref                             []
% 11.43/1.98  --abstr_ref_prep                        false
% 11.43/1.98  --abstr_ref_until_sat                   false
% 11.43/1.98  --abstr_ref_sig_restrict                funpre
% 11.43/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.43/1.98  --abstr_ref_under                       []
% 11.43/1.98  
% 11.43/1.98  ------ SAT Options
% 11.43/1.98  
% 11.43/1.98  --sat_mode                              false
% 11.43/1.98  --sat_fm_restart_options                ""
% 11.43/1.98  --sat_gr_def                            false
% 11.43/1.98  --sat_epr_types                         true
% 11.43/1.98  --sat_non_cyclic_types                  false
% 11.43/1.98  --sat_finite_models                     false
% 11.43/1.98  --sat_fm_lemmas                         false
% 11.43/1.98  --sat_fm_prep                           false
% 11.43/1.98  --sat_fm_uc_incr                        true
% 11.43/1.98  --sat_out_model                         small
% 11.43/1.98  --sat_out_clauses                       false
% 11.43/1.98  
% 11.43/1.98  ------ QBF Options
% 11.43/1.98  
% 11.43/1.98  --qbf_mode                              false
% 11.43/1.98  --qbf_elim_univ                         false
% 11.43/1.98  --qbf_dom_inst                          none
% 11.43/1.98  --qbf_dom_pre_inst                      false
% 11.43/1.98  --qbf_sk_in                             false
% 11.43/1.98  --qbf_pred_elim                         true
% 11.43/1.98  --qbf_split                             512
% 11.43/1.98  
% 11.43/1.98  ------ BMC1 Options
% 11.43/1.98  
% 11.43/1.98  --bmc1_incremental                      false
% 11.43/1.98  --bmc1_axioms                           reachable_all
% 11.43/1.98  --bmc1_min_bound                        0
% 11.43/1.98  --bmc1_max_bound                        -1
% 11.43/1.98  --bmc1_max_bound_default                -1
% 11.43/1.98  --bmc1_symbol_reachability              true
% 11.43/1.98  --bmc1_property_lemmas                  false
% 11.43/1.98  --bmc1_k_induction                      false
% 11.43/1.98  --bmc1_non_equiv_states                 false
% 11.43/1.98  --bmc1_deadlock                         false
% 11.43/1.98  --bmc1_ucm                              false
% 11.43/1.98  --bmc1_add_unsat_core                   none
% 11.43/1.98  --bmc1_unsat_core_children              false
% 11.43/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.43/1.98  --bmc1_out_stat                         full
% 11.43/1.98  --bmc1_ground_init                      false
% 11.43/1.98  --bmc1_pre_inst_next_state              false
% 11.43/1.98  --bmc1_pre_inst_state                   false
% 11.43/1.98  --bmc1_pre_inst_reach_state             false
% 11.43/1.98  --bmc1_out_unsat_core                   false
% 11.43/1.98  --bmc1_aig_witness_out                  false
% 11.43/1.98  --bmc1_verbose                          false
% 11.43/1.98  --bmc1_dump_clauses_tptp                false
% 11.43/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.43/1.98  --bmc1_dump_file                        -
% 11.43/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.43/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.43/1.98  --bmc1_ucm_extend_mode                  1
% 11.43/1.98  --bmc1_ucm_init_mode                    2
% 11.43/1.98  --bmc1_ucm_cone_mode                    none
% 11.43/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.43/1.98  --bmc1_ucm_relax_model                  4
% 11.43/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.43/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.43/1.98  --bmc1_ucm_layered_model                none
% 11.43/1.98  --bmc1_ucm_max_lemma_size               10
% 11.43/1.98  
% 11.43/1.98  ------ AIG Options
% 11.43/1.98  
% 11.43/1.98  --aig_mode                              false
% 11.43/1.98  
% 11.43/1.98  ------ Instantiation Options
% 11.43/1.98  
% 11.43/1.98  --instantiation_flag                    true
% 11.43/1.98  --inst_sos_flag                         true
% 11.43/1.98  --inst_sos_phase                        true
% 11.43/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.43/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.43/1.98  --inst_lit_sel_side                     num_symb
% 11.43/1.98  --inst_solver_per_active                1400
% 11.43/1.98  --inst_solver_calls_frac                1.
% 11.43/1.98  --inst_passive_queue_type               priority_queues
% 11.43/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.43/1.98  --inst_passive_queues_freq              [25;2]
% 11.43/1.98  --inst_dismatching                      true
% 11.43/1.98  --inst_eager_unprocessed_to_passive     true
% 11.43/1.98  --inst_prop_sim_given                   true
% 11.43/1.98  --inst_prop_sim_new                     false
% 11.43/1.98  --inst_subs_new                         false
% 11.43/1.98  --inst_eq_res_simp                      false
% 11.43/1.98  --inst_subs_given                       false
% 11.43/1.98  --inst_orphan_elimination               true
% 11.43/1.98  --inst_learning_loop_flag               true
% 11.43/1.98  --inst_learning_start                   3000
% 11.43/1.98  --inst_learning_factor                  2
% 11.43/1.98  --inst_start_prop_sim_after_learn       3
% 11.43/1.98  --inst_sel_renew                        solver
% 11.43/1.98  --inst_lit_activity_flag                true
% 11.43/1.98  --inst_restr_to_given                   false
% 11.43/1.98  --inst_activity_threshold               500
% 11.43/1.98  --inst_out_proof                        true
% 11.43/1.98  
% 11.43/1.98  ------ Resolution Options
% 11.43/1.98  
% 11.43/1.98  --resolution_flag                       true
% 11.43/1.98  --res_lit_sel                           adaptive
% 11.43/1.98  --res_lit_sel_side                      none
% 11.43/1.98  --res_ordering                          kbo
% 11.43/1.98  --res_to_prop_solver                    active
% 11.43/1.98  --res_prop_simpl_new                    false
% 11.43/1.98  --res_prop_simpl_given                  true
% 11.43/1.98  --res_passive_queue_type                priority_queues
% 11.43/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.43/1.98  --res_passive_queues_freq               [15;5]
% 11.43/1.98  --res_forward_subs                      full
% 11.43/1.98  --res_backward_subs                     full
% 11.43/1.98  --res_forward_subs_resolution           true
% 11.43/1.98  --res_backward_subs_resolution          true
% 11.43/1.98  --res_orphan_elimination                true
% 11.43/1.98  --res_time_limit                        2.
% 11.43/1.98  --res_out_proof                         true
% 11.43/1.98  
% 11.43/1.98  ------ Superposition Options
% 11.43/1.98  
% 11.43/1.98  --superposition_flag                    true
% 11.43/1.98  --sup_passive_queue_type                priority_queues
% 11.43/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.43/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.43/1.98  --demod_completeness_check              fast
% 11.43/1.98  --demod_use_ground                      true
% 11.43/1.98  --sup_to_prop_solver                    passive
% 11.43/1.98  --sup_prop_simpl_new                    true
% 11.43/1.98  --sup_prop_simpl_given                  true
% 11.43/1.98  --sup_fun_splitting                     true
% 11.43/1.98  --sup_smt_interval                      50000
% 11.43/1.98  
% 11.43/1.98  ------ Superposition Simplification Setup
% 11.43/1.98  
% 11.43/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.43/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.43/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.43/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.43/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.43/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.43/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.43/1.98  --sup_immed_triv                        [TrivRules]
% 11.43/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.98  --sup_immed_bw_main                     []
% 11.43/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.43/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.43/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.98  --sup_input_bw                          []
% 11.43/1.98  
% 11.43/1.98  ------ Combination Options
% 11.43/1.98  
% 11.43/1.98  --comb_res_mult                         3
% 11.43/1.98  --comb_sup_mult                         2
% 11.43/1.98  --comb_inst_mult                        10
% 11.43/1.98  
% 11.43/1.98  ------ Debug Options
% 11.43/1.98  
% 11.43/1.98  --dbg_backtrace                         false
% 11.43/1.98  --dbg_dump_prop_clauses                 false
% 11.43/1.98  --dbg_dump_prop_clauses_file            -
% 11.43/1.98  --dbg_out_stat                          false
% 11.43/1.98  ------ Parsing...
% 11.43/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.43/1.98  
% 11.43/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.43/1.98  
% 11.43/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.43/1.98  
% 11.43/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.43/1.98  ------ Proving...
% 11.43/1.98  ------ Problem Properties 
% 11.43/1.98  
% 11.43/1.98  
% 11.43/1.98  clauses                                 55
% 11.43/1.98  conjectures                             11
% 11.43/1.98  EPR                                     11
% 11.43/1.98  Horn                                    51
% 11.43/1.98  unary                                   21
% 11.43/1.98  binary                                  7
% 11.43/1.98  lits                                    179
% 11.43/1.98  lits eq                                 41
% 11.43/1.98  fd_pure                                 0
% 11.43/1.98  fd_pseudo                               0
% 11.43/1.98  fd_cond                                 5
% 11.43/1.98  fd_pseudo_cond                          1
% 11.43/1.98  AC symbols                              0
% 11.43/1.98  
% 11.43/1.98  ------ Schedule dynamic 5 is on 
% 11.43/1.98  
% 11.43/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.43/1.98  
% 11.43/1.98  
% 11.43/1.98  ------ 
% 11.43/1.98  Current options:
% 11.43/1.98  ------ 
% 11.43/1.98  
% 11.43/1.98  ------ Input Options
% 11.43/1.98  
% 11.43/1.98  --out_options                           all
% 11.43/1.98  --tptp_safe_out                         true
% 11.43/1.98  --problem_path                          ""
% 11.43/1.98  --include_path                          ""
% 11.43/1.98  --clausifier                            res/vclausify_rel
% 11.43/1.98  --clausifier_options                    ""
% 11.43/1.98  --stdin                                 false
% 11.43/1.98  --stats_out                             all
% 11.43/1.98  
% 11.43/1.98  ------ General Options
% 11.43/1.98  
% 11.43/1.98  --fof                                   false
% 11.43/1.98  --time_out_real                         305.
% 11.43/1.98  --time_out_virtual                      -1.
% 11.43/1.98  --symbol_type_check                     false
% 11.43/1.98  --clausify_out                          false
% 11.43/1.98  --sig_cnt_out                           false
% 11.43/1.98  --trig_cnt_out                          false
% 11.43/1.98  --trig_cnt_out_tolerance                1.
% 11.43/1.98  --trig_cnt_out_sk_spl                   false
% 11.43/1.98  --abstr_cl_out                          false
% 11.43/1.98  
% 11.43/1.98  ------ Global Options
% 11.43/1.98  
% 11.43/1.98  --schedule                              default
% 11.43/1.98  --add_important_lit                     false
% 11.43/1.98  --prop_solver_per_cl                    1000
% 11.43/1.98  --min_unsat_core                        false
% 11.43/1.98  --soft_assumptions                      false
% 11.43/1.98  --soft_lemma_size                       3
% 11.43/1.98  --prop_impl_unit_size                   0
% 11.43/1.98  --prop_impl_unit                        []
% 11.43/1.98  --share_sel_clauses                     true
% 11.43/1.98  --reset_solvers                         false
% 11.43/1.98  --bc_imp_inh                            [conj_cone]
% 11.43/1.98  --conj_cone_tolerance                   3.
% 11.43/1.98  --extra_neg_conj                        none
% 11.43/1.98  --large_theory_mode                     true
% 11.43/1.98  --prolific_symb_bound                   200
% 11.43/1.98  --lt_threshold                          2000
% 11.43/1.98  --clause_weak_htbl                      true
% 11.43/1.98  --gc_record_bc_elim                     false
% 11.43/1.98  
% 11.43/1.98  ------ Preprocessing Options
% 11.43/1.98  
% 11.43/1.98  --preprocessing_flag                    true
% 11.43/1.98  --time_out_prep_mult                    0.1
% 11.43/1.98  --splitting_mode                        input
% 11.43/1.98  --splitting_grd                         true
% 11.43/1.98  --splitting_cvd                         false
% 11.43/1.98  --splitting_cvd_svl                     false
% 11.43/1.98  --splitting_nvd                         32
% 11.43/1.98  --sub_typing                            true
% 11.43/1.98  --prep_gs_sim                           true
% 11.43/1.98  --prep_unflatten                        true
% 11.43/1.98  --prep_res_sim                          true
% 11.43/1.98  --prep_upred                            true
% 11.43/1.98  --prep_sem_filter                       exhaustive
% 11.43/1.98  --prep_sem_filter_out                   false
% 11.43/1.98  --pred_elim                             true
% 11.43/1.98  --res_sim_input                         true
% 11.43/1.98  --eq_ax_congr_red                       true
% 11.43/1.98  --pure_diseq_elim                       true
% 11.43/1.98  --brand_transform                       false
% 11.43/1.98  --non_eq_to_eq                          false
% 11.43/1.98  --prep_def_merge                        true
% 11.43/1.98  --prep_def_merge_prop_impl              false
% 11.43/1.98  --prep_def_merge_mbd                    true
% 11.43/1.98  --prep_def_merge_tr_red                 false
% 11.43/1.98  --prep_def_merge_tr_cl                  false
% 11.43/1.98  --smt_preprocessing                     true
% 11.43/1.98  --smt_ac_axioms                         fast
% 11.43/1.98  --preprocessed_out                      false
% 11.43/1.98  --preprocessed_stats                    false
% 11.43/1.98  
% 11.43/1.98  ------ Abstraction refinement Options
% 11.43/1.98  
% 11.43/1.98  --abstr_ref                             []
% 11.43/1.98  --abstr_ref_prep                        false
% 11.43/1.98  --abstr_ref_until_sat                   false
% 11.43/1.98  --abstr_ref_sig_restrict                funpre
% 11.43/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.43/1.98  --abstr_ref_under                       []
% 11.43/1.98  
% 11.43/1.98  ------ SAT Options
% 11.43/1.98  
% 11.43/1.98  --sat_mode                              false
% 11.43/1.98  --sat_fm_restart_options                ""
% 11.43/1.98  --sat_gr_def                            false
% 11.43/1.98  --sat_epr_types                         true
% 11.43/1.98  --sat_non_cyclic_types                  false
% 11.43/1.98  --sat_finite_models                     false
% 11.43/1.98  --sat_fm_lemmas                         false
% 11.43/1.98  --sat_fm_prep                           false
% 11.43/1.98  --sat_fm_uc_incr                        true
% 11.43/1.98  --sat_out_model                         small
% 11.43/1.98  --sat_out_clauses                       false
% 11.43/1.98  
% 11.43/1.98  ------ QBF Options
% 11.43/1.98  
% 11.43/1.98  --qbf_mode                              false
% 11.43/1.98  --qbf_elim_univ                         false
% 11.43/1.98  --qbf_dom_inst                          none
% 11.43/1.98  --qbf_dom_pre_inst                      false
% 11.43/1.98  --qbf_sk_in                             false
% 11.43/1.98  --qbf_pred_elim                         true
% 11.43/1.98  --qbf_split                             512
% 11.43/1.98  
% 11.43/1.98  ------ BMC1 Options
% 11.43/1.98  
% 11.43/1.98  --bmc1_incremental                      false
% 11.43/1.98  --bmc1_axioms                           reachable_all
% 11.43/1.98  --bmc1_min_bound                        0
% 11.43/1.98  --bmc1_max_bound                        -1
% 11.43/1.98  --bmc1_max_bound_default                -1
% 11.43/1.98  --bmc1_symbol_reachability              true
% 11.43/1.98  --bmc1_property_lemmas                  false
% 11.43/1.98  --bmc1_k_induction                      false
% 11.43/1.98  --bmc1_non_equiv_states                 false
% 11.43/1.98  --bmc1_deadlock                         false
% 11.43/1.98  --bmc1_ucm                              false
% 11.43/1.98  --bmc1_add_unsat_core                   none
% 11.43/1.98  --bmc1_unsat_core_children              false
% 11.43/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.43/1.98  --bmc1_out_stat                         full
% 11.43/1.98  --bmc1_ground_init                      false
% 11.43/1.98  --bmc1_pre_inst_next_state              false
% 11.43/1.98  --bmc1_pre_inst_state                   false
% 11.43/1.98  --bmc1_pre_inst_reach_state             false
% 11.43/1.98  --bmc1_out_unsat_core                   false
% 11.43/1.98  --bmc1_aig_witness_out                  false
% 11.43/1.98  --bmc1_verbose                          false
% 11.43/1.98  --bmc1_dump_clauses_tptp                false
% 11.43/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.43/1.98  --bmc1_dump_file                        -
% 11.43/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.43/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.43/1.98  --bmc1_ucm_extend_mode                  1
% 11.43/1.98  --bmc1_ucm_init_mode                    2
% 11.43/1.98  --bmc1_ucm_cone_mode                    none
% 11.43/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.43/1.98  --bmc1_ucm_relax_model                  4
% 11.43/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.43/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.43/1.98  --bmc1_ucm_layered_model                none
% 11.43/1.98  --bmc1_ucm_max_lemma_size               10
% 11.43/1.98  
% 11.43/1.98  ------ AIG Options
% 11.43/1.98  
% 11.43/1.98  --aig_mode                              false
% 11.43/1.98  
% 11.43/1.98  ------ Instantiation Options
% 11.43/1.98  
% 11.43/1.98  --instantiation_flag                    true
% 11.43/1.98  --inst_sos_flag                         true
% 11.43/1.98  --inst_sos_phase                        true
% 11.43/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.43/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.43/1.98  --inst_lit_sel_side                     none
% 11.43/1.98  --inst_solver_per_active                1400
% 11.43/1.98  --inst_solver_calls_frac                1.
% 11.43/1.98  --inst_passive_queue_type               priority_queues
% 11.43/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.43/1.98  --inst_passive_queues_freq              [25;2]
% 11.43/1.98  --inst_dismatching                      true
% 11.43/1.98  --inst_eager_unprocessed_to_passive     true
% 11.43/1.98  --inst_prop_sim_given                   true
% 11.43/1.98  --inst_prop_sim_new                     false
% 11.43/1.98  --inst_subs_new                         false
% 11.43/1.98  --inst_eq_res_simp                      false
% 11.43/1.98  --inst_subs_given                       false
% 11.43/1.98  --inst_orphan_elimination               true
% 11.43/1.98  --inst_learning_loop_flag               true
% 11.43/1.98  --inst_learning_start                   3000
% 11.43/1.98  --inst_learning_factor                  2
% 11.43/1.98  --inst_start_prop_sim_after_learn       3
% 11.43/1.98  --inst_sel_renew                        solver
% 11.43/1.98  --inst_lit_activity_flag                true
% 11.43/1.98  --inst_restr_to_given                   false
% 11.43/1.98  --inst_activity_threshold               500
% 11.43/1.98  --inst_out_proof                        true
% 11.43/1.98  
% 11.43/1.98  ------ Resolution Options
% 11.43/1.98  
% 11.43/1.98  --resolution_flag                       false
% 11.43/1.98  --res_lit_sel                           adaptive
% 11.43/1.98  --res_lit_sel_side                      none
% 11.43/1.98  --res_ordering                          kbo
% 11.43/1.98  --res_to_prop_solver                    active
% 11.43/1.98  --res_prop_simpl_new                    false
% 11.43/1.98  --res_prop_simpl_given                  true
% 11.43/1.98  --res_passive_queue_type                priority_queues
% 11.43/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.43/1.98  --res_passive_queues_freq               [15;5]
% 11.43/1.98  --res_forward_subs                      full
% 11.43/1.98  --res_backward_subs                     full
% 11.43/1.98  --res_forward_subs_resolution           true
% 11.43/1.98  --res_backward_subs_resolution          true
% 11.43/1.98  --res_orphan_elimination                true
% 11.43/1.98  --res_time_limit                        2.
% 11.43/1.98  --res_out_proof                         true
% 11.43/1.98  
% 11.43/1.98  ------ Superposition Options
% 11.43/1.98  
% 11.43/1.98  --superposition_flag                    true
% 11.43/1.98  --sup_passive_queue_type                priority_queues
% 11.43/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.43/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.43/1.98  --demod_completeness_check              fast
% 11.43/1.98  --demod_use_ground                      true
% 11.43/1.98  --sup_to_prop_solver                    passive
% 11.43/1.98  --sup_prop_simpl_new                    true
% 11.43/1.98  --sup_prop_simpl_given                  true
% 11.43/1.98  --sup_fun_splitting                     true
% 11.43/1.98  --sup_smt_interval                      50000
% 11.43/1.98  
% 11.43/1.98  ------ Superposition Simplification Setup
% 11.43/1.98  
% 11.43/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.43/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.43/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.43/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.43/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.43/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.43/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.43/1.98  --sup_immed_triv                        [TrivRules]
% 11.43/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.98  --sup_immed_bw_main                     []
% 11.43/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.43/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.43/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.98  --sup_input_bw                          []
% 11.43/1.98  
% 11.43/1.98  ------ Combination Options
% 11.43/1.98  
% 11.43/1.98  --comb_res_mult                         3
% 11.43/1.98  --comb_sup_mult                         2
% 11.43/1.98  --comb_inst_mult                        10
% 11.43/1.98  
% 11.43/1.98  ------ Debug Options
% 11.43/1.98  
% 11.43/1.98  --dbg_backtrace                         false
% 11.43/1.98  --dbg_dump_prop_clauses                 false
% 11.43/1.98  --dbg_dump_prop_clauses_file            -
% 11.43/1.98  --dbg_out_stat                          false
% 11.43/1.98  
% 11.43/1.98  
% 11.43/1.98  
% 11.43/1.98  
% 11.43/1.98  ------ Proving...
% 11.43/1.98  
% 11.43/1.98  
% 11.43/1.98  % SZS status Theorem for theBenchmark.p
% 11.43/1.98  
% 11.43/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.43/1.98  
% 11.43/1.98  fof(f33,conjecture,(
% 11.43/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f34,negated_conjecture,(
% 11.43/1.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.43/1.98    inference(negated_conjecture,[],[f33])).
% 11.43/1.98  
% 11.43/1.98  fof(f73,plain,(
% 11.43/1.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.43/1.98    inference(ennf_transformation,[],[f34])).
% 11.43/1.98  
% 11.43/1.98  fof(f74,plain,(
% 11.43/1.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.43/1.98    inference(flattening,[],[f73])).
% 11.43/1.98  
% 11.43/1.98  fof(f79,plain,(
% 11.43/1.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 11.43/1.98    introduced(choice_axiom,[])).
% 11.43/1.98  
% 11.43/1.98  fof(f78,plain,(
% 11.43/1.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 11.43/1.98    introduced(choice_axiom,[])).
% 11.43/1.98  
% 11.43/1.98  fof(f80,plain,(
% 11.43/1.98    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 11.43/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f74,f79,f78])).
% 11.43/1.98  
% 11.43/1.98  fof(f130,plain,(
% 11.43/1.98    v1_funct_1(sK3)),
% 11.43/1.98    inference(cnf_transformation,[],[f80])).
% 11.43/1.98  
% 11.43/1.98  fof(f13,axiom,(
% 11.43/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f44,plain,(
% 11.43/1.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.43/1.98    inference(ennf_transformation,[],[f13])).
% 11.43/1.98  
% 11.43/1.98  fof(f45,plain,(
% 11.43/1.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.43/1.98    inference(flattening,[],[f44])).
% 11.43/1.98  
% 11.43/1.98  fof(f94,plain,(
% 11.43/1.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.43/1.98    inference(cnf_transformation,[],[f45])).
% 11.43/1.98  
% 11.43/1.98  fof(f6,axiom,(
% 11.43/1.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f86,plain,(
% 11.43/1.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.43/1.98    inference(cnf_transformation,[],[f6])).
% 11.43/1.98  
% 11.43/1.98  fof(f132,plain,(
% 11.43/1.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.43/1.98    inference(cnf_transformation,[],[f80])).
% 11.43/1.98  
% 11.43/1.98  fof(f5,axiom,(
% 11.43/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f38,plain,(
% 11.43/1.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.43/1.98    inference(ennf_transformation,[],[f5])).
% 11.43/1.98  
% 11.43/1.98  fof(f85,plain,(
% 11.43/1.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.43/1.98    inference(cnf_transformation,[],[f38])).
% 11.43/1.98  
% 11.43/1.98  fof(f9,axiom,(
% 11.43/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f41,plain,(
% 11.43/1.98    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.43/1.98    inference(ennf_transformation,[],[f9])).
% 11.43/1.98  
% 11.43/1.98  fof(f89,plain,(
% 11.43/1.98    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.43/1.98    inference(cnf_transformation,[],[f41])).
% 11.43/1.98  
% 11.43/1.98  fof(f136,plain,(
% 11.43/1.98    k2_relset_1(sK1,sK2,sK3) = sK2),
% 11.43/1.98    inference(cnf_transformation,[],[f80])).
% 11.43/1.98  
% 11.43/1.98  fof(f31,axiom,(
% 11.43/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f69,plain,(
% 11.43/1.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.43/1.98    inference(ennf_transformation,[],[f31])).
% 11.43/1.98  
% 11.43/1.98  fof(f70,plain,(
% 11.43/1.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.43/1.98    inference(flattening,[],[f69])).
% 11.43/1.98  
% 11.43/1.98  fof(f126,plain,(
% 11.43/1.98    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.43/1.98    inference(cnf_transformation,[],[f70])).
% 11.43/1.98  
% 11.43/1.98  fof(f1,axiom,(
% 11.43/1.98    v1_xboole_0(o_0_0_xboole_0)),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f81,plain,(
% 11.43/1.98    v1_xboole_0(o_0_0_xboole_0)),
% 11.43/1.98    inference(cnf_transformation,[],[f1])).
% 11.43/1.98  
% 11.43/1.98  fof(f2,axiom,(
% 11.43/1.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f36,plain,(
% 11.43/1.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 11.43/1.98    inference(ennf_transformation,[],[f2])).
% 11.43/1.98  
% 11.43/1.98  fof(f82,plain,(
% 11.43/1.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 11.43/1.98    inference(cnf_transformation,[],[f36])).
% 11.43/1.98  
% 11.43/1.98  fof(f131,plain,(
% 11.43/1.98    v1_funct_2(sK3,sK1,sK2)),
% 11.43/1.98    inference(cnf_transformation,[],[f80])).
% 11.43/1.98  
% 11.43/1.98  fof(f138,plain,(
% 11.43/1.98    v2_funct_1(sK3)),
% 11.43/1.98    inference(cnf_transformation,[],[f80])).
% 11.43/1.98  
% 11.43/1.98  fof(f140,plain,(
% 11.43/1.98    k1_xboole_0 != sK2),
% 11.43/1.98    inference(cnf_transformation,[],[f80])).
% 11.43/1.98  
% 11.43/1.98  fof(f125,plain,(
% 11.43/1.98    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.43/1.98    inference(cnf_transformation,[],[f70])).
% 11.43/1.98  
% 11.43/1.98  fof(f11,axiom,(
% 11.43/1.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f42,plain,(
% 11.43/1.98    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 11.43/1.98    inference(ennf_transformation,[],[f11])).
% 11.43/1.98  
% 11.43/1.98  fof(f92,plain,(
% 11.43/1.98    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.43/1.98    inference(cnf_transformation,[],[f42])).
% 11.43/1.98  
% 11.43/1.98  fof(f28,axiom,(
% 11.43/1.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.43/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.98  
% 11.43/1.98  fof(f119,plain,(
% 11.43/1.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.43/1.98    inference(cnf_transformation,[],[f28])).
% 11.43/1.98  
% 11.43/1.98  fof(f144,plain,(
% 11.43/1.98    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.43/1.98    inference(definition_unfolding,[],[f92,f119])).
% 11.43/1.98  
% 11.43/1.98  fof(f18,axiom,(
% 11.43/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f50,plain,(
% 11.43/1.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.43/1.99    inference(ennf_transformation,[],[f18])).
% 11.43/1.99  
% 11.43/1.99  fof(f51,plain,(
% 11.43/1.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.43/1.99    inference(flattening,[],[f50])).
% 11.43/1.99  
% 11.43/1.99  fof(f104,plain,(
% 11.43/1.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f51])).
% 11.43/1.99  
% 11.43/1.99  fof(f23,axiom,(
% 11.43/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f58,plain,(
% 11.43/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.43/1.99    inference(ennf_transformation,[],[f23])).
% 11.43/1.99  
% 11.43/1.99  fof(f112,plain,(
% 11.43/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f58])).
% 11.43/1.99  
% 11.43/1.99  fof(f135,plain,(
% 11.43/1.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 11.43/1.99    inference(cnf_transformation,[],[f80])).
% 11.43/1.99  
% 11.43/1.99  fof(f27,axiom,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f63,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.43/1.99    inference(ennf_transformation,[],[f27])).
% 11.43/1.99  
% 11.43/1.99  fof(f64,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.43/1.99    inference(flattening,[],[f63])).
% 11.43/1.99  
% 11.43/1.99  fof(f118,plain,(
% 11.43/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f64])).
% 11.43/1.99  
% 11.43/1.99  fof(f133,plain,(
% 11.43/1.99    v1_funct_1(sK4)),
% 11.43/1.99    inference(cnf_transformation,[],[f80])).
% 11.43/1.99  
% 11.43/1.99  fof(f24,axiom,(
% 11.43/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f59,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.43/1.99    inference(ennf_transformation,[],[f24])).
% 11.43/1.99  
% 11.43/1.99  fof(f60,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.43/1.99    inference(flattening,[],[f59])).
% 11.43/1.99  
% 11.43/1.99  fof(f77,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.43/1.99    inference(nnf_transformation,[],[f60])).
% 11.43/1.99  
% 11.43/1.99  fof(f113,plain,(
% 11.43/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f77])).
% 11.43/1.99  
% 11.43/1.99  fof(f137,plain,(
% 11.43/1.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 11.43/1.99    inference(cnf_transformation,[],[f80])).
% 11.43/1.99  
% 11.43/1.99  fof(f26,axiom,(
% 11.43/1.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f35,plain,(
% 11.43/1.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.43/1.99    inference(pure_predicate_removal,[],[f26])).
% 11.43/1.99  
% 11.43/1.99  fof(f117,plain,(
% 11.43/1.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f35])).
% 11.43/1.99  
% 11.43/1.99  fof(f25,axiom,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f61,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.43/1.99    inference(ennf_transformation,[],[f25])).
% 11.43/1.99  
% 11.43/1.99  fof(f62,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.43/1.99    inference(flattening,[],[f61])).
% 11.43/1.99  
% 11.43/1.99  fof(f116,plain,(
% 11.43/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f62])).
% 11.43/1.99  
% 11.43/1.99  fof(f29,axiom,(
% 11.43/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f65,plain,(
% 11.43/1.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.43/1.99    inference(ennf_transformation,[],[f29])).
% 11.43/1.99  
% 11.43/1.99  fof(f66,plain,(
% 11.43/1.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.43/1.99    inference(flattening,[],[f65])).
% 11.43/1.99  
% 11.43/1.99  fof(f120,plain,(
% 11.43/1.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f66])).
% 11.43/1.99  
% 11.43/1.99  fof(f134,plain,(
% 11.43/1.99    v1_funct_2(sK4,sK2,sK1)),
% 11.43/1.99    inference(cnf_transformation,[],[f80])).
% 11.43/1.99  
% 11.43/1.99  fof(f139,plain,(
% 11.43/1.99    k1_xboole_0 != sK1),
% 11.43/1.99    inference(cnf_transformation,[],[f80])).
% 11.43/1.99  
% 11.43/1.99  fof(f15,axiom,(
% 11.43/1.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f99,plain,(
% 11.43/1.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f15])).
% 11.43/1.99  
% 11.43/1.99  fof(f148,plain,(
% 11.43/1.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.43/1.99    inference(definition_unfolding,[],[f99,f119])).
% 11.43/1.99  
% 11.43/1.99  fof(f30,axiom,(
% 11.43/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f67,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.43/1.99    inference(ennf_transformation,[],[f30])).
% 11.43/1.99  
% 11.43/1.99  fof(f68,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.43/1.99    inference(flattening,[],[f67])).
% 11.43/1.99  
% 11.43/1.99  fof(f123,plain,(
% 11.43/1.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f68])).
% 11.43/1.99  
% 11.43/1.99  fof(f20,axiom,(
% 11.43/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.43/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f54,plain,(
% 11.43/1.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.43/1.99    inference(ennf_transformation,[],[f20])).
% 11.43/1.99  
% 11.43/1.99  fof(f55,plain,(
% 11.43/1.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.43/1.99    inference(flattening,[],[f54])).
% 11.43/1.99  
% 11.43/1.99  fof(f108,plain,(
% 11.43/1.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f55])).
% 11.43/1.99  
% 11.43/1.99  fof(f151,plain,(
% 11.43/1.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(definition_unfolding,[],[f108,f119])).
% 11.43/1.99  
% 11.43/1.99  fof(f141,plain,(
% 11.43/1.99    k2_funct_1(sK3) != sK4),
% 11.43/1.99    inference(cnf_transformation,[],[f80])).
% 11.43/1.99  
% 11.43/1.99  cnf(c_59,negated_conjecture,
% 11.43/1.99      ( v1_funct_1(sK3) ),
% 11.43/1.99      inference(cnf_transformation,[],[f130]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1764,plain,
% 11.43/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_14,plain,
% 11.43/1.99      ( ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X0)
% 11.43/1.99      | v1_relat_1(k2_funct_1(X0)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1796,plain,
% 11.43/1.99      ( v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5,plain,
% 11.43/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1803,plain,
% 11.43/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_57,negated_conjecture,
% 11.43/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.43/1.99      inference(cnf_transformation,[],[f132]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1766,plain,
% 11.43/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.43/1.99      | ~ v1_relat_1(X1)
% 11.43/1.99      | v1_relat_1(X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1804,plain,
% 11.43/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.43/1.99      | v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4965,plain,
% 11.43/1.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 11.43/1.99      | v1_relat_1(sK3) = iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1766,c_1804]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5268,plain,
% 11.43/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1803,c_4965]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8,plain,
% 11.43/1.99      ( ~ v1_relat_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X1)
% 11.43/1.99      | ~ v1_relat_1(X2)
% 11.43/1.99      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1800,plain,
% 11.43/1.99      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_7747,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1796,c_1800]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21012,plain,
% 11.43/1.99      ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1764,c_7747]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21506,plain,
% 11.43/1.99      ( v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1)) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_21012,c_5268]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21507,plain,
% 11.43/1.99      ( k5_relat_1(k5_relat_1(k2_funct_1(sK3),X0),X1) = k5_relat_1(k2_funct_1(sK3),k5_relat_1(X0,X1))
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.43/1.99      inference(renaming,[status(thm)],[c_21506]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21515,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK3),sK3),X0)
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_5268,c_21507]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_53,negated_conjecture,
% 11.43/1.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 11.43/1.99      inference(cnf_transformation,[],[f136]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_43,plain,
% 11.43/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ v2_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | k2_relset_1(X1,X2,X0) != X2
% 11.43/1.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 11.43/1.99      | k1_xboole_0 = X2 ),
% 11.43/1.99      inference(cnf_transformation,[],[f126]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1774,plain,
% 11.43/1.99      ( k2_relset_1(X0,X1,X2) != X1
% 11.43/1.99      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 11.43/1.99      | k1_xboole_0 = X1
% 11.43/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v2_funct_1(X2) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_0,plain,
% 11.43/1.99      ( v1_xboole_0(o_0_0_xboole_0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1808,plain,
% 11.43/1.99      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1,plain,
% 11.43/1.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 11.43/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1807,plain,
% 11.43/1.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3416,plain,
% 11.43/1.99      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1808,c_1807]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5765,plain,
% 11.43/1.99      ( k2_relset_1(X0,X1,X2) != X1
% 11.43/1.99      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 11.43/1.99      | o_0_0_xboole_0 = X1
% 11.43/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v2_funct_1(X2) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.43/1.99      inference(demodulation,[status(thm)],[c_1774,c_3416]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5769,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 11.43/1.99      | sK2 = o_0_0_xboole_0
% 11.43/1.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.43/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.43/1.99      | v2_funct_1(sK3) != iProver_top
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_53,c_5765]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_58,negated_conjecture,
% 11.43/1.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 11.43/1.99      inference(cnf_transformation,[],[f131]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_51,negated_conjecture,
% 11.43/1.99      ( v2_funct_1(sK3) ),
% 11.43/1.99      inference(cnf_transformation,[],[f138]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_49,negated_conjecture,
% 11.43/1.99      ( k1_xboole_0 != sK2 ),
% 11.43/1.99      inference(cnf_transformation,[],[f140]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1879,plain,
% 11.43/1.99      ( ~ v1_funct_2(X0,X1,sK2)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 11.43/1.99      | ~ v2_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | k2_relset_1(X1,sK2,X0) != sK2
% 11.43/1.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK2)
% 11.43/1.99      | k1_xboole_0 = sK2 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_43]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1974,plain,
% 11.43/1.99      ( ~ v1_funct_2(sK3,X0,sK2)
% 11.43/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 11.43/1.99      | ~ v2_funct_1(sK3)
% 11.43/1.99      | ~ v1_funct_1(sK3)
% 11.43/1.99      | k2_relset_1(X0,sK2,sK3) != sK2
% 11.43/1.99      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 11.43/1.99      | k1_xboole_0 = sK2 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_1879]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2157,plain,
% 11.43/1.99      ( ~ v1_funct_2(sK3,sK1,sK2)
% 11.43/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.43/1.99      | ~ v2_funct_1(sK3)
% 11.43/1.99      | ~ v1_funct_1(sK3)
% 11.43/1.99      | k2_relset_1(sK1,sK2,sK3) != sK2
% 11.43/1.99      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
% 11.43/1.99      | k1_xboole_0 = sK2 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_7012,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_5769,c_59,c_58,c_57,c_53,c_51,c_49,c_2157]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21520,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK2),X0)
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_21515,c_7012]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21659,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK2),k2_funct_1(X0))
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1796,c_21520]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_23551,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK2),k2_funct_1(sK3))
% 11.43/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1764,c_21659]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_44,plain,
% 11.43/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ v2_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | k2_relset_1(X1,X2,X0) != X2
% 11.43/1.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.43/1.99      | k1_xboole_0 = X2 ),
% 11.43/1.99      inference(cnf_transformation,[],[f125]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1773,plain,
% 11.43/1.99      ( k2_relset_1(X0,X1,X2) != X1
% 11.43/1.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 11.43/1.99      | k1_xboole_0 = X1
% 11.43/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v2_funct_1(X2) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4971,plain,
% 11.43/1.99      ( k2_relset_1(X0,X1,X2) != X1
% 11.43/1.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 11.43/1.99      | o_0_0_xboole_0 = X1
% 11.43/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v2_funct_1(X2) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.43/1.99      inference(demodulation,[status(thm)],[c_1773,c_3416]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4975,plain,
% 11.43/1.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.43/1.99      | sK2 = o_0_0_xboole_0
% 11.43/1.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.43/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.43/1.99      | v2_funct_1(sK3) != iProver_top
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_53,c_4971]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1880,plain,
% 11.43/1.99      ( ~ v1_funct_2(X0,X1,sK2)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 11.43/1.99      | ~ v2_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | k2_relset_1(X1,sK2,X0) != sK2
% 11.43/1.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.43/1.99      | k1_xboole_0 = sK2 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_44]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2010,plain,
% 11.43/1.99      ( ~ v1_funct_2(sK3,X0,sK2)
% 11.43/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 11.43/1.99      | ~ v2_funct_1(sK3)
% 11.43/1.99      | ~ v1_funct_1(sK3)
% 11.43/1.99      | k2_relset_1(X0,sK2,sK3) != sK2
% 11.43/1.99      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
% 11.43/1.99      | k1_xboole_0 = sK2 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_1880]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2170,plain,
% 11.43/1.99      ( ~ v1_funct_2(sK3,sK1,sK2)
% 11.43/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.43/1.99      | ~ v2_funct_1(sK3)
% 11.43/1.99      | ~ v1_funct_1(sK3)
% 11.43/1.99      | k2_relset_1(sK1,sK2,sK3) != sK2
% 11.43/1.99      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.43/1.99      | k1_xboole_0 = sK2 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_2010]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5211,plain,
% 11.43/1.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_4975,c_59,c_58,c_57,c_53,c_51,c_49,c_2170]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_11,plain,
% 11.43/1.99      ( ~ v1_relat_1(X0)
% 11.43/1.99      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 11.43/1.99      inference(cnf_transformation,[],[f144]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1799,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4380,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1796,c_1799]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_11550,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3)
% 11.43/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1764,c_4380]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1770,plain,
% 11.43/1.99      ( v2_funct_1(sK3) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_24,plain,
% 11.43/1.99      ( ~ v2_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X0)
% 11.43/1.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1789,plain,
% 11.43/1.99      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 11.43/1.99      | v2_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5160,plain,
% 11.43/1.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top
% 11.43/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1770,c_1789]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_31,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1783,plain,
% 11.43/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3975,plain,
% 11.43/1.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1766,c_1783]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3976,plain,
% 11.43/1.99      ( k2_relat_1(sK3) = sK2 ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_3975,c_53]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5161,plain,
% 11.43/1.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top
% 11.43/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_5160,c_3976]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_60,plain,
% 11.43/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5271,plain,
% 11.43/1.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_5161,c_60,c_5268]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_11553,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(sK2),k2_funct_1(sK3)) = k2_funct_1(sK3)
% 11.43/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_11550,c_5271]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_12012,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(sK2),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_11553,c_5268]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_54,negated_conjecture,
% 11.43/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.43/1.99      inference(cnf_transformation,[],[f135]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1769,plain,
% 11.43/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4964,plain,
% 11.43/1.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 11.43/1.99      | v1_relat_1(sK4) = iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1769,c_1804]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5214,plain,
% 11.43/1.99      ( v1_relat_1(sK4) = iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1803,c_4964]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21662,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK3),k5_relat_1(sK3,sK4)) = k5_relat_1(k6_partfun1(sK2),sK4) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_5214,c_21520]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_37,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X3)
% 11.43/1.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f118]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1779,plain,
% 11.43/1.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.43/1.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.43/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v1_funct_1(X5) != iProver_top
% 11.43/1.99      | v1_funct_1(X4) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8220,plain,
% 11.43/1.99      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top
% 11.43/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1769,c_1779]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_56,negated_conjecture,
% 11.43/1.99      ( v1_funct_1(sK4) ),
% 11.43/1.99      inference(cnf_transformation,[],[f133]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_63,plain,
% 11.43/1.99      ( v1_funct_1(sK4) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8377,plain,
% 11.43/1.99      ( v1_funct_1(X2) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_8220,c_63]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8378,plain,
% 11.43/1.99      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.43/1.99      inference(renaming,[status(thm)],[c_8377]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8387,plain,
% 11.43/1.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_1766,c_8378]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_33,plain,
% 11.43/1.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.43/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.43/1.99      | X3 = X2 ),
% 11.43/1.99      inference(cnf_transformation,[],[f113]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_52,negated_conjecture,
% 11.43/1.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f137]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_617,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | X3 = X0
% 11.43/1.99      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 11.43/1.99      | k6_partfun1(sK1) != X3
% 11.43/1.99      | sK1 != X2
% 11.43/1.99      | sK1 != X1 ),
% 11.43/1.99      inference(resolution_lifted,[status(thm)],[c_33,c_52]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_618,plain,
% 11.43/1.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.43/1.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.43/1.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.43/1.99      inference(unflattening,[status(thm)],[c_617]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_36,plain,
% 11.43/1.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.43/1.99      inference(cnf_transformation,[],[f117]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_626,plain,
% 11.43/1.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.43/1.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.43/1.99      inference(forward_subsumption_resolution,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_618,c_36]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1762,plain,
% 11.43/1.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.43/1.99      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_34,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.43/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X3) ),
% 11.43/1.99      inference(cnf_transformation,[],[f116]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2280,plain,
% 11.43/1.99      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.43/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.43/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.43/1.99      | ~ v1_funct_1(sK4)
% 11.43/1.99      | ~ v1_funct_1(sK3) ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_34]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2853,plain,
% 11.43/1.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_1762,c_59,c_57,c_56,c_54,c_626,c_2280]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8390,plain,
% 11.43/1.99      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_8387,c_2853]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_10266,plain,
% 11.43/1.99      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_8390,c_60]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_38,plain,
% 11.43/1.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.43/1.99      | ~ v1_funct_2(X2,X0,X1)
% 11.43/1.99      | ~ v1_funct_2(X3,X1,X0)
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.43/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.43/1.99      | ~ v1_funct_1(X2)
% 11.43/1.99      | ~ v1_funct_1(X3)
% 11.43/1.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.43/1.99      inference(cnf_transformation,[],[f120]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_630,plain,
% 11.43/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.43/1.99      | ~ v1_funct_2(X3,X2,X1)
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X3)
% 11.43/1.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.43/1.99      | k2_relset_1(X1,X2,X0) = X2
% 11.43/1.99      | k6_partfun1(X2) != k6_partfun1(sK1)
% 11.43/1.99      | sK1 != X2 ),
% 11.43/1.99      inference(resolution_lifted,[status(thm)],[c_38,c_52]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_631,plain,
% 11.43/1.99      ( ~ v1_funct_2(X0,X1,sK1)
% 11.43/1.99      | ~ v1_funct_2(X2,sK1,X1)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.43/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X2)
% 11.43/1.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.43/1.99      | k2_relset_1(X1,sK1,X0) = sK1
% 11.43/1.99      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 11.43/1.99      inference(unflattening,[status(thm)],[c_630]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_733,plain,
% 11.43/1.99      ( ~ v1_funct_2(X0,X1,sK1)
% 11.43/1.99      | ~ v1_funct_2(X2,sK1,X1)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.43/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X2)
% 11.43/1.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.43/1.99      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 11.43/1.99      inference(equality_resolution_simp,[status(thm)],[c_631]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1761,plain,
% 11.43/1.99      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.43/1.99      | k2_relset_1(X0,sK1,X2) = sK1
% 11.43/1.99      | v1_funct_2(X2,X0,sK1) != iProver_top
% 11.43/1.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.43/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top
% 11.43/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2333,plain,
% 11.43/1.99      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 11.43/1.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.43/1.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.43/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.43/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.43/1.99      | v1_funct_1(sK4) != iProver_top
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.43/1.99      inference(equality_resolution,[status(thm)],[c_1761]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_61,plain,
% 11.43/1.99      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_62,plain,
% 11.43/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_55,negated_conjecture,
% 11.43/1.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 11.43/1.99      inference(cnf_transformation,[],[f134]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_64,plain,
% 11.43/1.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_65,plain,
% 11.43/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2860,plain,
% 11.43/1.99      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_2333,c_60,c_61,c_62,c_63,c_64,c_65]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4976,plain,
% 11.43/1.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 11.43/1.99      | sK1 = o_0_0_xboole_0
% 11.43/1.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.43/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.43/1.99      | v2_funct_1(sK4) != iProver_top
% 11.43/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2860,c_4971]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_50,negated_conjecture,
% 11.43/1.99      ( k1_xboole_0 != sK1 ),
% 11.43/1.99      inference(cnf_transformation,[],[f139]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1897,plain,
% 11.43/1.99      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1006,plain,
% 11.43/1.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 11.43/1.99      theory(equality) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1947,plain,
% 11.43/1.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_1006]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2302,plain,
% 11.43/1.99      ( v1_xboole_0(sK1)
% 11.43/1.99      | ~ v1_xboole_0(o_0_0_xboole_0)
% 11.43/1.99      | sK1 != o_0_0_xboole_0 ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_1947]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_17,plain,
% 11.43/1.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f148]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3679,plain,
% 11.43/1.99      ( v2_funct_1(k6_partfun1(sK1)) ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3680,plain,
% 11.43/1.99      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_3679]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_40,plain,
% 11.43/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.43/1.99      | ~ v1_funct_2(X3,X4,X1)
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | v2_funct_1(X0)
% 11.43/1.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X3)
% 11.43/1.99      | k2_relset_1(X4,X1,X3) != X1
% 11.43/1.99      | k1_xboole_0 = X2 ),
% 11.43/1.99      inference(cnf_transformation,[],[f123]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1777,plain,
% 11.43/1.99      ( k2_relset_1(X0,X1,X2) != X1
% 11.43/1.99      | k1_xboole_0 = X3
% 11.43/1.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 11.43/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.43/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v2_funct_1(X4) = iProver_top
% 11.43/1.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 11.43/1.99      | v1_funct_1(X4) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_9507,plain,
% 11.43/1.99      ( k2_relset_1(X0,X1,X2) != X1
% 11.43/1.99      | o_0_0_xboole_0 = X3
% 11.43/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.43/1.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 11.43/1.99      | v2_funct_1(X4) = iProver_top
% 11.43/1.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top
% 11.43/1.99      | v1_funct_1(X4) != iProver_top ),
% 11.43/1.99      inference(demodulation,[status(thm)],[c_1777,c_3416]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_9509,plain,
% 11.43/1.99      ( o_0_0_xboole_0 = X0
% 11.43/1.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.43/1.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.43/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 11.43/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.43/1.99      | v2_funct_1(X1) = iProver_top
% 11.43/1.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 11.43/1.99      | v1_funct_1(X1) != iProver_top
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_53,c_9507]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_9819,plain,
% 11.43/1.99      ( v1_funct_1(X1) != iProver_top
% 11.43/1.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 11.43/1.99      | v2_funct_1(X1) = iProver_top
% 11.43/1.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.43/1.99      | o_0_0_xboole_0 = X0
% 11.43/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_9509,c_60,c_61,c_62]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_9820,plain,
% 11.43/1.99      ( o_0_0_xboole_0 = X0
% 11.43/1.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.43/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 11.43/1.99      | v2_funct_1(X1) = iProver_top
% 11.43/1.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 11.43/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.43/1.99      inference(renaming,[status(thm)],[c_9819]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_9825,plain,
% 11.43/1.99      ( sK1 = o_0_0_xboole_0
% 11.43/1.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.43/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.43/1.99      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 11.43/1.99      | v2_funct_1(sK4) = iProver_top
% 11.43/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2853,c_9820]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_12236,plain,
% 11.43/1.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_4976,c_63,c_64,c_65,c_50,c_0,c_1897,c_2302,c_3680,
% 11.43/1.99                 c_9825]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_10166,plain,
% 11.43/1.99      ( v2_funct_1(sK4) = iProver_top ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_9825,c_63,c_64,c_65,c_50,c_0,c_1897,c_2302,c_3680]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_28,plain,
% 11.43/1.99      ( ~ v2_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X0)
% 11.43/1.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f151]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_1785,plain,
% 11.43/1.99      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 11.43/1.99      | v2_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_10176,plain,
% 11.43/1.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
% 11.43/1.99      | v1_funct_1(sK4) != iProver_top
% 11.43/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_10166,c_1785]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_10982,plain,
% 11.43/1.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_10176,c_63,c_5214]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_12238,plain,
% 11.43/1.99      ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK2) ),
% 11.43/1.99      inference(demodulation,[status(thm)],[c_12236,c_10982]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5354,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(k1_relat_1(sK4)),sK4) = sK4 ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_5214,c_1799]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_13813,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(sK2),sK4) = sK4 ),
% 11.43/1.99      inference(demodulation,[status(thm)],[c_12238,c_5354]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21668,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK3),k6_partfun1(sK1)) = sK4 ),
% 11.43/1.99      inference(light_normalisation,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_21662,c_10266,c_13813]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_23555,plain,
% 11.43/1.99      ( k2_funct_1(sK3) = sK4 | v1_relat_1(sK3) != iProver_top ),
% 11.43/1.99      inference(light_normalisation,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_23551,c_5211,c_12012,c_21668]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_48,negated_conjecture,
% 11.43/1.99      ( k2_funct_1(sK3) != sK4 ),
% 11.43/1.99      inference(cnf_transformation,[],[f141]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(contradiction,plain,
% 11.43/1.99      ( $false ),
% 11.43/1.99      inference(minisat,[status(thm)],[c_23555,c_5268,c_48]) ).
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.43/1.99  
% 11.43/1.99  ------                               Statistics
% 11.43/1.99  
% 11.43/1.99  ------ General
% 11.43/1.99  
% 11.43/1.99  abstr_ref_over_cycles:                  0
% 11.43/1.99  abstr_ref_under_cycles:                 0
% 11.43/1.99  gc_basic_clause_elim:                   0
% 11.43/1.99  forced_gc_time:                         0
% 11.43/1.99  parsing_time:                           0.011
% 11.43/1.99  unif_index_cands_time:                  0.
% 11.43/1.99  unif_index_add_time:                    0.
% 11.43/1.99  orderings_time:                         0.
% 11.43/1.99  out_proof_time:                         0.016
% 11.43/1.99  total_time:                             1.014
% 11.43/1.99  num_of_symbols:                         56
% 11.43/1.99  num_of_terms:                           38143
% 11.43/1.99  
% 11.43/1.99  ------ Preprocessing
% 11.43/1.99  
% 11.43/1.99  num_of_splits:                          0
% 11.43/1.99  num_of_split_atoms:                     0
% 11.43/1.99  num_of_reused_defs:                     0
% 11.43/1.99  num_eq_ax_congr_red:                    3
% 11.43/1.99  num_of_sem_filtered_clauses:            1
% 11.43/1.99  num_of_subtypes:                        0
% 11.43/1.99  monotx_restored_types:                  0
% 11.43/1.99  sat_num_of_epr_types:                   0
% 11.43/1.99  sat_num_of_non_cyclic_types:            0
% 11.43/1.99  sat_guarded_non_collapsed_types:        0
% 11.43/1.99  num_pure_diseq_elim:                    0
% 11.43/1.99  simp_replaced_by:                       0
% 11.43/1.99  res_preprocessed:                       260
% 11.43/1.99  prep_upred:                             0
% 11.43/1.99  prep_unflattend:                        12
% 11.43/1.99  smt_new_axioms:                         0
% 11.43/1.99  pred_elim_cands:                        6
% 11.43/1.99  pred_elim:                              1
% 11.43/1.99  pred_elim_cl:                           1
% 11.43/1.99  pred_elim_cycles:                       3
% 11.43/1.99  merged_defs:                            0
% 11.43/1.99  merged_defs_ncl:                        0
% 11.43/1.99  bin_hyper_res:                          0
% 11.43/1.99  prep_cycles:                            4
% 11.43/1.99  pred_elim_time:                         0.009
% 11.43/1.99  splitting_time:                         0.
% 11.43/1.99  sem_filter_time:                        0.
% 11.43/1.99  monotx_time:                            0.001
% 11.43/1.99  subtype_inf_time:                       0.
% 11.43/1.99  
% 11.43/1.99  ------ Problem properties
% 11.43/1.99  
% 11.43/1.99  clauses:                                55
% 11.43/1.99  conjectures:                            11
% 11.43/1.99  epr:                                    11
% 11.43/1.99  horn:                                   51
% 11.43/1.99  ground:                                 14
% 11.43/1.99  unary:                                  21
% 11.43/1.99  binary:                                 7
% 11.43/1.99  lits:                                   179
% 11.43/1.99  lits_eq:                                41
% 11.43/1.99  fd_pure:                                0
% 11.43/1.99  fd_pseudo:                              0
% 11.43/1.99  fd_cond:                                5
% 11.43/1.99  fd_pseudo_cond:                         1
% 11.43/1.99  ac_symbols:                             0
% 11.43/1.99  
% 11.43/1.99  ------ Propositional Solver
% 11.43/1.99  
% 11.43/1.99  prop_solver_calls:                      31
% 11.43/1.99  prop_fast_solver_calls:                 2725
% 11.43/1.99  smt_solver_calls:                       0
% 11.43/1.99  smt_fast_solver_calls:                  0
% 11.43/1.99  prop_num_of_clauses:                    10763
% 11.43/1.99  prop_preprocess_simplified:             20701
% 11.43/1.99  prop_fo_subsumed:                       207
% 11.43/1.99  prop_solver_time:                       0.
% 11.43/1.99  smt_solver_time:                        0.
% 11.43/1.99  smt_fast_solver_time:                   0.
% 11.43/1.99  prop_fast_solver_time:                  0.
% 11.43/1.99  prop_unsat_core_time:                   0.001
% 11.43/1.99  
% 11.43/1.99  ------ QBF
% 11.43/1.99  
% 11.43/1.99  qbf_q_res:                              0
% 11.43/1.99  qbf_num_tautologies:                    0
% 11.43/1.99  qbf_prep_cycles:                        0
% 11.43/1.99  
% 11.43/1.99  ------ BMC1
% 11.43/1.99  
% 11.43/1.99  bmc1_current_bound:                     -1
% 11.43/1.99  bmc1_last_solved_bound:                 -1
% 11.43/1.99  bmc1_unsat_core_size:                   -1
% 11.43/1.99  bmc1_unsat_core_parents_size:           -1
% 11.43/1.99  bmc1_merge_next_fun:                    0
% 11.43/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.43/1.99  
% 11.43/1.99  ------ Instantiation
% 11.43/1.99  
% 11.43/1.99  inst_num_of_clauses:                    2778
% 11.43/1.99  inst_num_in_passive:                    720
% 11.43/1.99  inst_num_in_active:                     1462
% 11.43/1.99  inst_num_in_unprocessed:                596
% 11.43/1.99  inst_num_of_loops:                      1600
% 11.43/1.99  inst_num_of_learning_restarts:          0
% 11.43/1.99  inst_num_moves_active_passive:          136
% 11.43/1.99  inst_lit_activity:                      0
% 11.43/1.99  inst_lit_activity_moves:                1
% 11.43/1.99  inst_num_tautologies:                   0
% 11.43/1.99  inst_num_prop_implied:                  0
% 11.43/1.99  inst_num_existing_simplified:           0
% 11.43/1.99  inst_num_eq_res_simplified:             0
% 11.43/1.99  inst_num_child_elim:                    0
% 11.43/1.99  inst_num_of_dismatching_blockings:      1460
% 11.43/1.99  inst_num_of_non_proper_insts:           2729
% 11.43/1.99  inst_num_of_duplicates:                 0
% 11.43/1.99  inst_inst_num_from_inst_to_res:         0
% 11.43/1.99  inst_dismatching_checking_time:         0.
% 11.43/1.99  
% 11.43/1.99  ------ Resolution
% 11.43/1.99  
% 11.43/1.99  res_num_of_clauses:                     0
% 11.43/1.99  res_num_in_passive:                     0
% 11.43/1.99  res_num_in_active:                      0
% 11.43/1.99  res_num_of_loops:                       264
% 11.43/1.99  res_forward_subset_subsumed:            234
% 11.43/1.99  res_backward_subset_subsumed:           0
% 11.43/1.99  res_forward_subsumed:                   0
% 11.43/1.99  res_backward_subsumed:                  0
% 11.43/1.99  res_forward_subsumption_resolution:     2
% 11.43/1.99  res_backward_subsumption_resolution:    0
% 11.43/1.99  res_clause_to_clause_subsumption:       1247
% 11.43/1.99  res_orphan_elimination:                 0
% 11.43/1.99  res_tautology_del:                      85
% 11.43/1.99  res_num_eq_res_simplified:              1
% 11.43/1.99  res_num_sel_changes:                    0
% 11.43/1.99  res_moves_from_active_to_pass:          0
% 11.43/1.99  
% 11.43/1.99  ------ Superposition
% 11.43/1.99  
% 11.43/1.99  sup_time_total:                         0.
% 11.43/1.99  sup_time_generating:                    0.
% 11.43/1.99  sup_time_sim_full:                      0.
% 11.43/1.99  sup_time_sim_immed:                     0.
% 11.43/1.99  
% 11.43/1.99  sup_num_of_clauses:                     604
% 11.43/1.99  sup_num_in_active:                      275
% 11.43/1.99  sup_num_in_passive:                     329
% 11.43/1.99  sup_num_of_loops:                       318
% 11.43/1.99  sup_fw_superposition:                   474
% 11.43/1.99  sup_bw_superposition:                   229
% 11.43/1.99  sup_immediate_simplified:               260
% 11.43/1.99  sup_given_eliminated:                   2
% 11.43/1.99  comparisons_done:                       0
% 11.43/1.99  comparisons_avoided:                    0
% 11.43/1.99  
% 11.43/1.99  ------ Simplifications
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  sim_fw_subset_subsumed:                 18
% 11.43/1.99  sim_bw_subset_subsumed:                 17
% 11.43/1.99  sim_fw_subsumed:                        34
% 11.43/1.99  sim_bw_subsumed:                        2
% 11.43/1.99  sim_fw_subsumption_res:                 0
% 11.43/1.99  sim_bw_subsumption_res:                 0
% 11.43/1.99  sim_tautology_del:                      10
% 11.43/1.99  sim_eq_tautology_del:                   59
% 11.43/1.99  sim_eq_res_simp:                        0
% 11.43/1.99  sim_fw_demodulated:                     26
% 11.43/1.99  sim_bw_demodulated:                     33
% 11.43/1.99  sim_light_normalised:                   242
% 11.43/1.99  sim_joinable_taut:                      0
% 11.43/1.99  sim_joinable_simp:                      0
% 11.43/1.99  sim_ac_normalised:                      0
% 11.43/1.99  sim_smt_subsumption:                    0
% 11.43/1.99  
%------------------------------------------------------------------------------
