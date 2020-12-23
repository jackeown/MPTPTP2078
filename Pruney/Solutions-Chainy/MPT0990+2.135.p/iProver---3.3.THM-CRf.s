%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:25 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 469 expanded)
%              Number of clauses        :   95 ( 136 expanded)
%              Number of leaves         :   17 ( 118 expanded)
%              Depth                    :   23
%              Number of atoms          :  624 (3876 expanded)
%              Number of equality atoms :  288 (1434 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f49,plain,(
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
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f49,f48])).

fof(f91,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
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

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f94,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2)
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2)
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k6_relat_1(X0) != k5_relat_1(X2,X3)
      | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_partfun1(X0)
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f58,f78,f78])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f95,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X0 = X3
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X3
    | k6_partfun1(sK0) != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_420,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_428,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_420,c_17])).

cnf(c_1719,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1881,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4947,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1719,c_43,c_41,c_40,c_38,c_428,c_1881])).

cnf(c_1721,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1723,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1725,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4181,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1725])).

cnf(c_47,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4196,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4181,c_47])).

cnf(c_4197,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4196])).

cnf(c_4205,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_4197])).

cnf(c_44,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4386,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4205,c_44])).

cnf(c_4949,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_4947,c_4386])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_462,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_463,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_467,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_43])).

cnf(c_468,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_467])).

cnf(c_868,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | sK0 != X0
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_468])).

cnf(c_869,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_871,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_41,c_37,c_33])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | X2 = X0
    | k5_relat_1(X3,X2) != k6_partfun1(X1)
    | k5_relat_1(X0,X3) != k6_partfun1(k1_relat_1(X2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1732,plain,
    ( X0 = X1
    | k5_relat_1(X2,X0) != k6_partfun1(X3)
    | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
    | r1_tarski(k2_relat_1(X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5049,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(X1)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_871,c_1732])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1729,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2536,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1721,c_1729])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_42])).

cnf(c_769,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_768])).

cnf(c_771,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_769,c_41,c_33])).

cnf(c_2537,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2536,c_771])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_531,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_532,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_43])).

cnf(c_1715,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2622,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2537,c_1715])).

cnf(c_46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1828,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2034,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_2343,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2034])).

cnf(c_2344,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2343])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2434,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2435,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2434])).

cnf(c_3709,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2622,c_46,c_2344,c_2435])).

cnf(c_5052,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(X1)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | r1_tarski(sK0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5049,c_3709])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2609,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2610,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2609])).

cnf(c_9129,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(X1)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | r1_tarski(sK0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5052,c_44,c_46,c_2344,c_2435,c_2610])).

cnf(c_9136,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(X0) != k6_partfun1(sK0)
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | r1_tarski(sK0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4949,c_9129])).

cnf(c_2535,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1723,c_1729])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_760,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_761,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_763,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_761,c_38,c_34])).

cnf(c_2538,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2535,c_763])).

cnf(c_9137,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(X0) != k6_partfun1(sK0)
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | r1_tarski(sK0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9136,c_2538])).

cnf(c_9138,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(X0) != k6_partfun1(sK0)
    | r1_tarski(sK0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9137])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_32,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1986,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2136,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1986])).

cnf(c_2364,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2136])).

cnf(c_2365,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2364])).

cnf(c_2437,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2438,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2437])).

cnf(c_10663,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | k6_partfun1(X0) != k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9138,c_49,c_32,c_2365,c_2438])).

cnf(c_10664,plain,
    ( k6_partfun1(X0) != k6_partfun1(sK0)
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10663])).

cnf(c_10669,plain,
    ( r1_tarski(sK0,sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10664])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2517,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2518,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10669,c_2518])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:44:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.07/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/0.98  
% 4.07/0.98  ------  iProver source info
% 4.07/0.98  
% 4.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/0.98  git: non_committed_changes: false
% 4.07/0.98  git: last_make_outside_of_git: false
% 4.07/0.98  
% 4.07/0.98  ------ 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options
% 4.07/0.98  
% 4.07/0.98  --out_options                           all
% 4.07/0.98  --tptp_safe_out                         true
% 4.07/0.98  --problem_path                          ""
% 4.07/0.98  --include_path                          ""
% 4.07/0.98  --clausifier                            res/vclausify_rel
% 4.07/0.98  --clausifier_options                    ""
% 4.07/0.98  --stdin                                 false
% 4.07/0.98  --stats_out                             all
% 4.07/0.98  
% 4.07/0.98  ------ General Options
% 4.07/0.98  
% 4.07/0.98  --fof                                   false
% 4.07/0.98  --time_out_real                         305.
% 4.07/0.98  --time_out_virtual                      -1.
% 4.07/0.98  --symbol_type_check                     false
% 4.07/0.98  --clausify_out                          false
% 4.07/0.98  --sig_cnt_out                           false
% 4.07/0.98  --trig_cnt_out                          false
% 4.07/0.98  --trig_cnt_out_tolerance                1.
% 4.07/0.98  --trig_cnt_out_sk_spl                   false
% 4.07/0.98  --abstr_cl_out                          false
% 4.07/0.98  
% 4.07/0.98  ------ Global Options
% 4.07/0.98  
% 4.07/0.98  --schedule                              default
% 4.07/0.98  --add_important_lit                     false
% 4.07/0.98  --prop_solver_per_cl                    1000
% 4.07/0.98  --min_unsat_core                        false
% 4.07/0.98  --soft_assumptions                      false
% 4.07/0.98  --soft_lemma_size                       3
% 4.07/0.98  --prop_impl_unit_size                   0
% 4.07/0.98  --prop_impl_unit                        []
% 4.07/0.98  --share_sel_clauses                     true
% 4.07/0.98  --reset_solvers                         false
% 4.07/0.98  --bc_imp_inh                            [conj_cone]
% 4.07/0.98  --conj_cone_tolerance                   3.
% 4.07/0.98  --extra_neg_conj                        none
% 4.07/0.98  --large_theory_mode                     true
% 4.07/0.98  --prolific_symb_bound                   200
% 4.07/0.98  --lt_threshold                          2000
% 4.07/0.98  --clause_weak_htbl                      true
% 4.07/0.98  --gc_record_bc_elim                     false
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing Options
% 4.07/0.98  
% 4.07/0.98  --preprocessing_flag                    true
% 4.07/0.98  --time_out_prep_mult                    0.1
% 4.07/0.98  --splitting_mode                        input
% 4.07/0.98  --splitting_grd                         true
% 4.07/0.98  --splitting_cvd                         false
% 4.07/0.98  --splitting_cvd_svl                     false
% 4.07/0.98  --splitting_nvd                         32
% 4.07/0.98  --sub_typing                            true
% 4.07/0.98  --prep_gs_sim                           true
% 4.07/0.98  --prep_unflatten                        true
% 4.07/0.98  --prep_res_sim                          true
% 4.07/0.98  --prep_upred                            true
% 4.07/0.98  --prep_sem_filter                       exhaustive
% 4.07/0.98  --prep_sem_filter_out                   false
% 4.07/0.98  --pred_elim                             true
% 4.07/0.98  --res_sim_input                         true
% 4.07/0.98  --eq_ax_congr_red                       true
% 4.07/0.98  --pure_diseq_elim                       true
% 4.07/0.98  --brand_transform                       false
% 4.07/0.98  --non_eq_to_eq                          false
% 4.07/0.98  --prep_def_merge                        true
% 4.07/0.98  --prep_def_merge_prop_impl              false
% 4.07/0.98  --prep_def_merge_mbd                    true
% 4.07/0.98  --prep_def_merge_tr_red                 false
% 4.07/0.98  --prep_def_merge_tr_cl                  false
% 4.07/0.98  --smt_preprocessing                     true
% 4.07/0.98  --smt_ac_axioms                         fast
% 4.07/0.98  --preprocessed_out                      false
% 4.07/0.98  --preprocessed_stats                    false
% 4.07/0.98  
% 4.07/0.98  ------ Abstraction refinement Options
% 4.07/0.98  
% 4.07/0.98  --abstr_ref                             []
% 4.07/0.98  --abstr_ref_prep                        false
% 4.07/0.98  --abstr_ref_until_sat                   false
% 4.07/0.98  --abstr_ref_sig_restrict                funpre
% 4.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.98  --abstr_ref_under                       []
% 4.07/0.98  
% 4.07/0.98  ------ SAT Options
% 4.07/0.98  
% 4.07/0.98  --sat_mode                              false
% 4.07/0.98  --sat_fm_restart_options                ""
% 4.07/0.98  --sat_gr_def                            false
% 4.07/0.98  --sat_epr_types                         true
% 4.07/0.98  --sat_non_cyclic_types                  false
% 4.07/0.98  --sat_finite_models                     false
% 4.07/0.98  --sat_fm_lemmas                         false
% 4.07/0.98  --sat_fm_prep                           false
% 4.07/0.98  --sat_fm_uc_incr                        true
% 4.07/0.98  --sat_out_model                         small
% 4.07/0.98  --sat_out_clauses                       false
% 4.07/0.98  
% 4.07/0.98  ------ QBF Options
% 4.07/0.98  
% 4.07/0.98  --qbf_mode                              false
% 4.07/0.98  --qbf_elim_univ                         false
% 4.07/0.98  --qbf_dom_inst                          none
% 4.07/0.98  --qbf_dom_pre_inst                      false
% 4.07/0.98  --qbf_sk_in                             false
% 4.07/0.98  --qbf_pred_elim                         true
% 4.07/0.98  --qbf_split                             512
% 4.07/0.98  
% 4.07/0.98  ------ BMC1 Options
% 4.07/0.98  
% 4.07/0.98  --bmc1_incremental                      false
% 4.07/0.98  --bmc1_axioms                           reachable_all
% 4.07/0.98  --bmc1_min_bound                        0
% 4.07/0.98  --bmc1_max_bound                        -1
% 4.07/0.98  --bmc1_max_bound_default                -1
% 4.07/0.98  --bmc1_symbol_reachability              true
% 4.07/0.98  --bmc1_property_lemmas                  false
% 4.07/0.98  --bmc1_k_induction                      false
% 4.07/0.98  --bmc1_non_equiv_states                 false
% 4.07/0.98  --bmc1_deadlock                         false
% 4.07/0.98  --bmc1_ucm                              false
% 4.07/0.98  --bmc1_add_unsat_core                   none
% 4.07/0.98  --bmc1_unsat_core_children              false
% 4.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.98  --bmc1_out_stat                         full
% 4.07/0.98  --bmc1_ground_init                      false
% 4.07/0.98  --bmc1_pre_inst_next_state              false
% 4.07/0.98  --bmc1_pre_inst_state                   false
% 4.07/0.98  --bmc1_pre_inst_reach_state             false
% 4.07/0.98  --bmc1_out_unsat_core                   false
% 4.07/0.98  --bmc1_aig_witness_out                  false
% 4.07/0.98  --bmc1_verbose                          false
% 4.07/0.98  --bmc1_dump_clauses_tptp                false
% 4.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.98  --bmc1_dump_file                        -
% 4.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.98  --bmc1_ucm_extend_mode                  1
% 4.07/0.98  --bmc1_ucm_init_mode                    2
% 4.07/0.98  --bmc1_ucm_cone_mode                    none
% 4.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.98  --bmc1_ucm_relax_model                  4
% 4.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.98  --bmc1_ucm_layered_model                none
% 4.07/0.98  --bmc1_ucm_max_lemma_size               10
% 4.07/0.98  
% 4.07/0.98  ------ AIG Options
% 4.07/0.98  
% 4.07/0.98  --aig_mode                              false
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation Options
% 4.07/0.98  
% 4.07/0.98  --instantiation_flag                    true
% 4.07/0.98  --inst_sos_flag                         true
% 4.07/0.98  --inst_sos_phase                        true
% 4.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel_side                     num_symb
% 4.07/0.98  --inst_solver_per_active                1400
% 4.07/0.98  --inst_solver_calls_frac                1.
% 4.07/0.98  --inst_passive_queue_type               priority_queues
% 4.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.98  --inst_passive_queues_freq              [25;2]
% 4.07/0.98  --inst_dismatching                      true
% 4.07/0.98  --inst_eager_unprocessed_to_passive     true
% 4.07/0.98  --inst_prop_sim_given                   true
% 4.07/0.98  --inst_prop_sim_new                     false
% 4.07/0.98  --inst_subs_new                         false
% 4.07/0.98  --inst_eq_res_simp                      false
% 4.07/0.98  --inst_subs_given                       false
% 4.07/0.98  --inst_orphan_elimination               true
% 4.07/0.98  --inst_learning_loop_flag               true
% 4.07/0.98  --inst_learning_start                   3000
% 4.07/0.98  --inst_learning_factor                  2
% 4.07/0.98  --inst_start_prop_sim_after_learn       3
% 4.07/0.98  --inst_sel_renew                        solver
% 4.07/0.98  --inst_lit_activity_flag                true
% 4.07/0.98  --inst_restr_to_given                   false
% 4.07/0.98  --inst_activity_threshold               500
% 4.07/0.98  --inst_out_proof                        true
% 4.07/0.98  
% 4.07/0.98  ------ Resolution Options
% 4.07/0.98  
% 4.07/0.98  --resolution_flag                       true
% 4.07/0.98  --res_lit_sel                           adaptive
% 4.07/0.98  --res_lit_sel_side                      none
% 4.07/0.98  --res_ordering                          kbo
% 4.07/0.98  --res_to_prop_solver                    active
% 4.07/0.98  --res_prop_simpl_new                    false
% 4.07/0.98  --res_prop_simpl_given                  true
% 4.07/0.98  --res_passive_queue_type                priority_queues
% 4.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.98  --res_passive_queues_freq               [15;5]
% 4.07/0.98  --res_forward_subs                      full
% 4.07/0.98  --res_backward_subs                     full
% 4.07/0.98  --res_forward_subs_resolution           true
% 4.07/0.98  --res_backward_subs_resolution          true
% 4.07/0.98  --res_orphan_elimination                true
% 4.07/0.98  --res_time_limit                        2.
% 4.07/0.98  --res_out_proof                         true
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Options
% 4.07/0.98  
% 4.07/0.98  --superposition_flag                    true
% 4.07/0.98  --sup_passive_queue_type                priority_queues
% 4.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.98  --demod_completeness_check              fast
% 4.07/0.98  --demod_use_ground                      true
% 4.07/0.98  --sup_to_prop_solver                    passive
% 4.07/0.98  --sup_prop_simpl_new                    true
% 4.07/0.98  --sup_prop_simpl_given                  true
% 4.07/0.98  --sup_fun_splitting                     true
% 4.07/0.98  --sup_smt_interval                      50000
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Simplification Setup
% 4.07/0.98  
% 4.07/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_immed_triv                        [TrivRules]
% 4.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_bw_main                     []
% 4.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_input_bw                          []
% 4.07/0.98  
% 4.07/0.98  ------ Combination Options
% 4.07/0.98  
% 4.07/0.98  --comb_res_mult                         3
% 4.07/0.98  --comb_sup_mult                         2
% 4.07/0.98  --comb_inst_mult                        10
% 4.07/0.98  
% 4.07/0.98  ------ Debug Options
% 4.07/0.98  
% 4.07/0.98  --dbg_backtrace                         false
% 4.07/0.98  --dbg_dump_prop_clauses                 false
% 4.07/0.98  --dbg_dump_prop_clauses_file            -
% 4.07/0.98  --dbg_out_stat                          false
% 4.07/0.98  ------ Parsing...
% 4.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/0.98  ------ Proving...
% 4.07/0.98  ------ Problem Properties 
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  clauses                                 43
% 4.07/0.98  conjectures                             8
% 4.07/0.98  EPR                                     6
% 4.07/0.98  Horn                                    39
% 4.07/0.98  unary                                   17
% 4.07/0.98  binary                                  6
% 4.07/0.98  lits                                    111
% 4.07/0.98  lits eq                                 50
% 4.07/0.98  fd_pure                                 0
% 4.07/0.98  fd_pseudo                               0
% 4.07/0.98  fd_cond                                 3
% 4.07/0.98  fd_pseudo_cond                          2
% 4.07/0.98  AC symbols                              0
% 4.07/0.98  
% 4.07/0.98  ------ Schedule dynamic 5 is on 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ 
% 4.07/0.98  Current options:
% 4.07/0.98  ------ 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options
% 4.07/0.98  
% 4.07/0.98  --out_options                           all
% 4.07/0.98  --tptp_safe_out                         true
% 4.07/0.98  --problem_path                          ""
% 4.07/0.98  --include_path                          ""
% 4.07/0.98  --clausifier                            res/vclausify_rel
% 4.07/0.98  --clausifier_options                    ""
% 4.07/0.98  --stdin                                 false
% 4.07/0.98  --stats_out                             all
% 4.07/0.98  
% 4.07/0.98  ------ General Options
% 4.07/0.98  
% 4.07/0.98  --fof                                   false
% 4.07/0.98  --time_out_real                         305.
% 4.07/0.98  --time_out_virtual                      -1.
% 4.07/0.98  --symbol_type_check                     false
% 4.07/0.98  --clausify_out                          false
% 4.07/0.98  --sig_cnt_out                           false
% 4.07/0.98  --trig_cnt_out                          false
% 4.07/0.98  --trig_cnt_out_tolerance                1.
% 4.07/0.98  --trig_cnt_out_sk_spl                   false
% 4.07/0.98  --abstr_cl_out                          false
% 4.07/0.98  
% 4.07/0.98  ------ Global Options
% 4.07/0.98  
% 4.07/0.98  --schedule                              default
% 4.07/0.98  --add_important_lit                     false
% 4.07/0.98  --prop_solver_per_cl                    1000
% 4.07/0.98  --min_unsat_core                        false
% 4.07/0.98  --soft_assumptions                      false
% 4.07/0.98  --soft_lemma_size                       3
% 4.07/0.98  --prop_impl_unit_size                   0
% 4.07/0.98  --prop_impl_unit                        []
% 4.07/0.98  --share_sel_clauses                     true
% 4.07/0.98  --reset_solvers                         false
% 4.07/0.98  --bc_imp_inh                            [conj_cone]
% 4.07/0.98  --conj_cone_tolerance                   3.
% 4.07/0.98  --extra_neg_conj                        none
% 4.07/0.98  --large_theory_mode                     true
% 4.07/0.98  --prolific_symb_bound                   200
% 4.07/0.98  --lt_threshold                          2000
% 4.07/0.98  --clause_weak_htbl                      true
% 4.07/0.98  --gc_record_bc_elim                     false
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing Options
% 4.07/0.98  
% 4.07/0.98  --preprocessing_flag                    true
% 4.07/0.98  --time_out_prep_mult                    0.1
% 4.07/0.98  --splitting_mode                        input
% 4.07/0.98  --splitting_grd                         true
% 4.07/0.98  --splitting_cvd                         false
% 4.07/0.98  --splitting_cvd_svl                     false
% 4.07/0.98  --splitting_nvd                         32
% 4.07/0.98  --sub_typing                            true
% 4.07/0.98  --prep_gs_sim                           true
% 4.07/0.98  --prep_unflatten                        true
% 4.07/0.98  --prep_res_sim                          true
% 4.07/0.98  --prep_upred                            true
% 4.07/0.98  --prep_sem_filter                       exhaustive
% 4.07/0.98  --prep_sem_filter_out                   false
% 4.07/0.98  --pred_elim                             true
% 4.07/0.98  --res_sim_input                         true
% 4.07/0.98  --eq_ax_congr_red                       true
% 4.07/0.98  --pure_diseq_elim                       true
% 4.07/0.98  --brand_transform                       false
% 4.07/0.98  --non_eq_to_eq                          false
% 4.07/0.98  --prep_def_merge                        true
% 4.07/0.98  --prep_def_merge_prop_impl              false
% 4.07/0.98  --prep_def_merge_mbd                    true
% 4.07/0.98  --prep_def_merge_tr_red                 false
% 4.07/0.98  --prep_def_merge_tr_cl                  false
% 4.07/0.98  --smt_preprocessing                     true
% 4.07/0.98  --smt_ac_axioms                         fast
% 4.07/0.98  --preprocessed_out                      false
% 4.07/0.98  --preprocessed_stats                    false
% 4.07/0.98  
% 4.07/0.98  ------ Abstraction refinement Options
% 4.07/0.98  
% 4.07/0.98  --abstr_ref                             []
% 4.07/0.98  --abstr_ref_prep                        false
% 4.07/0.98  --abstr_ref_until_sat                   false
% 4.07/0.98  --abstr_ref_sig_restrict                funpre
% 4.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.98  --abstr_ref_under                       []
% 4.07/0.98  
% 4.07/0.98  ------ SAT Options
% 4.07/0.98  
% 4.07/0.98  --sat_mode                              false
% 4.07/0.98  --sat_fm_restart_options                ""
% 4.07/0.98  --sat_gr_def                            false
% 4.07/0.98  --sat_epr_types                         true
% 4.07/0.98  --sat_non_cyclic_types                  false
% 4.07/0.98  --sat_finite_models                     false
% 4.07/0.98  --sat_fm_lemmas                         false
% 4.07/0.98  --sat_fm_prep                           false
% 4.07/0.98  --sat_fm_uc_incr                        true
% 4.07/0.98  --sat_out_model                         small
% 4.07/0.98  --sat_out_clauses                       false
% 4.07/0.98  
% 4.07/0.98  ------ QBF Options
% 4.07/0.98  
% 4.07/0.98  --qbf_mode                              false
% 4.07/0.98  --qbf_elim_univ                         false
% 4.07/0.98  --qbf_dom_inst                          none
% 4.07/0.98  --qbf_dom_pre_inst                      false
% 4.07/0.98  --qbf_sk_in                             false
% 4.07/0.98  --qbf_pred_elim                         true
% 4.07/0.98  --qbf_split                             512
% 4.07/0.98  
% 4.07/0.98  ------ BMC1 Options
% 4.07/0.98  
% 4.07/0.98  --bmc1_incremental                      false
% 4.07/0.98  --bmc1_axioms                           reachable_all
% 4.07/0.98  --bmc1_min_bound                        0
% 4.07/0.98  --bmc1_max_bound                        -1
% 4.07/0.98  --bmc1_max_bound_default                -1
% 4.07/0.98  --bmc1_symbol_reachability              true
% 4.07/0.98  --bmc1_property_lemmas                  false
% 4.07/0.98  --bmc1_k_induction                      false
% 4.07/0.98  --bmc1_non_equiv_states                 false
% 4.07/0.98  --bmc1_deadlock                         false
% 4.07/0.98  --bmc1_ucm                              false
% 4.07/0.98  --bmc1_add_unsat_core                   none
% 4.07/0.98  --bmc1_unsat_core_children              false
% 4.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.98  --bmc1_out_stat                         full
% 4.07/0.98  --bmc1_ground_init                      false
% 4.07/0.98  --bmc1_pre_inst_next_state              false
% 4.07/0.98  --bmc1_pre_inst_state                   false
% 4.07/0.98  --bmc1_pre_inst_reach_state             false
% 4.07/0.98  --bmc1_out_unsat_core                   false
% 4.07/0.98  --bmc1_aig_witness_out                  false
% 4.07/0.98  --bmc1_verbose                          false
% 4.07/0.98  --bmc1_dump_clauses_tptp                false
% 4.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.98  --bmc1_dump_file                        -
% 4.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.98  --bmc1_ucm_extend_mode                  1
% 4.07/0.98  --bmc1_ucm_init_mode                    2
% 4.07/0.98  --bmc1_ucm_cone_mode                    none
% 4.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.98  --bmc1_ucm_relax_model                  4
% 4.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.98  --bmc1_ucm_layered_model                none
% 4.07/0.98  --bmc1_ucm_max_lemma_size               10
% 4.07/0.98  
% 4.07/0.98  ------ AIG Options
% 4.07/0.98  
% 4.07/0.98  --aig_mode                              false
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation Options
% 4.07/0.98  
% 4.07/0.98  --instantiation_flag                    true
% 4.07/0.98  --inst_sos_flag                         true
% 4.07/0.98  --inst_sos_phase                        true
% 4.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel_side                     none
% 4.07/0.98  --inst_solver_per_active                1400
% 4.07/0.98  --inst_solver_calls_frac                1.
% 4.07/0.98  --inst_passive_queue_type               priority_queues
% 4.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.98  --inst_passive_queues_freq              [25;2]
% 4.07/0.98  --inst_dismatching                      true
% 4.07/0.98  --inst_eager_unprocessed_to_passive     true
% 4.07/0.98  --inst_prop_sim_given                   true
% 4.07/0.98  --inst_prop_sim_new                     false
% 4.07/0.98  --inst_subs_new                         false
% 4.07/0.98  --inst_eq_res_simp                      false
% 4.07/0.98  --inst_subs_given                       false
% 4.07/0.98  --inst_orphan_elimination               true
% 4.07/0.98  --inst_learning_loop_flag               true
% 4.07/0.98  --inst_learning_start                   3000
% 4.07/0.98  --inst_learning_factor                  2
% 4.07/0.98  --inst_start_prop_sim_after_learn       3
% 4.07/0.98  --inst_sel_renew                        solver
% 4.07/0.98  --inst_lit_activity_flag                true
% 4.07/0.98  --inst_restr_to_given                   false
% 4.07/0.98  --inst_activity_threshold               500
% 4.07/0.98  --inst_out_proof                        true
% 4.07/0.98  
% 4.07/0.98  ------ Resolution Options
% 4.07/0.98  
% 4.07/0.98  --resolution_flag                       false
% 4.07/0.98  --res_lit_sel                           adaptive
% 4.07/0.98  --res_lit_sel_side                      none
% 4.07/0.98  --res_ordering                          kbo
% 4.07/0.98  --res_to_prop_solver                    active
% 4.07/0.98  --res_prop_simpl_new                    false
% 4.07/0.98  --res_prop_simpl_given                  true
% 4.07/0.98  --res_passive_queue_type                priority_queues
% 4.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.98  --res_passive_queues_freq               [15;5]
% 4.07/0.98  --res_forward_subs                      full
% 4.07/0.98  --res_backward_subs                     full
% 4.07/0.98  --res_forward_subs_resolution           true
% 4.07/0.98  --res_backward_subs_resolution          true
% 4.07/0.98  --res_orphan_elimination                true
% 4.07/0.98  --res_time_limit                        2.
% 4.07/0.98  --res_out_proof                         true
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Options
% 4.07/0.98  
% 4.07/0.98  --superposition_flag                    true
% 4.07/0.98  --sup_passive_queue_type                priority_queues
% 4.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.98  --demod_completeness_check              fast
% 4.07/0.98  --demod_use_ground                      true
% 4.07/0.98  --sup_to_prop_solver                    passive
% 4.07/0.98  --sup_prop_simpl_new                    true
% 4.07/0.98  --sup_prop_simpl_given                  true
% 4.07/0.98  --sup_fun_splitting                     true
% 4.07/0.98  --sup_smt_interval                      50000
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Simplification Setup
% 4.07/0.98  
% 4.07/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_immed_triv                        [TrivRules]
% 4.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_bw_main                     []
% 4.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_input_bw                          []
% 4.07/0.98  
% 4.07/0.98  ------ Combination Options
% 4.07/0.98  
% 4.07/0.98  --comb_res_mult                         3
% 4.07/0.98  --comb_sup_mult                         2
% 4.07/0.98  --comb_inst_mult                        10
% 4.07/0.98  
% 4.07/0.98  ------ Debug Options
% 4.07/0.98  
% 4.07/0.98  --dbg_backtrace                         false
% 4.07/0.98  --dbg_dump_prop_clauses                 false
% 4.07/0.98  --dbg_dump_prop_clauses_file            -
% 4.07/0.98  --dbg_out_stat                          false
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ Proving...
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  % SZS status Theorem for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  fof(f10,axiom,(
% 4.07/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f30,plain,(
% 4.07/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.07/0.98    inference(ennf_transformation,[],[f10])).
% 4.07/0.98  
% 4.07/0.98  fof(f31,plain,(
% 4.07/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.07/0.98    inference(flattening,[],[f30])).
% 4.07/0.98  
% 4.07/0.98  fof(f46,plain,(
% 4.07/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.07/0.98    inference(nnf_transformation,[],[f31])).
% 4.07/0.98  
% 4.07/0.98  fof(f66,plain,(
% 4.07/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f46])).
% 4.07/0.98  
% 4.07/0.98  fof(f18,conjecture,(
% 4.07/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f19,negated_conjecture,(
% 4.07/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 4.07/0.98    inference(negated_conjecture,[],[f18])).
% 4.07/0.98  
% 4.07/0.98  fof(f42,plain,(
% 4.07/0.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.07/0.98    inference(ennf_transformation,[],[f19])).
% 4.07/0.98  
% 4.07/0.98  fof(f43,plain,(
% 4.07/0.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.07/0.98    inference(flattening,[],[f42])).
% 4.07/0.98  
% 4.07/0.98  fof(f49,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f48,plain,(
% 4.07/0.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f50,plain,(
% 4.07/0.98    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 4.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f49,f48])).
% 4.07/0.98  
% 4.07/0.98  fof(f91,plain,(
% 4.07/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f11,axiom,(
% 4.07/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f68,plain,(
% 4.07/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f11])).
% 4.07/0.98  
% 4.07/0.98  fof(f15,axiom,(
% 4.07/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f78,plain,(
% 4.07/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f15])).
% 4.07/0.98  
% 4.07/0.98  fof(f101,plain,(
% 4.07/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.07/0.98    inference(definition_unfolding,[],[f68,f78])).
% 4.07/0.98  
% 4.07/0.98  fof(f84,plain,(
% 4.07/0.98    v1_funct_1(sK2)),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f86,plain,(
% 4.07/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f87,plain,(
% 4.07/0.98    v1_funct_1(sK3)),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f89,plain,(
% 4.07/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f13,axiom,(
% 4.07/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f34,plain,(
% 4.07/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.07/0.98    inference(ennf_transformation,[],[f13])).
% 4.07/0.98  
% 4.07/0.98  fof(f35,plain,(
% 4.07/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.07/0.98    inference(flattening,[],[f34])).
% 4.07/0.98  
% 4.07/0.98  fof(f76,plain,(
% 4.07/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f35])).
% 4.07/0.98  
% 4.07/0.98  fof(f14,axiom,(
% 4.07/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f36,plain,(
% 4.07/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.07/0.98    inference(ennf_transformation,[],[f14])).
% 4.07/0.98  
% 4.07/0.98  fof(f37,plain,(
% 4.07/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.07/0.98    inference(flattening,[],[f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f77,plain,(
% 4.07/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f37])).
% 4.07/0.98  
% 4.07/0.98  fof(f85,plain,(
% 4.07/0.98    v1_funct_2(sK2,sK0,sK1)),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f16,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f38,plain,(
% 4.07/0.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.07/0.98    inference(ennf_transformation,[],[f16])).
% 4.07/0.98  
% 4.07/0.98  fof(f39,plain,(
% 4.07/0.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.07/0.98    inference(flattening,[],[f38])).
% 4.07/0.98  
% 4.07/0.98  fof(f80,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f39])).
% 4.07/0.98  
% 4.07/0.98  fof(f92,plain,(
% 4.07/0.98    v2_funct_1(sK2)),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f90,plain,(
% 4.07/0.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f94,plain,(
% 4.07/0.98    k1_xboole_0 != sK1),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f5,axiom,(
% 4.07/0.98    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f21,plain,(
% 4.07/0.98    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k6_relat_1(X0) != k5_relat_1(X2,X3) | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2) | ~r1_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.07/0.98    inference(ennf_transformation,[],[f5])).
% 4.07/0.98  
% 4.07/0.98  fof(f22,plain,(
% 4.07/0.98    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.07/0.98    inference(flattening,[],[f21])).
% 4.07/0.98  
% 4.07/0.98  fof(f58,plain,(
% 4.07/0.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f22])).
% 4.07/0.98  
% 4.07/0.98  fof(f98,plain,(
% 4.07/0.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(X0) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 4.07/0.98    inference(definition_unfolding,[],[f58,f78,f78])).
% 4.07/0.98  
% 4.07/0.98  fof(f9,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f29,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.07/0.98    inference(ennf_transformation,[],[f9])).
% 4.07/0.98  
% 4.07/0.98  fof(f65,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f29])).
% 4.07/0.98  
% 4.07/0.98  fof(f12,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f32,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.07/0.98    inference(ennf_transformation,[],[f12])).
% 4.07/0.98  
% 4.07/0.98  fof(f33,plain,(
% 4.07/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.07/0.98    inference(flattening,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f47,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.07/0.98    inference(nnf_transformation,[],[f33])).
% 4.07/0.98  
% 4.07/0.98  fof(f69,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f47])).
% 4.07/0.98  
% 4.07/0.98  fof(f7,axiom,(
% 4.07/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f25,plain,(
% 4.07/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.07/0.98    inference(ennf_transformation,[],[f7])).
% 4.07/0.98  
% 4.07/0.98  fof(f26,plain,(
% 4.07/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(flattening,[],[f25])).
% 4.07/0.98  
% 4.07/0.98  fof(f62,plain,(
% 4.07/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f26])).
% 4.07/0.98  
% 4.07/0.98  fof(f2,axiom,(
% 4.07/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f20,plain,(
% 4.07/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(ennf_transformation,[],[f2])).
% 4.07/0.98  
% 4.07/0.98  fof(f54,plain,(
% 4.07/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f20])).
% 4.07/0.98  
% 4.07/0.98  fof(f3,axiom,(
% 4.07/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f55,plain,(
% 4.07/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f3])).
% 4.07/0.98  
% 4.07/0.98  fof(f6,axiom,(
% 4.07/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f23,plain,(
% 4.07/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.07/0.98    inference(ennf_transformation,[],[f6])).
% 4.07/0.98  
% 4.07/0.98  fof(f24,plain,(
% 4.07/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(flattening,[],[f23])).
% 4.07/0.98  
% 4.07/0.98  fof(f59,plain,(
% 4.07/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f88,plain,(
% 4.07/0.98    v1_funct_2(sK3,sK1,sK0)),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f93,plain,(
% 4.07/0.98    k1_xboole_0 != sK0),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f95,plain,(
% 4.07/0.98    k2_funct_1(sK2) != sK3),
% 4.07/0.98    inference(cnf_transformation,[],[f50])).
% 4.07/0.98  
% 4.07/0.98  fof(f1,axiom,(
% 4.07/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f44,plain,(
% 4.07/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.07/0.98    inference(nnf_transformation,[],[f1])).
% 4.07/0.98  
% 4.07/0.98  fof(f45,plain,(
% 4.07/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.07/0.98    inference(flattening,[],[f44])).
% 4.07/0.98  
% 4.07/0.98  fof(f52,plain,(
% 4.07/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.07/0.98    inference(cnf_transformation,[],[f45])).
% 4.07/0.98  
% 4.07/0.98  fof(f102,plain,(
% 4.07/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.07/0.98    inference(equality_resolution,[],[f52])).
% 4.07/0.98  
% 4.07/0.98  cnf(c_16,plain,
% 4.07/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.07/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.07/0.98      | X2 = X3 ),
% 4.07/0.98      inference(cnf_transformation,[],[f66]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_36,negated_conjecture,
% 4.07/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f91]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_419,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.98      | X0 = X3
% 4.07/0.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X3
% 4.07/0.98      | k6_partfun1(sK0) != X0
% 4.07/0.98      | sK0 != X2
% 4.07/0.98      | sK0 != X1 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_420,plain,
% 4.07/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.07/0.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.07/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_419]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_17,plain,
% 4.07/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f101]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_428,plain,
% 4.07/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.07/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.07/0.98      inference(forward_subsumption_resolution,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_420,c_17]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1719,plain,
% 4.07/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.07/0.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_43,negated_conjecture,
% 4.07/0.98      ( v1_funct_1(sK2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f84]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_41,negated_conjecture,
% 4.07/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f86]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_40,negated_conjecture,
% 4.07/0.98      ( v1_funct_1(sK3) ),
% 4.07/0.98      inference(cnf_transformation,[],[f87]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_38,negated_conjecture,
% 4.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f89]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_24,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.07/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.07/0.98      | ~ v1_funct_1(X0)
% 4.07/0.98      | ~ v1_funct_1(X3) ),
% 4.07/0.98      inference(cnf_transformation,[],[f76]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1881,plain,
% 4.07/0.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.07/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.07/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.07/0.98      | ~ v1_funct_1(sK3)
% 4.07/0.98      | ~ v1_funct_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4947,plain,
% 4.07/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_1719,c_43,c_41,c_40,c_38,c_428,c_1881]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1721,plain,
% 4.07/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1723,plain,
% 4.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_26,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.07/0.98      | ~ v1_funct_1(X0)
% 4.07/0.98      | ~ v1_funct_1(X3)
% 4.07/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.07/0.98      inference(cnf_transformation,[],[f77]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1725,plain,
% 4.07/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.07/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.07/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.07/0.98      | v1_funct_1(X5) != iProver_top
% 4.07/0.98      | v1_funct_1(X4) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4181,plain,
% 4.07/0.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.07/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.07/0.98      | v1_funct_1(X2) != iProver_top
% 4.07/0.98      | v1_funct_1(sK3) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_1723,c_1725]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_47,plain,
% 4.07/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4196,plain,
% 4.07/0.98      ( v1_funct_1(X2) != iProver_top
% 4.07/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.07/0.98      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_4181,c_47]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4197,plain,
% 4.07/0.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.07/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.07/0.98      | v1_funct_1(X2) != iProver_top ),
% 4.07/0.98      inference(renaming,[status(thm)],[c_4196]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4205,plain,
% 4.07/0.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 4.07/0.98      | v1_funct_1(sK2) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_1721,c_4197]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_44,plain,
% 4.07/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4386,plain,
% 4.07/0.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_4205,c_44]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4949,plain,
% 4.07/0.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 4.07/0.98      inference(demodulation,[status(thm)],[c_4947,c_4386]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_42,negated_conjecture,
% 4.07/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f85]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_27,plain,
% 4.07/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.98      | ~ v2_funct_1(X0)
% 4.07/0.98      | ~ v1_funct_1(X0)
% 4.07/0.98      | k2_relset_1(X1,X2,X0) != X2
% 4.07/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 4.07/0.98      | k1_xboole_0 = X2 ),
% 4.07/0.98      inference(cnf_transformation,[],[f80]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_35,negated_conjecture,
% 4.07/0.98      ( v2_funct_1(sK2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f92]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_462,plain,
% 4.07/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.98      | ~ v1_funct_1(X0)
% 4.07/0.98      | k2_relset_1(X1,X2,X0) != X2
% 4.07/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 4.07/0.98      | sK2 != X0
% 4.07/0.98      | k1_xboole_0 = X2 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_463,plain,
% 4.07/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 4.07/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.07/0.98      | ~ v1_funct_1(sK2)
% 4.07/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 4.07/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 4.07/0.98      | k1_xboole_0 = X1 ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_462]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_467,plain,
% 4.07/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.07/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 4.07/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 4.07/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 4.07/0.98      | k1_xboole_0 = X1 ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_463,c_43]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_468,plain,
% 4.07/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 4.07/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.07/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 4.07/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 4.07/0.98      | k1_xboole_0 = X1 ),
% 4.07/0.98      inference(renaming,[status(thm)],[c_467]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_868,plain,
% 4.07/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.07/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 4.07/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 4.07/0.98      | sK0 != X0
% 4.07/0.98      | sK1 != X1
% 4.07/0.98      | sK2 != sK2
% 4.07/0.98      | k1_xboole_0 = X1 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_42,c_468]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_869,plain,
% 4.07/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.07/0.98      | k2_relset_1(sK0,sK1,sK2) != sK1
% 4.07/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 4.07/0.98      | k1_xboole_0 = sK1 ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_868]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_37,negated_conjecture,
% 4.07/0.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 4.07/0.98      inference(cnf_transformation,[],[f90]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_33,negated_conjecture,
% 4.07/0.98      ( k1_xboole_0 != sK1 ),
% 4.07/0.98      inference(cnf_transformation,[],[f94]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_871,plain,
% 4.07/0.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_869,c_41,c_37,c_33]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_7,plain,
% 4.07/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 4.07/0.98      | ~ v1_relat_1(X0)
% 4.07/0.98      | ~ v1_relat_1(X2)
% 4.07/0.98      | ~ v1_relat_1(X3)
% 4.07/0.98      | X2 = X0
% 4.07/0.98      | k5_relat_1(X3,X2) != k6_partfun1(X1)
% 4.07/0.98      | k5_relat_1(X0,X3) != k6_partfun1(k1_relat_1(X2)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f98]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1732,plain,
% 4.07/0.98      ( X0 = X1
% 4.07/0.98      | k5_relat_1(X2,X0) != k6_partfun1(X3)
% 4.07/0.98      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
% 4.07/0.98      | r1_tarski(k2_relat_1(X1),X3) != iProver_top
% 4.07/0.98      | v1_relat_1(X1) != iProver_top
% 4.07/0.98      | v1_relat_1(X0) != iProver_top
% 4.07/0.98      | v1_relat_1(X2) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_5049,plain,
% 4.07/0.98      ( k5_relat_1(sK2,X0) != k6_partfun1(X1)
% 4.07/0.98      | k2_funct_1(sK2) = X0
% 4.07/0.98      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 4.07/0.98      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) != iProver_top
% 4.07/0.98      | v1_relat_1(X0) != iProver_top
% 4.07/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 4.07/0.98      | v1_relat_1(sK2) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_871,c_1732]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_14,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.07/0.98      inference(cnf_transformation,[],[f65]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1729,plain,
% 4.07/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.07/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2536,plain,
% 4.07/0.98      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1721,c_1729]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_23,plain,
% 4.07/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.07/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.07/0.99      | k1_xboole_0 = X2 ),
% 4.07/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_768,plain,
% 4.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.07/0.99      | sK0 != X1
% 4.07/0.99      | sK1 != X2
% 4.07/0.99      | sK2 != X0
% 4.07/0.99      | k1_xboole_0 = X2 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_42]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_769,plain,
% 4.07/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.07/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 4.07/0.99      | k1_xboole_0 = sK1 ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_768]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_771,plain,
% 4.07/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_769,c_41,c_33]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2537,plain,
% 4.07/0.99      ( k1_relat_1(sK2) = sK0 ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_2536,c_771]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10,plain,
% 4.07/0.99      ( ~ v2_funct_1(X0)
% 4.07/0.99      | ~ v1_funct_1(X0)
% 4.07/0.99      | ~ v1_relat_1(X0)
% 4.07/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f62]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_531,plain,
% 4.07/0.99      ( ~ v1_funct_1(X0)
% 4.07/0.99      | ~ v1_relat_1(X0)
% 4.07/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 4.07/0.99      | sK2 != X0 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_532,plain,
% 4.07/0.99      ( ~ v1_funct_1(sK2)
% 4.07/0.99      | ~ v1_relat_1(sK2)
% 4.07/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_531]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_534,plain,
% 4.07/0.99      ( ~ v1_relat_1(sK2)
% 4.07/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_532,c_43]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1715,plain,
% 4.07/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 4.07/0.99      | v1_relat_1(sK2) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2622,plain,
% 4.07/0.99      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 4.07/0.99      | v1_relat_1(sK2) != iProver_top ),
% 4.07/0.99      inference(demodulation,[status(thm)],[c_2537,c_1715]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_46,plain,
% 4.07/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3,plain,
% 4.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.07/0.99      | ~ v1_relat_1(X1)
% 4.07/0.99      | v1_relat_1(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1828,plain,
% 4.07/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 4.07/0.99      | ~ v1_relat_1(X0)
% 4.07/0.99      | v1_relat_1(sK2) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2034,plain,
% 4.07/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.07/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 4.07/0.99      | v1_relat_1(sK2) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1828]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2343,plain,
% 4.07/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.07/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 4.07/0.99      | v1_relat_1(sK2) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2034]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2344,plain,
% 4.07/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.07/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 4.07/0.99      | v1_relat_1(sK2) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2343]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4,plain,
% 4.07/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2434,plain,
% 4.07/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2435,plain,
% 4.07/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2434]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3709,plain,
% 4.07/0.99      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_2622,c_46,c_2344,c_2435]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5052,plain,
% 4.07/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(X1)
% 4.07/0.99      | k2_funct_1(sK2) = X0
% 4.07/0.99      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 4.07/0.99      | r1_tarski(sK0,X1) != iProver_top
% 4.07/0.99      | v1_relat_1(X0) != iProver_top
% 4.07/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 4.07/0.99      | v1_relat_1(sK2) != iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_5049,c_3709]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9,plain,
% 4.07/0.99      ( ~ v1_funct_1(X0)
% 4.07/0.99      | ~ v1_relat_1(X0)
% 4.07/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2609,plain,
% 4.07/0.99      ( ~ v1_funct_1(sK2)
% 4.07/0.99      | v1_relat_1(k2_funct_1(sK2))
% 4.07/0.99      | ~ v1_relat_1(sK2) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2610,plain,
% 4.07/0.99      ( v1_funct_1(sK2) != iProver_top
% 4.07/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 4.07/0.99      | v1_relat_1(sK2) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2609]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9129,plain,
% 4.07/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(X1)
% 4.07/0.99      | k2_funct_1(sK2) = X0
% 4.07/0.99      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 4.07/0.99      | r1_tarski(sK0,X1) != iProver_top
% 4.07/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_5052,c_44,c_46,c_2344,c_2435,c_2610]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9136,plain,
% 4.07/0.99      ( k2_funct_1(sK2) = sK3
% 4.07/0.99      | k6_partfun1(X0) != k6_partfun1(sK0)
% 4.07/0.99      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 4.07/0.99      | r1_tarski(sK0,X0) != iProver_top
% 4.07/0.99      | v1_relat_1(sK3) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_4949,c_9129]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2535,plain,
% 4.07/0.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1723,c_1729]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_39,negated_conjecture,
% 4.07/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f88]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_760,plain,
% 4.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.07/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.07/0.99      | sK0 != X2
% 4.07/0.99      | sK1 != X1
% 4.07/0.99      | sK3 != X0
% 4.07/0.99      | k1_xboole_0 = X2 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_39]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_761,plain,
% 4.07/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.07/0.99      | k1_relset_1(sK1,sK0,sK3) = sK1
% 4.07/0.99      | k1_xboole_0 = sK0 ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_760]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_34,negated_conjecture,
% 4.07/0.99      ( k1_xboole_0 != sK0 ),
% 4.07/0.99      inference(cnf_transformation,[],[f93]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_763,plain,
% 4.07/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_761,c_38,c_34]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2538,plain,
% 4.07/0.99      ( k1_relat_1(sK3) = sK1 ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_2535,c_763]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9137,plain,
% 4.07/0.99      ( k2_funct_1(sK2) = sK3
% 4.07/0.99      | k6_partfun1(X0) != k6_partfun1(sK0)
% 4.07/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 4.07/0.99      | r1_tarski(sK0,X0) != iProver_top
% 4.07/0.99      | v1_relat_1(sK3) != iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_9136,c_2538]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9138,plain,
% 4.07/0.99      ( k2_funct_1(sK2) = sK3
% 4.07/0.99      | k6_partfun1(X0) != k6_partfun1(sK0)
% 4.07/0.99      | r1_tarski(sK0,X0) != iProver_top
% 4.07/0.99      | v1_relat_1(sK3) != iProver_top ),
% 4.07/0.99      inference(equality_resolution_simp,[status(thm)],[c_9137]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_49,plain,
% 4.07/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_32,negated_conjecture,
% 4.07/0.99      ( k2_funct_1(sK2) != sK3 ),
% 4.07/0.99      inference(cnf_transformation,[],[f95]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1986,plain,
% 4.07/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 4.07/0.99      | ~ v1_relat_1(X0)
% 4.07/0.99      | v1_relat_1(sK3) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2136,plain,
% 4.07/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.07/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 4.07/0.99      | v1_relat_1(sK3) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1986]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2364,plain,
% 4.07/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.07/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 4.07/0.99      | v1_relat_1(sK3) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2136]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2365,plain,
% 4.07/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.07/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 4.07/0.99      | v1_relat_1(sK3) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2364]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2437,plain,
% 4.07/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2438,plain,
% 4.07/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2437]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10663,plain,
% 4.07/0.99      ( r1_tarski(sK0,X0) != iProver_top
% 4.07/0.99      | k6_partfun1(X0) != k6_partfun1(sK0) ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_9138,c_49,c_32,c_2365,c_2438]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10664,plain,
% 4.07/0.99      ( k6_partfun1(X0) != k6_partfun1(sK0)
% 4.07/0.99      | r1_tarski(sK0,X0) != iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_10663]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10669,plain,
% 4.07/0.99      ( r1_tarski(sK0,sK0) != iProver_top ),
% 4.07/0.99      inference(equality_resolution,[status(thm)],[c_10664]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1,plain,
% 4.07/0.99      ( r1_tarski(X0,X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f102]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2517,plain,
% 4.07/0.99      ( r1_tarski(sK0,sK0) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2518,plain,
% 4.07/0.99      ( r1_tarski(sK0,sK0) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2517]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(contradiction,plain,
% 4.07/0.99      ( $false ),
% 4.07/0.99      inference(minisat,[status(thm)],[c_10669,c_2518]) ).
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  ------                               Statistics
% 4.07/0.99  
% 4.07/0.99  ------ General
% 4.07/0.99  
% 4.07/0.99  abstr_ref_over_cycles:                  0
% 4.07/0.99  abstr_ref_under_cycles:                 0
% 4.07/0.99  gc_basic_clause_elim:                   0
% 4.07/0.99  forced_gc_time:                         0
% 4.07/0.99  parsing_time:                           0.01
% 4.07/0.99  unif_index_cands_time:                  0.
% 4.07/0.99  unif_index_add_time:                    0.
% 4.07/0.99  orderings_time:                         0.
% 4.07/0.99  out_proof_time:                         0.026
% 4.07/0.99  total_time:                             0.456
% 4.07/0.99  num_of_symbols:                         53
% 4.07/0.99  num_of_terms:                           12819
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing
% 4.07/0.99  
% 4.07/0.99  num_of_splits:                          0
% 4.07/0.99  num_of_split_atoms:                     0
% 4.07/0.99  num_of_reused_defs:                     0
% 4.07/0.99  num_eq_ax_congr_red:                    5
% 4.07/0.99  num_of_sem_filtered_clauses:            1
% 4.07/0.99  num_of_subtypes:                        0
% 4.07/0.99  monotx_restored_types:                  0
% 4.07/0.99  sat_num_of_epr_types:                   0
% 4.07/0.99  sat_num_of_non_cyclic_types:            0
% 4.07/0.99  sat_guarded_non_collapsed_types:        0
% 4.07/0.99  num_pure_diseq_elim:                    0
% 4.07/0.99  simp_replaced_by:                       0
% 4.07/0.99  res_preprocessed:                       204
% 4.07/0.99  prep_upred:                             0
% 4.07/0.99  prep_unflattend:                        85
% 4.07/0.99  smt_new_axioms:                         0
% 4.07/0.99  pred_elim_cands:                        4
% 4.07/0.99  pred_elim:                              3
% 4.07/0.99  pred_elim_cl:                           -1
% 4.07/0.99  pred_elim_cycles:                       5
% 4.07/0.99  merged_defs:                            0
% 4.07/0.99  merged_defs_ncl:                        0
% 4.07/0.99  bin_hyper_res:                          0
% 4.07/0.99  prep_cycles:                            4
% 4.07/0.99  pred_elim_time:                         0.014
% 4.07/0.99  splitting_time:                         0.
% 4.07/0.99  sem_filter_time:                        0.
% 4.07/0.99  monotx_time:                            0.
% 4.07/0.99  subtype_inf_time:                       0.
% 4.07/0.99  
% 4.07/0.99  ------ Problem properties
% 4.07/0.99  
% 4.07/0.99  clauses:                                43
% 4.07/0.99  conjectures:                            8
% 4.07/0.99  epr:                                    6
% 4.07/0.99  horn:                                   39
% 4.07/0.99  ground:                                 23
% 4.07/0.99  unary:                                  17
% 4.07/0.99  binary:                                 6
% 4.07/0.99  lits:                                   111
% 4.07/0.99  lits_eq:                                50
% 4.07/0.99  fd_pure:                                0
% 4.07/0.99  fd_pseudo:                              0
% 4.07/0.99  fd_cond:                                3
% 4.07/0.99  fd_pseudo_cond:                         2
% 4.07/0.99  ac_symbols:                             0
% 4.07/0.99  
% 4.07/0.99  ------ Propositional Solver
% 4.07/0.99  
% 4.07/0.99  prop_solver_calls:                      29
% 4.07/0.99  prop_fast_solver_calls:                 1654
% 4.07/0.99  smt_solver_calls:                       0
% 4.07/0.99  smt_fast_solver_calls:                  0
% 4.07/0.99  prop_num_of_clauses:                    5031
% 4.07/0.99  prop_preprocess_simplified:             11143
% 4.07/0.99  prop_fo_subsumed:                       105
% 4.07/0.99  prop_solver_time:                       0.
% 4.07/0.99  smt_solver_time:                        0.
% 4.07/0.99  smt_fast_solver_time:                   0.
% 4.07/0.99  prop_fast_solver_time:                  0.
% 4.07/0.99  prop_unsat_core_time:                   0.001
% 4.07/0.99  
% 4.07/0.99  ------ QBF
% 4.07/0.99  
% 4.07/0.99  qbf_q_res:                              0
% 4.07/0.99  qbf_num_tautologies:                    0
% 4.07/0.99  qbf_prep_cycles:                        0
% 4.07/0.99  
% 4.07/0.99  ------ BMC1
% 4.07/0.99  
% 4.07/0.99  bmc1_current_bound:                     -1
% 4.07/0.99  bmc1_last_solved_bound:                 -1
% 4.07/0.99  bmc1_unsat_core_size:                   -1
% 4.07/0.99  bmc1_unsat_core_parents_size:           -1
% 4.07/0.99  bmc1_merge_next_fun:                    0
% 4.07/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.07/0.99  
% 4.07/0.99  ------ Instantiation
% 4.07/0.99  
% 4.07/0.99  inst_num_of_clauses:                    1351
% 4.07/0.99  inst_num_in_passive:                    380
% 4.07/0.99  inst_num_in_active:                     527
% 4.07/0.99  inst_num_in_unprocessed:                444
% 4.07/0.99  inst_num_of_loops:                      600
% 4.07/0.99  inst_num_of_learning_restarts:          0
% 4.07/0.99  inst_num_moves_active_passive:          70
% 4.07/0.99  inst_lit_activity:                      0
% 4.07/0.99  inst_lit_activity_moves:                1
% 4.07/0.99  inst_num_tautologies:                   0
% 4.07/0.99  inst_num_prop_implied:                  0
% 4.07/0.99  inst_num_existing_simplified:           0
% 4.07/0.99  inst_num_eq_res_simplified:             0
% 4.07/0.99  inst_num_child_elim:                    0
% 4.07/0.99  inst_num_of_dismatching_blockings:      624
% 4.07/0.99  inst_num_of_non_proper_insts:           1376
% 4.07/0.99  inst_num_of_duplicates:                 0
% 4.07/0.99  inst_inst_num_from_inst_to_res:         0
% 4.07/0.99  inst_dismatching_checking_time:         0.
% 4.07/0.99  
% 4.07/0.99  ------ Resolution
% 4.07/0.99  
% 4.07/0.99  res_num_of_clauses:                     0
% 4.07/0.99  res_num_in_passive:                     0
% 4.07/0.99  res_num_in_active:                      0
% 4.07/0.99  res_num_of_loops:                       208
% 4.07/0.99  res_forward_subset_subsumed:            195
% 4.07/0.99  res_backward_subset_subsumed:           0
% 4.07/0.99  res_forward_subsumed:                   2
% 4.07/0.99  res_backward_subsumed:                  2
% 4.07/0.99  res_forward_subsumption_resolution:     1
% 4.07/0.99  res_backward_subsumption_resolution:    0
% 4.07/0.99  res_clause_to_clause_subsumption:       465
% 4.07/0.99  res_orphan_elimination:                 0
% 4.07/0.99  res_tautology_del:                      122
% 4.07/0.99  res_num_eq_res_simplified:              0
% 4.07/0.99  res_num_sel_changes:                    0
% 4.07/0.99  res_moves_from_active_to_pass:          0
% 4.07/0.99  
% 4.07/0.99  ------ Superposition
% 4.07/0.99  
% 4.07/0.99  sup_time_total:                         0.
% 4.07/0.99  sup_time_generating:                    0.
% 4.07/0.99  sup_time_sim_full:                      0.
% 4.07/0.99  sup_time_sim_immed:                     0.
% 4.07/0.99  
% 4.07/0.99  sup_num_of_clauses:                     207
% 4.07/0.99  sup_num_in_active:                      104
% 4.07/0.99  sup_num_in_passive:                     103
% 4.07/0.99  sup_num_of_loops:                       118
% 4.07/0.99  sup_fw_superposition:                   126
% 4.07/0.99  sup_bw_superposition:                   107
% 4.07/0.99  sup_immediate_simplified:               83
% 4.07/0.99  sup_given_eliminated:                   1
% 4.07/0.99  comparisons_done:                       0
% 4.07/0.99  comparisons_avoided:                    14
% 4.07/0.99  
% 4.07/0.99  ------ Simplifications
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  sim_fw_subset_subsumed:                 12
% 4.07/0.99  sim_bw_subset_subsumed:                 14
% 4.07/0.99  sim_fw_subsumed:                        9
% 4.07/0.99  sim_bw_subsumed:                        3
% 4.07/0.99  sim_fw_subsumption_res:                 0
% 4.07/0.99  sim_bw_subsumption_res:                 0
% 4.07/0.99  sim_tautology_del:                      2
% 4.07/0.99  sim_eq_tautology_del:                   31
% 4.07/0.99  sim_eq_res_simp:                        1
% 4.07/0.99  sim_fw_demodulated:                     13
% 4.07/0.99  sim_bw_demodulated:                     5
% 4.07/0.99  sim_light_normalised:                   68
% 4.07/0.99  sim_joinable_taut:                      0
% 4.07/0.99  sim_joinable_simp:                      0
% 4.07/0.99  sim_ac_normalised:                      0
% 4.07/0.99  sim_smt_subsumption:                    0
% 4.07/0.99  
%------------------------------------------------------------------------------
