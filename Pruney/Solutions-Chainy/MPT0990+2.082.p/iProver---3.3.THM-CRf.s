%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:14 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  167 (1463 expanded)
%              Number of clauses        :   95 ( 387 expanded)
%              Number of leaves         :   20 ( 397 expanded)
%              Depth                    :   21
%              Number of atoms          :  697 (12706 expanded)
%              Number of equality atoms :  332 (4614 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f51,f50])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f91,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f72,f76])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f7,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f76])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f76])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f76])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1273,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1276,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1284,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5022,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1276,c_1284])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_45,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5150,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5022,c_45])).

cnf(c_5151,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5150])).

cnf(c_5159,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_5151])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_443,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_451,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_443,c_19])).

cnf(c_1269,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1388,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2115,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1269,c_41,c_39,c_38,c_36,c_451,c_1388])).

cnf(c_5160,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5159,c_2115])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5428,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5160,c_42])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1291,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5430,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5428,c_1291])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1288,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2331,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1273,c_1288])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2332,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2331,c_35])).

cnf(c_2330,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1276,c_1288])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_455,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_456,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_543,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_456])).

cnf(c_1268,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_1815,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1268])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_43,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2122,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1815,c_42,c_43,c_44,c_45,c_46,c_47])).

cnf(c_2333,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2330,c_2122])).

cnf(c_5431,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5430,c_2332,c_2333])).

cnf(c_5432,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5431])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_732,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_763,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_733,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1386,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1387,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1434,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1783,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_1784,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2042,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2927,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2928,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2927])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_1282,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5519,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1282])).

cnf(c_5750,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5519,c_42,c_43,c_44])).

cnf(c_5751,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5750])).

cnf(c_5754,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2115,c_5751])).

cnf(c_6594,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5754,c_45,c_46,c_47,c_32,c_763,c_1387,c_2928])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1292,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6600,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6594,c_1292])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1278,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2872,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_1278])).

cnf(c_3345,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2872,c_45,c_46,c_47,c_32,c_763,c_1387])).

cnf(c_3346,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3345])).

cnf(c_6605,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_6594,c_3346])).

cnf(c_6607,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6600,c_6605])).

cnf(c_1,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6608,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6607,c_1])).

cnf(c_7912,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5432,c_42,c_44,c_45,c_46,c_47,c_32,c_763,c_1387,c_1784,c_2042,c_2928,c_5754,c_6608])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1290,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6603,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6594,c_1290])).

cnf(c_3774,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3775,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3774])).

cnf(c_6806,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6603,c_45,c_46,c_47,c_32,c_763,c_1387,c_1784,c_2928,c_3775,c_5754])).

cnf(c_7914,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_7912,c_6806])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7914,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:21:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.95/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/0.98  
% 3.95/0.98  ------  iProver source info
% 3.95/0.98  
% 3.95/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.95/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/0.98  git: non_committed_changes: false
% 3.95/0.98  git: last_make_outside_of_git: false
% 3.95/0.98  
% 3.95/0.98  ------ 
% 3.95/0.98  
% 3.95/0.98  ------ Input Options
% 3.95/0.98  
% 3.95/0.98  --out_options                           all
% 3.95/0.98  --tptp_safe_out                         true
% 3.95/0.98  --problem_path                          ""
% 3.95/0.98  --include_path                          ""
% 3.95/0.98  --clausifier                            res/vclausify_rel
% 3.95/0.98  --clausifier_options                    ""
% 3.95/0.98  --stdin                                 false
% 3.95/0.98  --stats_out                             all
% 3.95/0.98  
% 3.95/0.98  ------ General Options
% 3.95/0.98  
% 3.95/0.98  --fof                                   false
% 3.95/0.98  --time_out_real                         305.
% 3.95/0.98  --time_out_virtual                      -1.
% 3.95/0.98  --symbol_type_check                     false
% 3.95/0.98  --clausify_out                          false
% 3.95/0.98  --sig_cnt_out                           false
% 3.95/0.98  --trig_cnt_out                          false
% 3.95/0.98  --trig_cnt_out_tolerance                1.
% 3.95/0.98  --trig_cnt_out_sk_spl                   false
% 3.95/0.98  --abstr_cl_out                          false
% 3.95/0.98  
% 3.95/0.98  ------ Global Options
% 3.95/0.98  
% 3.95/0.98  --schedule                              default
% 3.95/0.98  --add_important_lit                     false
% 3.95/0.98  --prop_solver_per_cl                    1000
% 3.95/0.98  --min_unsat_core                        false
% 3.95/0.98  --soft_assumptions                      false
% 3.95/0.98  --soft_lemma_size                       3
% 3.95/0.98  --prop_impl_unit_size                   0
% 3.95/0.98  --prop_impl_unit                        []
% 3.95/0.98  --share_sel_clauses                     true
% 3.95/0.98  --reset_solvers                         false
% 3.95/0.98  --bc_imp_inh                            [conj_cone]
% 3.95/0.98  --conj_cone_tolerance                   3.
% 3.95/0.98  --extra_neg_conj                        none
% 3.95/0.98  --large_theory_mode                     true
% 3.95/0.98  --prolific_symb_bound                   200
% 3.95/0.98  --lt_threshold                          2000
% 3.95/0.98  --clause_weak_htbl                      true
% 3.95/0.98  --gc_record_bc_elim                     false
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing Options
% 3.95/0.98  
% 3.95/0.98  --preprocessing_flag                    true
% 3.95/0.98  --time_out_prep_mult                    0.1
% 3.95/0.98  --splitting_mode                        input
% 3.95/0.98  --splitting_grd                         true
% 3.95/0.98  --splitting_cvd                         false
% 3.95/0.98  --splitting_cvd_svl                     false
% 3.95/0.98  --splitting_nvd                         32
% 3.95/0.98  --sub_typing                            true
% 3.95/0.98  --prep_gs_sim                           true
% 3.95/0.98  --prep_unflatten                        true
% 3.95/0.98  --prep_res_sim                          true
% 3.95/0.98  --prep_upred                            true
% 3.95/0.98  --prep_sem_filter                       exhaustive
% 3.95/0.98  --prep_sem_filter_out                   false
% 3.95/0.98  --pred_elim                             true
% 3.95/0.98  --res_sim_input                         true
% 3.95/0.98  --eq_ax_congr_red                       true
% 3.95/0.98  --pure_diseq_elim                       true
% 3.95/0.98  --brand_transform                       false
% 3.95/0.98  --non_eq_to_eq                          false
% 3.95/0.98  --prep_def_merge                        true
% 3.95/0.98  --prep_def_merge_prop_impl              false
% 3.95/0.98  --prep_def_merge_mbd                    true
% 3.95/0.98  --prep_def_merge_tr_red                 false
% 3.95/0.98  --prep_def_merge_tr_cl                  false
% 3.95/0.98  --smt_preprocessing                     true
% 3.95/0.98  --smt_ac_axioms                         fast
% 3.95/0.98  --preprocessed_out                      false
% 3.95/0.98  --preprocessed_stats                    false
% 3.95/0.98  
% 3.95/0.98  ------ Abstraction refinement Options
% 3.95/0.98  
% 3.95/0.98  --abstr_ref                             []
% 3.95/0.98  --abstr_ref_prep                        false
% 3.95/0.98  --abstr_ref_until_sat                   false
% 3.95/0.98  --abstr_ref_sig_restrict                funpre
% 3.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/0.98  --abstr_ref_under                       []
% 3.95/0.98  
% 3.95/0.98  ------ SAT Options
% 3.95/0.98  
% 3.95/0.98  --sat_mode                              false
% 3.95/0.98  --sat_fm_restart_options                ""
% 3.95/0.98  --sat_gr_def                            false
% 3.95/0.98  --sat_epr_types                         true
% 3.95/0.98  --sat_non_cyclic_types                  false
% 3.95/0.98  --sat_finite_models                     false
% 3.95/0.98  --sat_fm_lemmas                         false
% 3.95/0.98  --sat_fm_prep                           false
% 3.95/0.98  --sat_fm_uc_incr                        true
% 3.95/0.98  --sat_out_model                         small
% 3.95/0.98  --sat_out_clauses                       false
% 3.95/0.98  
% 3.95/0.98  ------ QBF Options
% 3.95/0.98  
% 3.95/0.98  --qbf_mode                              false
% 3.95/0.98  --qbf_elim_univ                         false
% 3.95/0.98  --qbf_dom_inst                          none
% 3.95/0.98  --qbf_dom_pre_inst                      false
% 3.95/0.98  --qbf_sk_in                             false
% 3.95/0.98  --qbf_pred_elim                         true
% 3.95/0.98  --qbf_split                             512
% 3.95/0.98  
% 3.95/0.98  ------ BMC1 Options
% 3.95/0.98  
% 3.95/0.98  --bmc1_incremental                      false
% 3.95/0.98  --bmc1_axioms                           reachable_all
% 3.95/0.98  --bmc1_min_bound                        0
% 3.95/0.98  --bmc1_max_bound                        -1
% 3.95/0.98  --bmc1_max_bound_default                -1
% 3.95/0.98  --bmc1_symbol_reachability              true
% 3.95/0.98  --bmc1_property_lemmas                  false
% 3.95/0.98  --bmc1_k_induction                      false
% 3.95/0.98  --bmc1_non_equiv_states                 false
% 3.95/0.98  --bmc1_deadlock                         false
% 3.95/0.98  --bmc1_ucm                              false
% 3.95/0.98  --bmc1_add_unsat_core                   none
% 3.95/0.98  --bmc1_unsat_core_children              false
% 3.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/0.98  --bmc1_out_stat                         full
% 3.95/0.98  --bmc1_ground_init                      false
% 3.95/0.98  --bmc1_pre_inst_next_state              false
% 3.95/0.98  --bmc1_pre_inst_state                   false
% 3.95/0.98  --bmc1_pre_inst_reach_state             false
% 3.95/0.98  --bmc1_out_unsat_core                   false
% 3.95/0.98  --bmc1_aig_witness_out                  false
% 3.95/0.98  --bmc1_verbose                          false
% 3.95/0.98  --bmc1_dump_clauses_tptp                false
% 3.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.95/0.98  --bmc1_dump_file                        -
% 3.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.95/0.98  --bmc1_ucm_extend_mode                  1
% 3.95/0.98  --bmc1_ucm_init_mode                    2
% 3.95/0.98  --bmc1_ucm_cone_mode                    none
% 3.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.95/0.98  --bmc1_ucm_relax_model                  4
% 3.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/0.98  --bmc1_ucm_layered_model                none
% 3.95/0.98  --bmc1_ucm_max_lemma_size               10
% 3.95/0.98  
% 3.95/0.98  ------ AIG Options
% 3.95/0.98  
% 3.95/0.98  --aig_mode                              false
% 3.95/0.98  
% 3.95/0.98  ------ Instantiation Options
% 3.95/0.98  
% 3.95/0.98  --instantiation_flag                    true
% 3.95/0.98  --inst_sos_flag                         true
% 3.95/0.98  --inst_sos_phase                        true
% 3.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/0.98  --inst_lit_sel_side                     num_symb
% 3.95/0.98  --inst_solver_per_active                1400
% 3.95/0.98  --inst_solver_calls_frac                1.
% 3.95/0.98  --inst_passive_queue_type               priority_queues
% 3.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/0.98  --inst_passive_queues_freq              [25;2]
% 3.95/0.98  --inst_dismatching                      true
% 3.95/0.98  --inst_eager_unprocessed_to_passive     true
% 3.95/0.98  --inst_prop_sim_given                   true
% 3.95/0.98  --inst_prop_sim_new                     false
% 3.95/0.98  --inst_subs_new                         false
% 3.95/0.98  --inst_eq_res_simp                      false
% 3.95/0.98  --inst_subs_given                       false
% 3.95/0.98  --inst_orphan_elimination               true
% 3.95/0.98  --inst_learning_loop_flag               true
% 3.95/0.98  --inst_learning_start                   3000
% 3.95/0.98  --inst_learning_factor                  2
% 3.95/0.98  --inst_start_prop_sim_after_learn       3
% 3.95/0.98  --inst_sel_renew                        solver
% 3.95/0.98  --inst_lit_activity_flag                true
% 3.95/0.98  --inst_restr_to_given                   false
% 3.95/0.98  --inst_activity_threshold               500
% 3.95/0.98  --inst_out_proof                        true
% 3.95/0.98  
% 3.95/0.98  ------ Resolution Options
% 3.95/0.98  
% 3.95/0.98  --resolution_flag                       true
% 3.95/0.98  --res_lit_sel                           adaptive
% 3.95/0.98  --res_lit_sel_side                      none
% 3.95/0.98  --res_ordering                          kbo
% 3.95/0.98  --res_to_prop_solver                    active
% 3.95/0.98  --res_prop_simpl_new                    false
% 3.95/0.98  --res_prop_simpl_given                  true
% 3.95/0.98  --res_passive_queue_type                priority_queues
% 3.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/0.98  --res_passive_queues_freq               [15;5]
% 3.95/0.98  --res_forward_subs                      full
% 3.95/0.98  --res_backward_subs                     full
% 3.95/0.98  --res_forward_subs_resolution           true
% 3.95/0.98  --res_backward_subs_resolution          true
% 3.95/0.98  --res_orphan_elimination                true
% 3.95/0.98  --res_time_limit                        2.
% 3.95/0.98  --res_out_proof                         true
% 3.95/0.98  
% 3.95/0.98  ------ Superposition Options
% 3.95/0.98  
% 3.95/0.98  --superposition_flag                    true
% 3.95/0.98  --sup_passive_queue_type                priority_queues
% 3.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.95/0.98  --demod_completeness_check              fast
% 3.95/0.98  --demod_use_ground                      true
% 3.95/0.98  --sup_to_prop_solver                    passive
% 3.95/0.98  --sup_prop_simpl_new                    true
% 3.95/0.98  --sup_prop_simpl_given                  true
% 3.95/0.98  --sup_fun_splitting                     true
% 3.95/0.98  --sup_smt_interval                      50000
% 3.95/0.98  
% 3.95/0.98  ------ Superposition Simplification Setup
% 3.95/0.98  
% 3.95/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.95/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.95/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.95/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.95/0.98  --sup_immed_triv                        [TrivRules]
% 3.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_immed_bw_main                     []
% 3.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_input_bw                          []
% 3.95/0.98  
% 3.95/0.98  ------ Combination Options
% 3.95/0.98  
% 3.95/0.98  --comb_res_mult                         3
% 3.95/0.98  --comb_sup_mult                         2
% 3.95/0.98  --comb_inst_mult                        10
% 3.95/0.98  
% 3.95/0.98  ------ Debug Options
% 3.95/0.98  
% 3.95/0.98  --dbg_backtrace                         false
% 3.95/0.98  --dbg_dump_prop_clauses                 false
% 3.95/0.98  --dbg_dump_prop_clauses_file            -
% 3.95/0.98  --dbg_out_stat                          false
% 3.95/0.98  ------ Parsing...
% 3.95/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/0.98  ------ Proving...
% 3.95/0.98  ------ Problem Properties 
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  clauses                                 39
% 3.95/0.98  conjectures                             11
% 3.95/0.98  EPR                                     7
% 3.95/0.98  Horn                                    35
% 3.95/0.98  unary                                   16
% 3.95/0.98  binary                                  3
% 3.95/0.98  lits                                    143
% 3.95/0.98  lits eq                                 33
% 3.95/0.98  fd_pure                                 0
% 3.95/0.98  fd_pseudo                               0
% 3.95/0.98  fd_cond                                 4
% 3.95/0.98  fd_pseudo_cond                          1
% 3.95/0.98  AC symbols                              0
% 3.95/0.98  
% 3.95/0.98  ------ Schedule dynamic 5 is on 
% 3.95/0.98  
% 3.95/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  ------ 
% 3.95/0.98  Current options:
% 3.95/0.98  ------ 
% 3.95/0.98  
% 3.95/0.98  ------ Input Options
% 3.95/0.98  
% 3.95/0.98  --out_options                           all
% 3.95/0.98  --tptp_safe_out                         true
% 3.95/0.98  --problem_path                          ""
% 3.95/0.98  --include_path                          ""
% 3.95/0.98  --clausifier                            res/vclausify_rel
% 3.95/0.98  --clausifier_options                    ""
% 3.95/0.98  --stdin                                 false
% 3.95/0.98  --stats_out                             all
% 3.95/0.98  
% 3.95/0.98  ------ General Options
% 3.95/0.98  
% 3.95/0.98  --fof                                   false
% 3.95/0.98  --time_out_real                         305.
% 3.95/0.98  --time_out_virtual                      -1.
% 3.95/0.98  --symbol_type_check                     false
% 3.95/0.98  --clausify_out                          false
% 3.95/0.98  --sig_cnt_out                           false
% 3.95/0.98  --trig_cnt_out                          false
% 3.95/0.98  --trig_cnt_out_tolerance                1.
% 3.95/0.98  --trig_cnt_out_sk_spl                   false
% 3.95/0.98  --abstr_cl_out                          false
% 3.95/0.98  
% 3.95/0.98  ------ Global Options
% 3.95/0.98  
% 3.95/0.98  --schedule                              default
% 3.95/0.98  --add_important_lit                     false
% 3.95/0.98  --prop_solver_per_cl                    1000
% 3.95/0.98  --min_unsat_core                        false
% 3.95/0.98  --soft_assumptions                      false
% 3.95/0.98  --soft_lemma_size                       3
% 3.95/0.98  --prop_impl_unit_size                   0
% 3.95/0.98  --prop_impl_unit                        []
% 3.95/0.98  --share_sel_clauses                     true
% 3.95/0.98  --reset_solvers                         false
% 3.95/0.98  --bc_imp_inh                            [conj_cone]
% 3.95/0.98  --conj_cone_tolerance                   3.
% 3.95/0.98  --extra_neg_conj                        none
% 3.95/0.98  --large_theory_mode                     true
% 3.95/0.98  --prolific_symb_bound                   200
% 3.95/0.98  --lt_threshold                          2000
% 3.95/0.98  --clause_weak_htbl                      true
% 3.95/0.98  --gc_record_bc_elim                     false
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing Options
% 3.95/0.98  
% 3.95/0.98  --preprocessing_flag                    true
% 3.95/0.98  --time_out_prep_mult                    0.1
% 3.95/0.98  --splitting_mode                        input
% 3.95/0.98  --splitting_grd                         true
% 3.95/0.98  --splitting_cvd                         false
% 3.95/0.98  --splitting_cvd_svl                     false
% 3.95/0.98  --splitting_nvd                         32
% 3.95/0.98  --sub_typing                            true
% 3.95/0.98  --prep_gs_sim                           true
% 3.95/0.98  --prep_unflatten                        true
% 3.95/0.98  --prep_res_sim                          true
% 3.95/0.98  --prep_upred                            true
% 3.95/0.98  --prep_sem_filter                       exhaustive
% 3.95/0.98  --prep_sem_filter_out                   false
% 3.95/0.98  --pred_elim                             true
% 3.95/0.98  --res_sim_input                         true
% 3.95/0.98  --eq_ax_congr_red                       true
% 3.95/0.98  --pure_diseq_elim                       true
% 3.95/0.98  --brand_transform                       false
% 3.95/0.98  --non_eq_to_eq                          false
% 3.95/0.98  --prep_def_merge                        true
% 3.95/0.98  --prep_def_merge_prop_impl              false
% 3.95/0.98  --prep_def_merge_mbd                    true
% 3.95/0.98  --prep_def_merge_tr_red                 false
% 3.95/0.98  --prep_def_merge_tr_cl                  false
% 3.95/0.98  --smt_preprocessing                     true
% 3.95/0.98  --smt_ac_axioms                         fast
% 3.95/0.98  --preprocessed_out                      false
% 3.95/0.98  --preprocessed_stats                    false
% 3.95/0.98  
% 3.95/0.98  ------ Abstraction refinement Options
% 3.95/0.98  
% 3.95/0.98  --abstr_ref                             []
% 3.95/0.98  --abstr_ref_prep                        false
% 3.95/0.98  --abstr_ref_until_sat                   false
% 3.95/0.98  --abstr_ref_sig_restrict                funpre
% 3.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/0.98  --abstr_ref_under                       []
% 3.95/0.98  
% 3.95/0.98  ------ SAT Options
% 3.95/0.98  
% 3.95/0.98  --sat_mode                              false
% 3.95/0.98  --sat_fm_restart_options                ""
% 3.95/0.98  --sat_gr_def                            false
% 3.95/0.98  --sat_epr_types                         true
% 3.95/0.98  --sat_non_cyclic_types                  false
% 3.95/0.98  --sat_finite_models                     false
% 3.95/0.98  --sat_fm_lemmas                         false
% 3.95/0.98  --sat_fm_prep                           false
% 3.95/0.98  --sat_fm_uc_incr                        true
% 3.95/0.98  --sat_out_model                         small
% 3.95/0.98  --sat_out_clauses                       false
% 3.95/0.98  
% 3.95/0.98  ------ QBF Options
% 3.95/0.98  
% 3.95/0.98  --qbf_mode                              false
% 3.95/0.98  --qbf_elim_univ                         false
% 3.95/0.98  --qbf_dom_inst                          none
% 3.95/0.98  --qbf_dom_pre_inst                      false
% 3.95/0.98  --qbf_sk_in                             false
% 3.95/0.98  --qbf_pred_elim                         true
% 3.95/0.98  --qbf_split                             512
% 3.95/0.98  
% 3.95/0.98  ------ BMC1 Options
% 3.95/0.98  
% 3.95/0.98  --bmc1_incremental                      false
% 3.95/0.98  --bmc1_axioms                           reachable_all
% 3.95/0.98  --bmc1_min_bound                        0
% 3.95/0.98  --bmc1_max_bound                        -1
% 3.95/0.98  --bmc1_max_bound_default                -1
% 3.95/0.98  --bmc1_symbol_reachability              true
% 3.95/0.98  --bmc1_property_lemmas                  false
% 3.95/0.98  --bmc1_k_induction                      false
% 3.95/0.98  --bmc1_non_equiv_states                 false
% 3.95/0.98  --bmc1_deadlock                         false
% 3.95/0.98  --bmc1_ucm                              false
% 3.95/0.98  --bmc1_add_unsat_core                   none
% 3.95/0.98  --bmc1_unsat_core_children              false
% 3.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/0.98  --bmc1_out_stat                         full
% 3.95/0.98  --bmc1_ground_init                      false
% 3.95/0.98  --bmc1_pre_inst_next_state              false
% 3.95/0.98  --bmc1_pre_inst_state                   false
% 3.95/0.98  --bmc1_pre_inst_reach_state             false
% 3.95/0.98  --bmc1_out_unsat_core                   false
% 3.95/0.98  --bmc1_aig_witness_out                  false
% 3.95/0.98  --bmc1_verbose                          false
% 3.95/0.98  --bmc1_dump_clauses_tptp                false
% 3.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.95/0.98  --bmc1_dump_file                        -
% 3.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.95/0.98  --bmc1_ucm_extend_mode                  1
% 3.95/0.98  --bmc1_ucm_init_mode                    2
% 3.95/0.98  --bmc1_ucm_cone_mode                    none
% 3.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.95/0.98  --bmc1_ucm_relax_model                  4
% 3.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/0.98  --bmc1_ucm_layered_model                none
% 3.95/0.98  --bmc1_ucm_max_lemma_size               10
% 3.95/0.98  
% 3.95/0.98  ------ AIG Options
% 3.95/0.98  
% 3.95/0.98  --aig_mode                              false
% 3.95/0.98  
% 3.95/0.98  ------ Instantiation Options
% 3.95/0.98  
% 3.95/0.98  --instantiation_flag                    true
% 3.95/0.98  --inst_sos_flag                         true
% 3.95/0.98  --inst_sos_phase                        true
% 3.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/0.98  --inst_lit_sel_side                     none
% 3.95/0.98  --inst_solver_per_active                1400
% 3.95/0.98  --inst_solver_calls_frac                1.
% 3.95/0.98  --inst_passive_queue_type               priority_queues
% 3.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/0.98  --inst_passive_queues_freq              [25;2]
% 3.95/0.98  --inst_dismatching                      true
% 3.95/0.98  --inst_eager_unprocessed_to_passive     true
% 3.95/0.98  --inst_prop_sim_given                   true
% 3.95/0.98  --inst_prop_sim_new                     false
% 3.95/0.98  --inst_subs_new                         false
% 3.95/0.98  --inst_eq_res_simp                      false
% 3.95/0.98  --inst_subs_given                       false
% 3.95/0.98  --inst_orphan_elimination               true
% 3.95/0.98  --inst_learning_loop_flag               true
% 3.95/0.98  --inst_learning_start                   3000
% 3.95/0.98  --inst_learning_factor                  2
% 3.95/0.98  --inst_start_prop_sim_after_learn       3
% 3.95/0.98  --inst_sel_renew                        solver
% 3.95/0.98  --inst_lit_activity_flag                true
% 3.95/0.98  --inst_restr_to_given                   false
% 3.95/0.98  --inst_activity_threshold               500
% 3.95/0.98  --inst_out_proof                        true
% 3.95/0.98  
% 3.95/0.98  ------ Resolution Options
% 3.95/0.98  
% 3.95/0.98  --resolution_flag                       false
% 3.95/0.98  --res_lit_sel                           adaptive
% 3.95/0.98  --res_lit_sel_side                      none
% 3.95/0.98  --res_ordering                          kbo
% 3.95/0.98  --res_to_prop_solver                    active
% 3.95/0.98  --res_prop_simpl_new                    false
% 3.95/0.98  --res_prop_simpl_given                  true
% 3.95/0.98  --res_passive_queue_type                priority_queues
% 3.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/0.98  --res_passive_queues_freq               [15;5]
% 3.95/0.98  --res_forward_subs                      full
% 3.95/0.98  --res_backward_subs                     full
% 3.95/0.98  --res_forward_subs_resolution           true
% 3.95/0.98  --res_backward_subs_resolution          true
% 3.95/0.98  --res_orphan_elimination                true
% 3.95/0.98  --res_time_limit                        2.
% 3.95/0.98  --res_out_proof                         true
% 3.95/0.98  
% 3.95/0.98  ------ Superposition Options
% 3.95/0.98  
% 3.95/0.98  --superposition_flag                    true
% 3.95/0.98  --sup_passive_queue_type                priority_queues
% 3.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.95/0.98  --demod_completeness_check              fast
% 3.95/0.98  --demod_use_ground                      true
% 3.95/0.98  --sup_to_prop_solver                    passive
% 3.95/0.98  --sup_prop_simpl_new                    true
% 3.95/0.98  --sup_prop_simpl_given                  true
% 3.95/0.98  --sup_fun_splitting                     true
% 3.95/0.98  --sup_smt_interval                      50000
% 3.95/0.98  
% 3.95/0.98  ------ Superposition Simplification Setup
% 3.95/0.98  
% 3.95/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.95/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.95/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.95/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.95/0.98  --sup_immed_triv                        [TrivRules]
% 3.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_immed_bw_main                     []
% 3.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_input_bw                          []
% 3.95/0.98  
% 3.95/0.98  ------ Combination Options
% 3.95/0.98  
% 3.95/0.98  --comb_res_mult                         3
% 3.95/0.98  --comb_sup_mult                         2
% 3.95/0.98  --comb_inst_mult                        10
% 3.95/0.98  
% 3.95/0.98  ------ Debug Options
% 3.95/0.98  
% 3.95/0.98  --dbg_backtrace                         false
% 3.95/0.98  --dbg_dump_prop_clauses                 false
% 3.95/0.98  --dbg_dump_prop_clauses_file            -
% 3.95/0.98  --dbg_out_stat                          false
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  ------ Proving...
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  % SZS status Theorem for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  fof(f19,conjecture,(
% 3.95/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f20,negated_conjecture,(
% 3.95/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.95/0.98    inference(negated_conjecture,[],[f19])).
% 3.95/0.98  
% 3.95/0.98  fof(f47,plain,(
% 3.95/0.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.95/0.98    inference(ennf_transformation,[],[f20])).
% 3.95/0.98  
% 3.95/0.98  fof(f48,plain,(
% 3.95/0.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.95/0.98    inference(flattening,[],[f47])).
% 3.95/0.98  
% 3.95/0.98  fof(f51,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.95/0.98    introduced(choice_axiom,[])).
% 3.95/0.98  
% 3.95/0.98  fof(f50,plain,(
% 3.95/0.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.95/0.98    introduced(choice_axiom,[])).
% 3.95/0.98  
% 3.95/0.98  fof(f52,plain,(
% 3.95/0.98    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f51,f50])).
% 3.95/0.98  
% 3.95/0.98  fof(f86,plain,(
% 3.95/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f89,plain,(
% 3.95/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f14,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f39,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.95/0.98    inference(ennf_transformation,[],[f14])).
% 3.95/0.98  
% 3.95/0.98  fof(f40,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.95/0.98    inference(flattening,[],[f39])).
% 3.95/0.98  
% 3.95/0.98  fof(f75,plain,(
% 3.95/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f40])).
% 3.95/0.98  
% 3.95/0.98  fof(f87,plain,(
% 3.95/0.98    v1_funct_1(sK3)),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f11,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f35,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.95/0.98    inference(ennf_transformation,[],[f11])).
% 3.95/0.98  
% 3.95/0.98  fof(f36,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/0.98    inference(flattening,[],[f35])).
% 3.95/0.98  
% 3.95/0.98  fof(f49,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/0.98    inference(nnf_transformation,[],[f36])).
% 3.95/0.98  
% 3.95/0.98  fof(f70,plain,(
% 3.95/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/0.98    inference(cnf_transformation,[],[f49])).
% 3.95/0.98  
% 3.95/0.98  fof(f91,plain,(
% 3.95/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f12,axiom,(
% 3.95/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f72,plain,(
% 3.95/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.95/0.98    inference(cnf_transformation,[],[f12])).
% 3.95/0.98  
% 3.95/0.98  fof(f15,axiom,(
% 3.95/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f76,plain,(
% 3.95/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f15])).
% 3.95/0.98  
% 3.95/0.98  fof(f101,plain,(
% 3.95/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.95/0.98    inference(definition_unfolding,[],[f72,f76])).
% 3.95/0.98  
% 3.95/0.98  fof(f84,plain,(
% 3.95/0.98    v1_funct_1(sK2)),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f13,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f37,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.95/0.98    inference(ennf_transformation,[],[f13])).
% 3.95/0.98  
% 3.95/0.98  fof(f38,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.95/0.98    inference(flattening,[],[f37])).
% 3.95/0.98  
% 3.95/0.98  fof(f74,plain,(
% 3.95/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f38])).
% 3.95/0.98  
% 3.95/0.98  fof(f7,axiom,(
% 3.95/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f29,plain,(
% 3.95/0.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.95/0.98    inference(ennf_transformation,[],[f7])).
% 3.95/0.98  
% 3.95/0.98  fof(f30,plain,(
% 3.95/0.98    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.95/0.98    inference(flattening,[],[f29])).
% 3.95/0.98  
% 3.95/0.98  fof(f66,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f30])).
% 3.95/0.98  
% 3.95/0.98  fof(f100,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f66,f76])).
% 3.95/0.98  
% 3.95/0.98  fof(f10,axiom,(
% 3.95/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f34,plain,(
% 3.95/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/0.98    inference(ennf_transformation,[],[f10])).
% 3.95/0.98  
% 3.95/0.98  fof(f69,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/0.98    inference(cnf_transformation,[],[f34])).
% 3.95/0.98  
% 3.95/0.98  fof(f90,plain,(
% 3.95/0.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f16,axiom,(
% 3.95/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f41,plain,(
% 3.95/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.95/0.98    inference(ennf_transformation,[],[f16])).
% 3.95/0.98  
% 3.95/0.98  fof(f42,plain,(
% 3.95/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.95/0.98    inference(flattening,[],[f41])).
% 3.95/0.98  
% 3.95/0.98  fof(f77,plain,(
% 3.95/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f42])).
% 3.95/0.98  
% 3.95/0.98  fof(f85,plain,(
% 3.95/0.98    v1_funct_2(sK2,sK0,sK1)),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f88,plain,(
% 3.95/0.98    v1_funct_2(sK3,sK1,sK0)),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f93,plain,(
% 3.95/0.98    k1_xboole_0 != sK0),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  fof(f9,axiom,(
% 3.95/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f33,plain,(
% 3.95/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/0.98    inference(ennf_transformation,[],[f9])).
% 3.95/0.98  
% 3.95/0.98  fof(f68,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/0.98    inference(cnf_transformation,[],[f33])).
% 3.95/0.98  
% 3.95/0.98  fof(f3,axiom,(
% 3.95/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f58,plain,(
% 3.95/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.95/0.98    inference(cnf_transformation,[],[f3])).
% 3.95/0.98  
% 3.95/0.98  fof(f98,plain,(
% 3.95/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.95/0.98    inference(definition_unfolding,[],[f58,f76])).
% 3.95/0.98  
% 3.95/0.98  fof(f17,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f43,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.95/0.98    inference(ennf_transformation,[],[f17])).
% 3.95/0.98  
% 3.95/0.98  fof(f44,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.95/0.98    inference(flattening,[],[f43])).
% 3.95/0.98  
% 3.95/0.98  fof(f80,plain,(
% 3.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f44])).
% 3.95/0.98  
% 3.95/0.98  fof(f6,axiom,(
% 3.95/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f27,plain,(
% 3.95/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.95/0.98    inference(ennf_transformation,[],[f6])).
% 3.95/0.98  
% 3.95/0.98  fof(f28,plain,(
% 3.95/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.95/0.98    inference(flattening,[],[f27])).
% 3.95/0.98  
% 3.95/0.98  fof(f64,plain,(
% 3.95/0.98    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f28])).
% 3.95/0.98  
% 3.95/0.98  fof(f18,axiom,(
% 3.95/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f45,plain,(
% 3.95/0.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.95/0.98    inference(ennf_transformation,[],[f18])).
% 3.95/0.98  
% 3.95/0.98  fof(f46,plain,(
% 3.95/0.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.95/0.98    inference(flattening,[],[f45])).
% 3.95/0.98  
% 3.95/0.98  fof(f82,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f46])).
% 3.95/0.98  
% 3.95/0.98  fof(f1,axiom,(
% 3.95/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f53,plain,(
% 3.95/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.95/0.98    inference(cnf_transformation,[],[f1])).
% 3.95/0.98  
% 3.95/0.98  fof(f97,plain,(
% 3.95/0.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.95/0.98    inference(definition_unfolding,[],[f53,f76])).
% 3.95/0.98  
% 3.95/0.98  fof(f8,axiom,(
% 3.95/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f31,plain,(
% 3.95/0.98    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.95/0.98    inference(ennf_transformation,[],[f8])).
% 3.95/0.98  
% 3.95/0.98  fof(f32,plain,(
% 3.95/0.98    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.95/0.98    inference(flattening,[],[f31])).
% 3.95/0.98  
% 3.95/0.98  fof(f67,plain,(
% 3.95/0.98    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f32])).
% 3.95/0.98  
% 3.95/0.98  fof(f95,plain,(
% 3.95/0.98    k2_funct_1(sK2) != sK3),
% 3.95/0.98    inference(cnf_transformation,[],[f52])).
% 3.95/0.98  
% 3.95/0.98  cnf(c_39,negated_conjecture,
% 3.95/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.95/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1273,plain,
% 3.95/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_36,negated_conjecture,
% 3.95/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.95/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1276,plain,
% 3.95/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_22,plain,
% 3.95/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X3)
% 3.95/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.95/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1284,plain,
% 3.95/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.95/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.95/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.95/0.98      | v1_funct_1(X5) != iProver_top
% 3.95/0.98      | v1_funct_1(X4) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5022,plain,
% 3.95/0.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.95/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.95/0.98      | v1_funct_1(X2) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1276,c_1284]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_38,negated_conjecture,
% 3.95/0.98      ( v1_funct_1(sK3) ),
% 3.95/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_45,plain,
% 3.95/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5150,plain,
% 3.95/0.98      ( v1_funct_1(X2) != iProver_top
% 3.95/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.95/0.98      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_5022,c_45]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5151,plain,
% 3.95/0.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.95/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.95/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.95/0.98      inference(renaming,[status(thm)],[c_5150]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5159,plain,
% 3.95/0.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.95/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1273,c_5151]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_18,plain,
% 3.95/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.95/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.95/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.95/0.98      | X3 = X2 ),
% 3.95/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_34,negated_conjecture,
% 3.95/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.95/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_442,plain,
% 3.95/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | X3 = X0
% 3.95/0.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.95/0.98      | k6_partfun1(sK0) != X3
% 3.95/0.98      | sK0 != X2
% 3.95/0.98      | sK0 != X1 ),
% 3.95/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_443,plain,
% 3.95/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.95/0.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.95/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.95/0.98      inference(unflattening,[status(thm)],[c_442]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_19,plain,
% 3.95/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.95/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_451,plain,
% 3.95/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.95/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.95/0.98      inference(forward_subsumption_resolution,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_443,c_19]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1269,plain,
% 3.95/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.95/0.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_41,negated_conjecture,
% 3.95/0.98      ( v1_funct_1(sK2) ),
% 3.95/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_20,plain,
% 3.95/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.95/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X3) ),
% 3.95/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1388,plain,
% 3.95/0.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.95/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.95/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.95/0.98      | ~ v1_funct_1(sK3)
% 3.95/0.98      | ~ v1_funct_1(sK2) ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2115,plain,
% 3.95/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_1269,c_41,c_39,c_38,c_36,c_451,c_1388]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5160,plain,
% 3.95/0.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.95/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.95/0.98      inference(light_normalisation,[status(thm)],[c_5159,c_2115]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_42,plain,
% 3.95/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5428,plain,
% 3.95/0.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_5160,c_42]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_13,plain,
% 3.95/0.98      ( ~ v2_funct_1(X0)
% 3.95/0.98      | ~ v1_relat_1(X0)
% 3.95/0.98      | ~ v1_relat_1(X1)
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X1)
% 3.95/0.98      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 3.95/0.98      | k2_funct_1(X0) = X1
% 3.95/0.98      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.95/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1291,plain,
% 3.95/0.98      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.95/0.98      | k2_funct_1(X1) = X0
% 3.95/0.98      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.95/0.98      | v2_funct_1(X1) != iProver_top
% 3.95/0.98      | v1_relat_1(X1) != iProver_top
% 3.95/0.98      | v1_relat_1(X0) != iProver_top
% 3.95/0.98      | v1_funct_1(X1) != iProver_top
% 3.95/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5430,plain,
% 3.95/0.98      ( k2_funct_1(sK3) = sK2
% 3.95/0.98      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.95/0.98      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.95/0.98      | v2_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_relat_1(sK3) != iProver_top
% 3.95/0.98      | v1_relat_1(sK2) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_5428,c_1291]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_16,plain,
% 3.95/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.95/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1288,plain,
% 3.95/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.95/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2331,plain,
% 3.95/0.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1273,c_1288]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_35,negated_conjecture,
% 3.95/0.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.95/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2332,plain,
% 3.95/0.98      ( k2_relat_1(sK2) = sK1 ),
% 3.95/0.98      inference(light_normalisation,[status(thm)],[c_2331,c_35]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2330,plain,
% 3.95/0.98      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1276,c_1288]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_23,plain,
% 3.95/0.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.95/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.95/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.95/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.95/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.95/0.98      | ~ v1_funct_1(X2)
% 3.95/0.98      | ~ v1_funct_1(X3)
% 3.95/0.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_455,plain,
% 3.95/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.95/0.98      | ~ v1_funct_2(X3,X2,X1)
% 3.95/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.95/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X3)
% 3.95/0.98      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.95/0.98      | k2_relset_1(X1,X2,X0) = X2
% 3.95/0.98      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.95/0.98      | sK0 != X2 ),
% 3.95/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_456,plain,
% 3.95/0.98      ( ~ v1_funct_2(X0,X1,sK0)
% 3.95/0.98      | ~ v1_funct_2(X2,sK0,X1)
% 3.95/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.95/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X2)
% 3.95/0.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.95/0.98      | k2_relset_1(X1,sK0,X0) = sK0
% 3.95/0.98      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.95/0.98      inference(unflattening,[status(thm)],[c_455]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_543,plain,
% 3.95/0.98      ( ~ v1_funct_2(X0,X1,sK0)
% 3.95/0.98      | ~ v1_funct_2(X2,sK0,X1)
% 3.95/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.95/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X2)
% 3.95/0.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.95/0.98      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.95/0.98      inference(equality_resolution_simp,[status(thm)],[c_456]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1268,plain,
% 3.95/0.98      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.95/0.98      | k2_relset_1(X0,sK0,X2) = sK0
% 3.95/0.98      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.95/0.98      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.95/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.95/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.95/0.98      | v1_funct_1(X2) != iProver_top
% 3.95/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1815,plain,
% 3.95/0.98      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.95/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.95/0.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.95/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.95/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.95/0.98      inference(equality_resolution,[status(thm)],[c_1268]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_40,negated_conjecture,
% 3.95/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.95/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_43,plain,
% 3.95/0.98      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_44,plain,
% 3.95/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_37,negated_conjecture,
% 3.95/0.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.95/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_46,plain,
% 3.95/0.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_47,plain,
% 3.95/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2122,plain,
% 3.95/0.98      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_1815,c_42,c_43,c_44,c_45,c_46,c_47]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2333,plain,
% 3.95/0.98      ( k2_relat_1(sK3) = sK0 ),
% 3.95/0.98      inference(light_normalisation,[status(thm)],[c_2330,c_2122]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5431,plain,
% 3.95/0.98      ( k2_funct_1(sK3) = sK2
% 3.95/0.98      | k1_relat_1(sK3) != sK1
% 3.95/0.98      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.95/0.98      | v2_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_relat_1(sK3) != iProver_top
% 3.95/0.98      | v1_relat_1(sK2) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.95/0.98      inference(light_normalisation,[status(thm)],[c_5430,c_2332,c_2333]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5432,plain,
% 3.95/0.98      ( k2_funct_1(sK3) = sK2
% 3.95/0.98      | k1_relat_1(sK3) != sK1
% 3.95/0.98      | v2_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_relat_1(sK3) != iProver_top
% 3.95/0.98      | v1_relat_1(sK2) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.95/0.98      inference(equality_resolution_simp,[status(thm)],[c_5431]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_32,negated_conjecture,
% 3.95/0.98      ( k1_xboole_0 != sK0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_732,plain,( X0 = X0 ),theory(equality) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_763,plain,
% 3.95/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_732]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_733,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1386,plain,
% 3.95/0.98      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_733]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1387,plain,
% 3.95/0.98      ( sK0 != k1_xboole_0
% 3.95/0.98      | k1_xboole_0 = sK0
% 3.95/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_1386]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_15,plain,
% 3.95/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | v1_relat_1(X0) ),
% 3.95/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1434,plain,
% 3.95/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.95/0.98      | v1_relat_1(sK3) ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1783,plain,
% 3.95/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.95/0.98      | v1_relat_1(sK3) ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_1434]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1784,plain,
% 3.95/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.95/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2041,plain,
% 3.95/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.95/0.98      | v1_relat_1(sK2) ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2042,plain,
% 3.95/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.95/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_4,plain,
% 3.95/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.95/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2927,plain,
% 3.95/0.98      ( v2_funct_1(k6_partfun1(sK0)) ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2928,plain,
% 3.95/0.98      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_2927]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_25,plain,
% 3.95/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.95/0.98      | ~ v1_funct_2(X3,X4,X1)
% 3.95/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.95/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | v2_funct_1(X0)
% 3.95/0.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X3)
% 3.95/0.98      | k2_relset_1(X4,X1,X3) != X1
% 3.95/0.98      | k1_xboole_0 = X2 ),
% 3.95/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1282,plain,
% 3.95/0.98      ( k2_relset_1(X0,X1,X2) != X1
% 3.95/0.98      | k1_xboole_0 = X3
% 3.95/0.98      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.95/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.95/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.95/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.95/0.98      | v2_funct_1(X4) = iProver_top
% 3.95/0.98      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 3.95/0.98      | v1_funct_1(X4) != iProver_top
% 3.95/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5519,plain,
% 3.95/0.98      ( k1_xboole_0 = X0
% 3.95/0.98      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.95/0.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.95/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.95/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.95/0.98      | v2_funct_1(X1) = iProver_top
% 3.95/0.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 3.95/0.98      | v1_funct_1(X1) != iProver_top
% 3.95/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_35,c_1282]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5750,plain,
% 3.95/0.98      ( v1_funct_1(X1) != iProver_top
% 3.95/0.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 3.95/0.98      | v2_funct_1(X1) = iProver_top
% 3.95/0.98      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.95/0.98      | k1_xboole_0 = X0
% 3.95/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_5519,c_42,c_43,c_44]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5751,plain,
% 3.95/0.98      ( k1_xboole_0 = X0
% 3.95/0.98      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.95/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.95/0.98      | v2_funct_1(X1) = iProver_top
% 3.95/0.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 3.95/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.95/0.98      inference(renaming,[status(thm)],[c_5750]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5754,plain,
% 3.95/0.98      ( sK0 = k1_xboole_0
% 3.95/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.95/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.95/0.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.95/0.98      | v2_funct_1(sK3) = iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_2115,c_5751]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6594,plain,
% 3.95/0.98      ( v2_funct_1(sK3) = iProver_top ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_5754,c_45,c_46,c_47,c_32,c_763,c_1387,c_2928]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_12,plain,
% 3.95/0.98      ( ~ v2_funct_1(X0)
% 3.95/0.98      | ~ v1_relat_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 3.95/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1292,plain,
% 3.95/0.98      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 3.95/0.98      | v2_funct_1(X0) != iProver_top
% 3.95/0.98      | v1_relat_1(X0) != iProver_top
% 3.95/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6600,plain,
% 3.95/0.98      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 3.95/0.98      | v1_relat_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_6594,c_1292]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_29,plain,
% 3.95/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.95/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.98      | ~ v2_funct_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | k2_relset_1(X1,X2,X0) != X2
% 3.95/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.95/0.98      | k1_xboole_0 = X2 ),
% 3.95/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1278,plain,
% 3.95/0.98      ( k2_relset_1(X0,X1,X2) != X1
% 3.95/0.98      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 3.95/0.98      | k1_xboole_0 = X1
% 3.95/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.95/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.95/0.98      | v2_funct_1(X2) != iProver_top
% 3.95/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2872,plain,
% 3.95/0.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 3.95/0.98      | sK0 = k1_xboole_0
% 3.95/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.95/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.95/0.98      | v2_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_2122,c_1278]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3345,plain,
% 3.95/0.98      ( v2_funct_1(sK3) != iProver_top
% 3.95/0.98      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_2872,c_45,c_46,c_47,c_32,c_763,c_1387]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3346,plain,
% 3.95/0.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 3.95/0.98      | v2_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(renaming,[status(thm)],[c_3345]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6605,plain,
% 3.95/0.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_6594,c_3346]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6607,plain,
% 3.95/0.98      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 3.95/0.98      | v1_relat_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_6600,c_6605]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1,plain,
% 3.95/0.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6608,plain,
% 3.95/0.98      ( k1_relat_1(sK3) = sK1
% 3.95/0.98      | v1_relat_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_6607,c_1]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_7912,plain,
% 3.95/0.98      ( k2_funct_1(sK3) = sK2 ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_5432,c_42,c_44,c_45,c_46,c_47,c_32,c_763,c_1387,
% 3.95/0.98                 c_1784,c_2042,c_2928,c_5754,c_6608]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14,plain,
% 3.95/0.98      ( ~ v2_funct_1(X0)
% 3.95/0.98      | ~ v1_relat_1(X0)
% 3.95/0.98      | ~ v1_funct_1(X0)
% 3.95/0.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1290,plain,
% 3.95/0.98      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.95/0.98      | v2_funct_1(X0) != iProver_top
% 3.95/0.98      | v1_relat_1(X0) != iProver_top
% 3.95/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6603,plain,
% 3.95/0.98      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.95/0.98      | v1_relat_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_6594,c_1290]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3774,plain,
% 3.95/0.98      ( ~ v2_funct_1(sK3)
% 3.95/0.98      | ~ v1_relat_1(sK3)
% 3.95/0.98      | ~ v1_funct_1(sK3)
% 3.95/0.98      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3775,plain,
% 3.95/0.98      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.95/0.98      | v2_funct_1(sK3) != iProver_top
% 3.95/0.98      | v1_relat_1(sK3) != iProver_top
% 3.95/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_3774]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6806,plain,
% 3.95/0.98      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.95/0.98      inference(global_propositional_subsumption,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_6603,c_45,c_46,c_47,c_32,c_763,c_1387,c_1784,c_2928,
% 3.95/0.98                 c_3775,c_5754]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_7914,plain,
% 3.95/0.98      ( k2_funct_1(sK2) = sK3 ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_7912,c_6806]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_30,negated_conjecture,
% 3.95/0.98      ( k2_funct_1(sK2) != sK3 ),
% 3.95/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(contradiction,plain,
% 3.95/0.98      ( $false ),
% 3.95/0.98      inference(minisat,[status(thm)],[c_7914,c_30]) ).
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  ------                               Statistics
% 3.95/0.98  
% 3.95/0.98  ------ General
% 3.95/0.98  
% 3.95/0.98  abstr_ref_over_cycles:                  0
% 3.95/0.98  abstr_ref_under_cycles:                 0
% 3.95/0.98  gc_basic_clause_elim:                   0
% 3.95/0.98  forced_gc_time:                         0
% 3.95/0.98  parsing_time:                           0.01
% 3.95/0.98  unif_index_cands_time:                  0.
% 3.95/0.98  unif_index_add_time:                    0.
% 3.95/0.98  orderings_time:                         0.
% 3.95/0.98  out_proof_time:                         0.013
% 3.95/0.98  total_time:                             0.355
% 3.95/0.98  num_of_symbols:                         51
% 3.95/0.98  num_of_terms:                           12953
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing
% 3.95/0.98  
% 3.95/0.98  num_of_splits:                          0
% 3.95/0.98  num_of_split_atoms:                     0
% 3.95/0.98  num_of_reused_defs:                     0
% 3.95/0.98  num_eq_ax_congr_red:                    0
% 3.95/0.98  num_of_sem_filtered_clauses:            1
% 3.95/0.98  num_of_subtypes:                        0
% 3.95/0.98  monotx_restored_types:                  0
% 3.95/0.98  sat_num_of_epr_types:                   0
% 3.95/0.98  sat_num_of_non_cyclic_types:            0
% 3.95/0.98  sat_guarded_non_collapsed_types:        0
% 3.95/0.98  num_pure_diseq_elim:                    0
% 3.95/0.98  simp_replaced_by:                       0
% 3.95/0.98  res_preprocessed:                       190
% 3.95/0.98  prep_upred:                             0
% 3.95/0.98  prep_unflattend:                        12
% 3.95/0.98  smt_new_axioms:                         0
% 3.95/0.98  pred_elim_cands:                        5
% 3.95/0.98  pred_elim:                              1
% 3.95/0.98  pred_elim_cl:                           1
% 3.95/0.98  pred_elim_cycles:                       3
% 3.95/0.98  merged_defs:                            0
% 3.95/0.98  merged_defs_ncl:                        0
% 3.95/0.98  bin_hyper_res:                          0
% 3.95/0.98  prep_cycles:                            4
% 3.95/0.98  pred_elim_time:                         0.004
% 3.95/0.98  splitting_time:                         0.
% 3.95/0.98  sem_filter_time:                        0.
% 3.95/0.98  monotx_time:                            0.001
% 3.95/0.98  subtype_inf_time:                       0.
% 3.95/0.98  
% 3.95/0.98  ------ Problem properties
% 3.95/0.98  
% 3.95/0.98  clauses:                                39
% 3.95/0.98  conjectures:                            11
% 3.95/0.98  epr:                                    7
% 3.95/0.98  horn:                                   35
% 3.95/0.98  ground:                                 12
% 3.95/0.98  unary:                                  16
% 3.95/0.98  binary:                                 3
% 3.95/0.98  lits:                                   143
% 3.95/0.98  lits_eq:                                33
% 3.95/0.98  fd_pure:                                0
% 3.95/0.98  fd_pseudo:                              0
% 3.95/0.98  fd_cond:                                4
% 3.95/0.98  fd_pseudo_cond:                         1
% 3.95/0.98  ac_symbols:                             0
% 3.95/0.98  
% 3.95/0.98  ------ Propositional Solver
% 3.95/0.98  
% 3.95/0.98  prop_solver_calls:                      29
% 3.95/0.98  prop_fast_solver_calls:                 1758
% 3.95/0.98  smt_solver_calls:                       0
% 3.95/0.98  smt_fast_solver_calls:                  0
% 3.95/0.98  prop_num_of_clauses:                    4205
% 3.95/0.98  prop_preprocess_simplified:             10024
% 3.95/0.98  prop_fo_subsumed:                       93
% 3.95/0.98  prop_solver_time:                       0.
% 3.95/0.98  smt_solver_time:                        0.
% 3.95/0.98  smt_fast_solver_time:                   0.
% 3.95/0.98  prop_fast_solver_time:                  0.
% 3.95/0.98  prop_unsat_core_time:                   0.
% 3.95/0.98  
% 3.95/0.98  ------ QBF
% 3.95/0.98  
% 3.95/0.98  qbf_q_res:                              0
% 3.95/0.98  qbf_num_tautologies:                    0
% 3.95/0.98  qbf_prep_cycles:                        0
% 3.95/0.98  
% 3.95/0.98  ------ BMC1
% 3.95/0.98  
% 3.95/0.98  bmc1_current_bound:                     -1
% 3.95/0.98  bmc1_last_solved_bound:                 -1
% 3.95/0.98  bmc1_unsat_core_size:                   -1
% 3.95/0.98  bmc1_unsat_core_parents_size:           -1
% 3.95/0.98  bmc1_merge_next_fun:                    0
% 3.95/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.95/0.98  
% 3.95/0.98  ------ Instantiation
% 3.95/0.98  
% 3.95/0.98  inst_num_of_clauses:                    1072
% 3.95/0.98  inst_num_in_passive:                    126
% 3.95/0.98  inst_num_in_active:                     466
% 3.95/0.98  inst_num_in_unprocessed:                480
% 3.95/0.98  inst_num_of_loops:                      480
% 3.95/0.98  inst_num_of_learning_restarts:          0
% 3.95/0.98  inst_num_moves_active_passive:          12
% 3.95/0.98  inst_lit_activity:                      0
% 3.95/0.98  inst_lit_activity_moves:                0
% 3.95/0.98  inst_num_tautologies:                   0
% 3.95/0.98  inst_num_prop_implied:                  0
% 3.95/0.98  inst_num_existing_simplified:           0
% 3.95/0.98  inst_num_eq_res_simplified:             0
% 3.95/0.98  inst_num_child_elim:                    0
% 3.95/0.98  inst_num_of_dismatching_blockings:      173
% 3.95/0.98  inst_num_of_non_proper_insts:           799
% 3.95/0.98  inst_num_of_duplicates:                 0
% 3.95/0.98  inst_inst_num_from_inst_to_res:         0
% 3.95/0.98  inst_dismatching_checking_time:         0.
% 3.95/0.98  
% 3.95/0.98  ------ Resolution
% 3.95/0.98  
% 3.95/0.98  res_num_of_clauses:                     0
% 3.95/0.98  res_num_in_passive:                     0
% 3.95/0.98  res_num_in_active:                      0
% 3.95/0.98  res_num_of_loops:                       194
% 3.95/0.98  res_forward_subset_subsumed:            45
% 3.95/0.98  res_backward_subset_subsumed:           0
% 3.95/0.98  res_forward_subsumed:                   0
% 3.95/0.98  res_backward_subsumed:                  0
% 3.95/0.98  res_forward_subsumption_resolution:     2
% 3.95/0.98  res_backward_subsumption_resolution:    0
% 3.95/0.98  res_clause_to_clause_subsumption:       231
% 3.95/0.98  res_orphan_elimination:                 0
% 3.95/0.98  res_tautology_del:                      23
% 3.95/0.98  res_num_eq_res_simplified:              1
% 3.95/0.98  res_num_sel_changes:                    0
% 3.95/0.98  res_moves_from_active_to_pass:          0
% 3.95/0.98  
% 3.95/0.98  ------ Superposition
% 3.95/0.98  
% 3.95/0.98  sup_time_total:                         0.
% 3.95/0.98  sup_time_generating:                    0.
% 3.95/0.98  sup_time_sim_full:                      0.
% 3.95/0.98  sup_time_sim_immed:                     0.
% 3.95/0.98  
% 3.95/0.98  sup_num_of_clauses:                     126
% 3.95/0.98  sup_num_in_active:                      87
% 3.95/0.98  sup_num_in_passive:                     39
% 3.95/0.98  sup_num_of_loops:                       95
% 3.95/0.98  sup_fw_superposition:                   59
% 3.95/0.98  sup_bw_superposition:                   60
% 3.95/0.98  sup_immediate_simplified:               38
% 3.95/0.98  sup_given_eliminated:                   0
% 3.95/0.98  comparisons_done:                       0
% 3.95/0.98  comparisons_avoided:                    2
% 3.95/0.98  
% 3.95/0.98  ------ Simplifications
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  sim_fw_subset_subsumed:                 12
% 3.95/0.98  sim_bw_subset_subsumed:                 3
% 3.95/0.98  sim_fw_subsumed:                        5
% 3.95/0.98  sim_bw_subsumed:                        0
% 3.95/0.98  sim_fw_subsumption_res:                 0
% 3.95/0.98  sim_bw_subsumption_res:                 0
% 3.95/0.98  sim_tautology_del:                      0
% 3.95/0.98  sim_eq_tautology_del:                   6
% 3.95/0.98  sim_eq_res_simp:                        1
% 3.95/0.98  sim_fw_demodulated:                     6
% 3.95/0.98  sim_bw_demodulated:                     6
% 3.95/0.98  sim_light_normalised:                   18
% 3.95/0.98  sim_joinable_taut:                      0
% 3.95/0.98  sim_joinable_simp:                      0
% 3.95/0.98  sim_ac_normalised:                      0
% 3.95/0.98  sim_smt_subsumption:                    0
% 3.95/0.98  
%------------------------------------------------------------------------------
