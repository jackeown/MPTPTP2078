%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:36 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  210 (1160 expanded)
%              Number of clauses        :  126 ( 325 expanded)
%              Number of leaves         :   23 ( 307 expanded)
%              Depth                    :   22
%              Number of atoms          :  795 (9691 expanded)
%              Number of equality atoms :  392 (3557 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f49,f48])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f19,axiom,(
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

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1310,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1286,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1311,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2945,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1311])).

cnf(c_3057,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_2945])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1283,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2946,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1311])).

cnf(c_3060,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_2946])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1281,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1305,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1309,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4020,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1309])).

cnf(c_9704,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_4020])).

cnf(c_9864,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9704,c_3060])).

cnf(c_9865,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9864])).

cnf(c_9874,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3060,c_9865])).

cnf(c_34,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1289,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3083,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1289])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1357,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1448,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1357])).

cnf(c_1650,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_3311,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3083,c_40,c_39,c_38,c_34,c_32,c_30,c_1650])).

cnf(c_9878,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9874,c_3311])).

cnf(c_9980,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3057,c_9878])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1294,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4212,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1294])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4246,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4212,c_44])).

cnf(c_4247,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4246])).

cnf(c_4254,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_4247])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_431,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_439,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_431,c_18])).

cnf(c_1279,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1397,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2114,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1279,c_40,c_38,c_37,c_35,c_439,c_1397])).

cnf(c_4255,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4254,c_2114])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4414,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4255,c_41])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1292,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4754,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1292])).

cnf(c_42,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4761,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4754,c_41,c_42,c_43])).

cnf(c_4762,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4761])).

cnf(c_4765,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2114,c_4762])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_727,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_758,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_728,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1395,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_1396,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_9,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2964,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2965,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2964])).

cnf(c_4786,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4765,c_44,c_45,c_46,c_31,c_758,c_1396,c_2965])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1299,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4791,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4786,c_1299])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_443,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_444,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_532,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_444])).

cnf(c_1278,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_1796,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1278])).

cnf(c_2121,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1796,c_41,c_42,c_43,c_44,c_45,c_46])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1288,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2969,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2121,c_1288])).

cnf(c_3629,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2969,c_44,c_45,c_46,c_31,c_758,c_1396])).

cnf(c_3630,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3629])).

cnf(c_4795,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_4786,c_3630])).

cnf(c_4797,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4791,c_4795])).

cnf(c_4,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4798,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4797,c_4])).

cnf(c_5000,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4798,c_44,c_3057])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1308,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3075,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3057,c_1308])).

cnf(c_5003,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_5000,c_3075])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1307,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2894,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1307])).

cnf(c_4984,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_2894])).

cnf(c_1287,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3106,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1299])).

cnf(c_2968,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1288])).

cnf(c_1358,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1474,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_1663,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_3042,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2968,c_40,c_39,c_38,c_34,c_32,c_30,c_1663])).

cnf(c_3107,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3106,c_3042])).

cnf(c_3108,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3107,c_4])).

cnf(c_3115,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3108,c_41,c_3060])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1302,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3021,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1302])).

cnf(c_3072,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3021,c_41,c_3060])).

cnf(c_3117,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_3115,c_3072])).

cnf(c_4987,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4984,c_3117])).

cnf(c_5105,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4987,c_3060])).

cnf(c_9987,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_9980,c_4414,c_5003,c_5105])).

cnf(c_29,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9987,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.32  % CPULimit   : 60
% 0.18/0.32  % WCLimit    : 600
% 0.18/0.32  % DateTime   : Tue Dec  1 18:31:57 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 7.39/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/1.48  
% 7.39/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.39/1.48  
% 7.39/1.48  ------  iProver source info
% 7.39/1.48  
% 7.39/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.39/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.39/1.48  git: non_committed_changes: false
% 7.39/1.48  git: last_make_outside_of_git: false
% 7.39/1.48  
% 7.39/1.48  ------ 
% 7.39/1.48  
% 7.39/1.48  ------ Input Options
% 7.39/1.48  
% 7.39/1.48  --out_options                           all
% 7.39/1.48  --tptp_safe_out                         true
% 7.39/1.48  --problem_path                          ""
% 7.39/1.48  --include_path                          ""
% 7.39/1.48  --clausifier                            res/vclausify_rel
% 7.39/1.48  --clausifier_options                    ""
% 7.39/1.48  --stdin                                 false
% 7.39/1.48  --stats_out                             all
% 7.39/1.48  
% 7.39/1.48  ------ General Options
% 7.39/1.48  
% 7.39/1.48  --fof                                   false
% 7.39/1.48  --time_out_real                         305.
% 7.39/1.48  --time_out_virtual                      -1.
% 7.39/1.48  --symbol_type_check                     false
% 7.39/1.48  --clausify_out                          false
% 7.39/1.48  --sig_cnt_out                           false
% 7.39/1.48  --trig_cnt_out                          false
% 7.39/1.48  --trig_cnt_out_tolerance                1.
% 7.39/1.48  --trig_cnt_out_sk_spl                   false
% 7.39/1.48  --abstr_cl_out                          false
% 7.39/1.48  
% 7.39/1.48  ------ Global Options
% 7.39/1.48  
% 7.39/1.48  --schedule                              default
% 7.39/1.48  --add_important_lit                     false
% 7.39/1.48  --prop_solver_per_cl                    1000
% 7.39/1.48  --min_unsat_core                        false
% 7.39/1.48  --soft_assumptions                      false
% 7.39/1.48  --soft_lemma_size                       3
% 7.39/1.48  --prop_impl_unit_size                   0
% 7.39/1.48  --prop_impl_unit                        []
% 7.39/1.48  --share_sel_clauses                     true
% 7.39/1.48  --reset_solvers                         false
% 7.39/1.48  --bc_imp_inh                            [conj_cone]
% 7.39/1.48  --conj_cone_tolerance                   3.
% 7.39/1.48  --extra_neg_conj                        none
% 7.39/1.48  --large_theory_mode                     true
% 7.39/1.48  --prolific_symb_bound                   200
% 7.39/1.48  --lt_threshold                          2000
% 7.39/1.48  --clause_weak_htbl                      true
% 7.39/1.48  --gc_record_bc_elim                     false
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing Options
% 7.39/1.48  
% 7.39/1.48  --preprocessing_flag                    true
% 7.39/1.48  --time_out_prep_mult                    0.1
% 7.39/1.48  --splitting_mode                        input
% 7.39/1.48  --splitting_grd                         true
% 7.39/1.48  --splitting_cvd                         false
% 7.39/1.48  --splitting_cvd_svl                     false
% 7.39/1.48  --splitting_nvd                         32
% 7.39/1.48  --sub_typing                            true
% 7.39/1.48  --prep_gs_sim                           true
% 7.39/1.48  --prep_unflatten                        true
% 7.39/1.48  --prep_res_sim                          true
% 7.39/1.48  --prep_upred                            true
% 7.39/1.48  --prep_sem_filter                       exhaustive
% 7.39/1.48  --prep_sem_filter_out                   false
% 7.39/1.48  --pred_elim                             true
% 7.39/1.48  --res_sim_input                         true
% 7.39/1.48  --eq_ax_congr_red                       true
% 7.39/1.48  --pure_diseq_elim                       true
% 7.39/1.48  --brand_transform                       false
% 7.39/1.48  --non_eq_to_eq                          false
% 7.39/1.48  --prep_def_merge                        true
% 7.39/1.48  --prep_def_merge_prop_impl              false
% 7.39/1.48  --prep_def_merge_mbd                    true
% 7.39/1.48  --prep_def_merge_tr_red                 false
% 7.39/1.48  --prep_def_merge_tr_cl                  false
% 7.39/1.48  --smt_preprocessing                     true
% 7.39/1.48  --smt_ac_axioms                         fast
% 7.39/1.48  --preprocessed_out                      false
% 7.39/1.48  --preprocessed_stats                    false
% 7.39/1.48  
% 7.39/1.48  ------ Abstraction refinement Options
% 7.39/1.48  
% 7.39/1.48  --abstr_ref                             []
% 7.39/1.48  --abstr_ref_prep                        false
% 7.39/1.48  --abstr_ref_until_sat                   false
% 7.39/1.48  --abstr_ref_sig_restrict                funpre
% 7.39/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.39/1.48  --abstr_ref_under                       []
% 7.39/1.48  
% 7.39/1.48  ------ SAT Options
% 7.39/1.48  
% 7.39/1.48  --sat_mode                              false
% 7.39/1.48  --sat_fm_restart_options                ""
% 7.39/1.48  --sat_gr_def                            false
% 7.39/1.48  --sat_epr_types                         true
% 7.39/1.48  --sat_non_cyclic_types                  false
% 7.39/1.48  --sat_finite_models                     false
% 7.39/1.48  --sat_fm_lemmas                         false
% 7.39/1.48  --sat_fm_prep                           false
% 7.39/1.48  --sat_fm_uc_incr                        true
% 7.39/1.48  --sat_out_model                         small
% 7.39/1.48  --sat_out_clauses                       false
% 7.39/1.48  
% 7.39/1.48  ------ QBF Options
% 7.39/1.48  
% 7.39/1.48  --qbf_mode                              false
% 7.39/1.48  --qbf_elim_univ                         false
% 7.39/1.48  --qbf_dom_inst                          none
% 7.39/1.48  --qbf_dom_pre_inst                      false
% 7.39/1.48  --qbf_sk_in                             false
% 7.39/1.48  --qbf_pred_elim                         true
% 7.39/1.48  --qbf_split                             512
% 7.39/1.48  
% 7.39/1.48  ------ BMC1 Options
% 7.39/1.48  
% 7.39/1.48  --bmc1_incremental                      false
% 7.39/1.48  --bmc1_axioms                           reachable_all
% 7.39/1.48  --bmc1_min_bound                        0
% 7.39/1.48  --bmc1_max_bound                        -1
% 7.39/1.48  --bmc1_max_bound_default                -1
% 7.39/1.48  --bmc1_symbol_reachability              true
% 7.39/1.48  --bmc1_property_lemmas                  false
% 7.39/1.48  --bmc1_k_induction                      false
% 7.39/1.48  --bmc1_non_equiv_states                 false
% 7.39/1.48  --bmc1_deadlock                         false
% 7.39/1.48  --bmc1_ucm                              false
% 7.39/1.48  --bmc1_add_unsat_core                   none
% 7.39/1.48  --bmc1_unsat_core_children              false
% 7.39/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.39/1.48  --bmc1_out_stat                         full
% 7.39/1.48  --bmc1_ground_init                      false
% 7.39/1.48  --bmc1_pre_inst_next_state              false
% 7.39/1.48  --bmc1_pre_inst_state                   false
% 7.39/1.48  --bmc1_pre_inst_reach_state             false
% 7.39/1.48  --bmc1_out_unsat_core                   false
% 7.39/1.48  --bmc1_aig_witness_out                  false
% 7.39/1.48  --bmc1_verbose                          false
% 7.39/1.48  --bmc1_dump_clauses_tptp                false
% 7.39/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.39/1.48  --bmc1_dump_file                        -
% 7.39/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.39/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.39/1.48  --bmc1_ucm_extend_mode                  1
% 7.39/1.48  --bmc1_ucm_init_mode                    2
% 7.39/1.48  --bmc1_ucm_cone_mode                    none
% 7.39/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.39/1.48  --bmc1_ucm_relax_model                  4
% 7.39/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.39/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.39/1.48  --bmc1_ucm_layered_model                none
% 7.39/1.48  --bmc1_ucm_max_lemma_size               10
% 7.39/1.48  
% 7.39/1.48  ------ AIG Options
% 7.39/1.48  
% 7.39/1.48  --aig_mode                              false
% 7.39/1.48  
% 7.39/1.48  ------ Instantiation Options
% 7.39/1.48  
% 7.39/1.48  --instantiation_flag                    true
% 7.39/1.48  --inst_sos_flag                         true
% 7.39/1.48  --inst_sos_phase                        true
% 7.39/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.39/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.39/1.48  --inst_lit_sel_side                     num_symb
% 7.39/1.48  --inst_solver_per_active                1400
% 7.39/1.48  --inst_solver_calls_frac                1.
% 7.39/1.48  --inst_passive_queue_type               priority_queues
% 7.39/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.39/1.48  --inst_passive_queues_freq              [25;2]
% 7.39/1.48  --inst_dismatching                      true
% 7.39/1.48  --inst_eager_unprocessed_to_passive     true
% 7.39/1.48  --inst_prop_sim_given                   true
% 7.39/1.48  --inst_prop_sim_new                     false
% 7.39/1.48  --inst_subs_new                         false
% 7.39/1.48  --inst_eq_res_simp                      false
% 7.39/1.48  --inst_subs_given                       false
% 7.39/1.48  --inst_orphan_elimination               true
% 7.39/1.48  --inst_learning_loop_flag               true
% 7.39/1.48  --inst_learning_start                   3000
% 7.39/1.48  --inst_learning_factor                  2
% 7.39/1.48  --inst_start_prop_sim_after_learn       3
% 7.39/1.48  --inst_sel_renew                        solver
% 7.39/1.48  --inst_lit_activity_flag                true
% 7.39/1.48  --inst_restr_to_given                   false
% 7.39/1.48  --inst_activity_threshold               500
% 7.39/1.48  --inst_out_proof                        true
% 7.39/1.48  
% 7.39/1.48  ------ Resolution Options
% 7.39/1.48  
% 7.39/1.48  --resolution_flag                       true
% 7.39/1.48  --res_lit_sel                           adaptive
% 7.39/1.48  --res_lit_sel_side                      none
% 7.39/1.48  --res_ordering                          kbo
% 7.39/1.48  --res_to_prop_solver                    active
% 7.39/1.48  --res_prop_simpl_new                    false
% 7.39/1.48  --res_prop_simpl_given                  true
% 7.39/1.48  --res_passive_queue_type                priority_queues
% 7.39/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.39/1.48  --res_passive_queues_freq               [15;5]
% 7.39/1.48  --res_forward_subs                      full
% 7.39/1.48  --res_backward_subs                     full
% 7.39/1.48  --res_forward_subs_resolution           true
% 7.39/1.48  --res_backward_subs_resolution          true
% 7.39/1.48  --res_orphan_elimination                true
% 7.39/1.48  --res_time_limit                        2.
% 7.39/1.48  --res_out_proof                         true
% 7.39/1.48  
% 7.39/1.48  ------ Superposition Options
% 7.39/1.48  
% 7.39/1.48  --superposition_flag                    true
% 7.39/1.48  --sup_passive_queue_type                priority_queues
% 7.39/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.39/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.39/1.48  --demod_completeness_check              fast
% 7.39/1.48  --demod_use_ground                      true
% 7.39/1.48  --sup_to_prop_solver                    passive
% 7.39/1.48  --sup_prop_simpl_new                    true
% 7.39/1.48  --sup_prop_simpl_given                  true
% 7.39/1.48  --sup_fun_splitting                     true
% 7.39/1.48  --sup_smt_interval                      50000
% 7.39/1.48  
% 7.39/1.48  ------ Superposition Simplification Setup
% 7.39/1.48  
% 7.39/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.39/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.39/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.39/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.39/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.39/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.39/1.48  --sup_immed_triv                        [TrivRules]
% 7.39/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.48  --sup_immed_bw_main                     []
% 7.39/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.39/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.39/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.48  --sup_input_bw                          []
% 7.39/1.48  
% 7.39/1.48  ------ Combination Options
% 7.39/1.48  
% 7.39/1.48  --comb_res_mult                         3
% 7.39/1.48  --comb_sup_mult                         2
% 7.39/1.48  --comb_inst_mult                        10
% 7.39/1.48  
% 7.39/1.48  ------ Debug Options
% 7.39/1.48  
% 7.39/1.48  --dbg_backtrace                         false
% 7.39/1.48  --dbg_dump_prop_clauses                 false
% 7.39/1.48  --dbg_dump_prop_clauses_file            -
% 7.39/1.48  --dbg_out_stat                          false
% 7.39/1.48  ------ Parsing...
% 7.39/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.48  ------ Proving...
% 7.39/1.48  ------ Problem Properties 
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  clauses                                 40
% 7.39/1.48  conjectures                             11
% 7.39/1.48  EPR                                     7
% 7.39/1.48  Horn                                    36
% 7.39/1.48  unary                                   17
% 7.39/1.48  binary                                  4
% 7.39/1.48  lits                                    137
% 7.39/1.48  lits eq                                 32
% 7.39/1.48  fd_pure                                 0
% 7.39/1.48  fd_pseudo                               0
% 7.39/1.48  fd_cond                                 4
% 7.39/1.48  fd_pseudo_cond                          0
% 7.39/1.48  AC symbols                              0
% 7.39/1.48  
% 7.39/1.48  ------ Schedule dynamic 5 is on 
% 7.39/1.48  
% 7.39/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  ------ 
% 7.39/1.48  Current options:
% 7.39/1.48  ------ 
% 7.39/1.48  
% 7.39/1.48  ------ Input Options
% 7.39/1.48  
% 7.39/1.48  --out_options                           all
% 7.39/1.48  --tptp_safe_out                         true
% 7.39/1.48  --problem_path                          ""
% 7.39/1.48  --include_path                          ""
% 7.39/1.48  --clausifier                            res/vclausify_rel
% 7.39/1.48  --clausifier_options                    ""
% 7.39/1.48  --stdin                                 false
% 7.39/1.48  --stats_out                             all
% 7.39/1.48  
% 7.39/1.48  ------ General Options
% 7.39/1.48  
% 7.39/1.48  --fof                                   false
% 7.39/1.48  --time_out_real                         305.
% 7.39/1.48  --time_out_virtual                      -1.
% 7.39/1.48  --symbol_type_check                     false
% 7.39/1.48  --clausify_out                          false
% 7.39/1.48  --sig_cnt_out                           false
% 7.39/1.48  --trig_cnt_out                          false
% 7.39/1.48  --trig_cnt_out_tolerance                1.
% 7.39/1.48  --trig_cnt_out_sk_spl                   false
% 7.39/1.48  --abstr_cl_out                          false
% 7.39/1.48  
% 7.39/1.48  ------ Global Options
% 7.39/1.48  
% 7.39/1.48  --schedule                              default
% 7.39/1.48  --add_important_lit                     false
% 7.39/1.48  --prop_solver_per_cl                    1000
% 7.39/1.48  --min_unsat_core                        false
% 7.39/1.48  --soft_assumptions                      false
% 7.39/1.48  --soft_lemma_size                       3
% 7.39/1.48  --prop_impl_unit_size                   0
% 7.39/1.48  --prop_impl_unit                        []
% 7.39/1.48  --share_sel_clauses                     true
% 7.39/1.48  --reset_solvers                         false
% 7.39/1.48  --bc_imp_inh                            [conj_cone]
% 7.39/1.48  --conj_cone_tolerance                   3.
% 7.39/1.48  --extra_neg_conj                        none
% 7.39/1.48  --large_theory_mode                     true
% 7.39/1.48  --prolific_symb_bound                   200
% 7.39/1.48  --lt_threshold                          2000
% 7.39/1.48  --clause_weak_htbl                      true
% 7.39/1.48  --gc_record_bc_elim                     false
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing Options
% 7.39/1.48  
% 7.39/1.48  --preprocessing_flag                    true
% 7.39/1.48  --time_out_prep_mult                    0.1
% 7.39/1.48  --splitting_mode                        input
% 7.39/1.48  --splitting_grd                         true
% 7.39/1.48  --splitting_cvd                         false
% 7.39/1.48  --splitting_cvd_svl                     false
% 7.39/1.48  --splitting_nvd                         32
% 7.39/1.48  --sub_typing                            true
% 7.39/1.48  --prep_gs_sim                           true
% 7.39/1.48  --prep_unflatten                        true
% 7.39/1.48  --prep_res_sim                          true
% 7.39/1.48  --prep_upred                            true
% 7.39/1.48  --prep_sem_filter                       exhaustive
% 7.39/1.48  --prep_sem_filter_out                   false
% 7.39/1.48  --pred_elim                             true
% 7.39/1.48  --res_sim_input                         true
% 7.39/1.48  --eq_ax_congr_red                       true
% 7.39/1.48  --pure_diseq_elim                       true
% 7.39/1.48  --brand_transform                       false
% 7.39/1.48  --non_eq_to_eq                          false
% 7.39/1.48  --prep_def_merge                        true
% 7.39/1.48  --prep_def_merge_prop_impl              false
% 7.39/1.48  --prep_def_merge_mbd                    true
% 7.39/1.48  --prep_def_merge_tr_red                 false
% 7.39/1.48  --prep_def_merge_tr_cl                  false
% 7.39/1.48  --smt_preprocessing                     true
% 7.39/1.48  --smt_ac_axioms                         fast
% 7.39/1.48  --preprocessed_out                      false
% 7.39/1.48  --preprocessed_stats                    false
% 7.39/1.48  
% 7.39/1.48  ------ Abstraction refinement Options
% 7.39/1.48  
% 7.39/1.48  --abstr_ref                             []
% 7.39/1.48  --abstr_ref_prep                        false
% 7.39/1.48  --abstr_ref_until_sat                   false
% 7.39/1.48  --abstr_ref_sig_restrict                funpre
% 7.39/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.39/1.48  --abstr_ref_under                       []
% 7.39/1.48  
% 7.39/1.48  ------ SAT Options
% 7.39/1.48  
% 7.39/1.48  --sat_mode                              false
% 7.39/1.48  --sat_fm_restart_options                ""
% 7.39/1.48  --sat_gr_def                            false
% 7.39/1.48  --sat_epr_types                         true
% 7.39/1.48  --sat_non_cyclic_types                  false
% 7.39/1.48  --sat_finite_models                     false
% 7.39/1.48  --sat_fm_lemmas                         false
% 7.39/1.48  --sat_fm_prep                           false
% 7.39/1.48  --sat_fm_uc_incr                        true
% 7.39/1.48  --sat_out_model                         small
% 7.39/1.48  --sat_out_clauses                       false
% 7.39/1.48  
% 7.39/1.48  ------ QBF Options
% 7.39/1.48  
% 7.39/1.48  --qbf_mode                              false
% 7.39/1.48  --qbf_elim_univ                         false
% 7.39/1.48  --qbf_dom_inst                          none
% 7.39/1.48  --qbf_dom_pre_inst                      false
% 7.39/1.48  --qbf_sk_in                             false
% 7.39/1.48  --qbf_pred_elim                         true
% 7.39/1.48  --qbf_split                             512
% 7.39/1.48  
% 7.39/1.48  ------ BMC1 Options
% 7.39/1.48  
% 7.39/1.48  --bmc1_incremental                      false
% 7.39/1.48  --bmc1_axioms                           reachable_all
% 7.39/1.48  --bmc1_min_bound                        0
% 7.39/1.48  --bmc1_max_bound                        -1
% 7.39/1.48  --bmc1_max_bound_default                -1
% 7.39/1.48  --bmc1_symbol_reachability              true
% 7.39/1.48  --bmc1_property_lemmas                  false
% 7.39/1.48  --bmc1_k_induction                      false
% 7.39/1.48  --bmc1_non_equiv_states                 false
% 7.39/1.48  --bmc1_deadlock                         false
% 7.39/1.48  --bmc1_ucm                              false
% 7.39/1.48  --bmc1_add_unsat_core                   none
% 7.39/1.48  --bmc1_unsat_core_children              false
% 7.39/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.39/1.48  --bmc1_out_stat                         full
% 7.39/1.48  --bmc1_ground_init                      false
% 7.39/1.48  --bmc1_pre_inst_next_state              false
% 7.39/1.48  --bmc1_pre_inst_state                   false
% 7.39/1.48  --bmc1_pre_inst_reach_state             false
% 7.39/1.48  --bmc1_out_unsat_core                   false
% 7.39/1.48  --bmc1_aig_witness_out                  false
% 7.39/1.48  --bmc1_verbose                          false
% 7.39/1.48  --bmc1_dump_clauses_tptp                false
% 7.39/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.39/1.48  --bmc1_dump_file                        -
% 7.39/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.39/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.39/1.48  --bmc1_ucm_extend_mode                  1
% 7.39/1.48  --bmc1_ucm_init_mode                    2
% 7.39/1.48  --bmc1_ucm_cone_mode                    none
% 7.39/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.39/1.48  --bmc1_ucm_relax_model                  4
% 7.39/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.39/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.39/1.48  --bmc1_ucm_layered_model                none
% 7.39/1.48  --bmc1_ucm_max_lemma_size               10
% 7.39/1.48  
% 7.39/1.48  ------ AIG Options
% 7.39/1.48  
% 7.39/1.48  --aig_mode                              false
% 7.39/1.48  
% 7.39/1.48  ------ Instantiation Options
% 7.39/1.48  
% 7.39/1.48  --instantiation_flag                    true
% 7.39/1.48  --inst_sos_flag                         true
% 7.39/1.48  --inst_sos_phase                        true
% 7.39/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.39/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.39/1.48  --inst_lit_sel_side                     none
% 7.39/1.48  --inst_solver_per_active                1400
% 7.39/1.48  --inst_solver_calls_frac                1.
% 7.39/1.48  --inst_passive_queue_type               priority_queues
% 7.39/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.39/1.48  --inst_passive_queues_freq              [25;2]
% 7.39/1.48  --inst_dismatching                      true
% 7.39/1.48  --inst_eager_unprocessed_to_passive     true
% 7.39/1.48  --inst_prop_sim_given                   true
% 7.39/1.48  --inst_prop_sim_new                     false
% 7.39/1.48  --inst_subs_new                         false
% 7.39/1.48  --inst_eq_res_simp                      false
% 7.39/1.48  --inst_subs_given                       false
% 7.39/1.48  --inst_orphan_elimination               true
% 7.39/1.48  --inst_learning_loop_flag               true
% 7.39/1.48  --inst_learning_start                   3000
% 7.39/1.48  --inst_learning_factor                  2
% 7.39/1.48  --inst_start_prop_sim_after_learn       3
% 7.39/1.48  --inst_sel_renew                        solver
% 7.39/1.48  --inst_lit_activity_flag                true
% 7.39/1.48  --inst_restr_to_given                   false
% 7.39/1.48  --inst_activity_threshold               500
% 7.39/1.48  --inst_out_proof                        true
% 7.39/1.48  
% 7.39/1.48  ------ Resolution Options
% 7.39/1.48  
% 7.39/1.48  --resolution_flag                       false
% 7.39/1.48  --res_lit_sel                           adaptive
% 7.39/1.48  --res_lit_sel_side                      none
% 7.39/1.48  --res_ordering                          kbo
% 7.39/1.48  --res_to_prop_solver                    active
% 7.39/1.48  --res_prop_simpl_new                    false
% 7.39/1.48  --res_prop_simpl_given                  true
% 7.39/1.48  --res_passive_queue_type                priority_queues
% 7.39/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.39/1.48  --res_passive_queues_freq               [15;5]
% 7.39/1.48  --res_forward_subs                      full
% 7.39/1.48  --res_backward_subs                     full
% 7.39/1.48  --res_forward_subs_resolution           true
% 7.39/1.48  --res_backward_subs_resolution          true
% 7.39/1.48  --res_orphan_elimination                true
% 7.39/1.48  --res_time_limit                        2.
% 7.39/1.48  --res_out_proof                         true
% 7.39/1.48  
% 7.39/1.48  ------ Superposition Options
% 7.39/1.48  
% 7.39/1.48  --superposition_flag                    true
% 7.39/1.48  --sup_passive_queue_type                priority_queues
% 7.39/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.39/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.39/1.48  --demod_completeness_check              fast
% 7.39/1.48  --demod_use_ground                      true
% 7.39/1.48  --sup_to_prop_solver                    passive
% 7.39/1.48  --sup_prop_simpl_new                    true
% 7.39/1.48  --sup_prop_simpl_given                  true
% 7.39/1.48  --sup_fun_splitting                     true
% 7.39/1.48  --sup_smt_interval                      50000
% 7.39/1.48  
% 7.39/1.48  ------ Superposition Simplification Setup
% 7.39/1.48  
% 7.39/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.39/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.39/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.39/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.39/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.39/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.39/1.48  --sup_immed_triv                        [TrivRules]
% 7.39/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.48  --sup_immed_bw_main                     []
% 7.39/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.39/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.39/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.48  --sup_input_bw                          []
% 7.39/1.48  
% 7.39/1.48  ------ Combination Options
% 7.39/1.48  
% 7.39/1.48  --comb_res_mult                         3
% 7.39/1.48  --comb_sup_mult                         2
% 7.39/1.48  --comb_inst_mult                        10
% 7.39/1.48  
% 7.39/1.48  ------ Debug Options
% 7.39/1.48  
% 7.39/1.48  --dbg_backtrace                         false
% 7.39/1.48  --dbg_dump_prop_clauses                 false
% 7.39/1.48  --dbg_dump_prop_clauses_file            -
% 7.39/1.48  --dbg_out_stat                          false
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  ------ Proving...
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  % SZS status Theorem for theBenchmark.p
% 7.39/1.48  
% 7.39/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.39/1.48  
% 7.39/1.48  fof(f2,axiom,(
% 7.39/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f52,plain,(
% 7.39/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f2])).
% 7.39/1.48  
% 7.39/1.48  fof(f20,conjecture,(
% 7.39/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f21,negated_conjecture,(
% 7.39/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.39/1.48    inference(negated_conjecture,[],[f20])).
% 7.39/1.48  
% 7.39/1.48  fof(f45,plain,(
% 7.39/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.39/1.48    inference(ennf_transformation,[],[f21])).
% 7.39/1.48  
% 7.39/1.48  fof(f46,plain,(
% 7.39/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.39/1.48    inference(flattening,[],[f45])).
% 7.39/1.48  
% 7.39/1.48  fof(f49,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.39/1.48    introduced(choice_axiom,[])).
% 7.39/1.48  
% 7.39/1.48  fof(f48,plain,(
% 7.39/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.39/1.48    introduced(choice_axiom,[])).
% 7.39/1.48  
% 7.39/1.48  fof(f50,plain,(
% 7.39/1.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.39/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f49,f48])).
% 7.39/1.48  
% 7.39/1.48  fof(f86,plain,(
% 7.39/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f1,axiom,(
% 7.39/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f22,plain,(
% 7.39/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.39/1.48    inference(ennf_transformation,[],[f1])).
% 7.39/1.48  
% 7.39/1.48  fof(f51,plain,(
% 7.39/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f22])).
% 7.39/1.48  
% 7.39/1.48  fof(f83,plain,(
% 7.39/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f81,plain,(
% 7.39/1.48    v1_funct_1(sK2)),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f7,axiom,(
% 7.39/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f26,plain,(
% 7.39/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.39/1.48    inference(ennf_transformation,[],[f7])).
% 7.39/1.48  
% 7.39/1.48  fof(f27,plain,(
% 7.39/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.39/1.48    inference(flattening,[],[f26])).
% 7.39/1.48  
% 7.39/1.48  fof(f58,plain,(
% 7.39/1.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f27])).
% 7.39/1.48  
% 7.39/1.48  fof(f3,axiom,(
% 7.39/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f23,plain,(
% 7.39/1.48    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.39/1.48    inference(ennf_transformation,[],[f3])).
% 7.39/1.48  
% 7.39/1.48  fof(f53,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f23])).
% 7.39/1.48  
% 7.39/1.48  fof(f87,plain,(
% 7.39/1.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f19,axiom,(
% 7.39/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f43,plain,(
% 7.39/1.48    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.39/1.48    inference(ennf_transformation,[],[f19])).
% 7.39/1.48  
% 7.39/1.48  fof(f44,plain,(
% 7.39/1.48    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.39/1.48    inference(flattening,[],[f43])).
% 7.39/1.48  
% 7.39/1.48  fof(f80,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f44])).
% 7.39/1.48  
% 7.39/1.48  fof(f82,plain,(
% 7.39/1.48    v1_funct_2(sK2,sK0,sK1)),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f89,plain,(
% 7.39/1.48    v2_funct_1(sK2)),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f91,plain,(
% 7.39/1.48    k1_xboole_0 != sK1),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f15,axiom,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f37,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.39/1.48    inference(ennf_transformation,[],[f15])).
% 7.39/1.48  
% 7.39/1.48  fof(f38,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.39/1.48    inference(flattening,[],[f37])).
% 7.39/1.48  
% 7.39/1.48  fof(f72,plain,(
% 7.39/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f38])).
% 7.39/1.48  
% 7.39/1.48  fof(f84,plain,(
% 7.39/1.48    v1_funct_1(sK3)),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f12,axiom,(
% 7.39/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f33,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.39/1.48    inference(ennf_transformation,[],[f12])).
% 7.39/1.48  
% 7.39/1.48  fof(f34,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.39/1.48    inference(flattening,[],[f33])).
% 7.39/1.48  
% 7.39/1.48  fof(f47,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.39/1.48    inference(nnf_transformation,[],[f34])).
% 7.39/1.48  
% 7.39/1.48  fof(f67,plain,(
% 7.39/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f47])).
% 7.39/1.48  
% 7.39/1.48  fof(f88,plain,(
% 7.39/1.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f13,axiom,(
% 7.39/1.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f69,plain,(
% 7.39/1.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f13])).
% 7.39/1.48  
% 7.39/1.48  fof(f16,axiom,(
% 7.39/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f73,plain,(
% 7.39/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f16])).
% 7.39/1.48  
% 7.39/1.48  fof(f99,plain,(
% 7.39/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.39/1.48    inference(definition_unfolding,[],[f69,f73])).
% 7.39/1.48  
% 7.39/1.48  fof(f14,axiom,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f35,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.39/1.48    inference(ennf_transformation,[],[f14])).
% 7.39/1.48  
% 7.39/1.48  fof(f36,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.39/1.48    inference(flattening,[],[f35])).
% 7.39/1.48  
% 7.39/1.48  fof(f71,plain,(
% 7.39/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f36])).
% 7.39/1.48  
% 7.39/1.48  fof(f18,axiom,(
% 7.39/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f41,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.39/1.48    inference(ennf_transformation,[],[f18])).
% 7.39/1.48  
% 7.39/1.48  fof(f42,plain,(
% 7.39/1.48    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.39/1.48    inference(flattening,[],[f41])).
% 7.39/1.48  
% 7.39/1.48  fof(f77,plain,(
% 7.39/1.48    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f42])).
% 7.39/1.48  
% 7.39/1.48  fof(f85,plain,(
% 7.39/1.48    v1_funct_2(sK3,sK1,sK0)),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f90,plain,(
% 7.39/1.48    k1_xboole_0 != sK0),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f8,axiom,(
% 7.39/1.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f61,plain,(
% 7.39/1.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f8])).
% 7.39/1.48  
% 7.39/1.48  fof(f97,plain,(
% 7.39/1.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.39/1.48    inference(definition_unfolding,[],[f61,f73])).
% 7.39/1.48  
% 7.39/1.48  fof(f10,axiom,(
% 7.39/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f30,plain,(
% 7.39/1.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.39/1.48    inference(ennf_transformation,[],[f10])).
% 7.39/1.48  
% 7.39/1.48  fof(f31,plain,(
% 7.39/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.39/1.48    inference(flattening,[],[f30])).
% 7.39/1.48  
% 7.39/1.48  fof(f64,plain,(
% 7.39/1.48    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f31])).
% 7.39/1.48  
% 7.39/1.48  fof(f17,axiom,(
% 7.39/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f39,plain,(
% 7.39/1.48    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.39/1.48    inference(ennf_transformation,[],[f17])).
% 7.39/1.48  
% 7.39/1.48  fof(f40,plain,(
% 7.39/1.48    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.39/1.48    inference(flattening,[],[f39])).
% 7.39/1.48  
% 7.39/1.48  fof(f74,plain,(
% 7.39/1.48    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f40])).
% 7.39/1.48  
% 7.39/1.48  fof(f79,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f44])).
% 7.39/1.48  
% 7.39/1.48  fof(f4,axiom,(
% 7.39/1.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f54,plain,(
% 7.39/1.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.39/1.48    inference(cnf_transformation,[],[f4])).
% 7.39/1.48  
% 7.39/1.48  fof(f94,plain,(
% 7.39/1.48    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.39/1.48    inference(definition_unfolding,[],[f54,f73])).
% 7.39/1.48  
% 7.39/1.48  fof(f5,axiom,(
% 7.39/1.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f24,plain,(
% 7.39/1.48    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.39/1.48    inference(ennf_transformation,[],[f5])).
% 7.39/1.48  
% 7.39/1.48  fof(f56,plain,(
% 7.39/1.48    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f24])).
% 7.39/1.48  
% 7.39/1.48  fof(f95,plain,(
% 7.39/1.48    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f56,f73])).
% 7.39/1.48  
% 7.39/1.48  fof(f6,axiom,(
% 7.39/1.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f25,plain,(
% 7.39/1.48    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.39/1.48    inference(ennf_transformation,[],[f6])).
% 7.39/1.48  
% 7.39/1.48  fof(f57,plain,(
% 7.39/1.48    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f25])).
% 7.39/1.48  
% 7.39/1.48  fof(f96,plain,(
% 7.39/1.48    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f57,f73])).
% 7.39/1.48  
% 7.39/1.48  fof(f9,axiom,(
% 7.39/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f28,plain,(
% 7.39/1.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.39/1.48    inference(ennf_transformation,[],[f9])).
% 7.39/1.48  
% 7.39/1.48  fof(f29,plain,(
% 7.39/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.39/1.48    inference(flattening,[],[f28])).
% 7.39/1.48  
% 7.39/1.48  fof(f63,plain,(
% 7.39/1.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f29])).
% 7.39/1.48  
% 7.39/1.48  fof(f92,plain,(
% 7.39/1.48    k2_funct_1(sK2) != sK3),
% 7.39/1.48    inference(cnf_transformation,[],[f50])).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1,plain,
% 7.39/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1310,plain,
% 7.39/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_35,negated_conjecture,
% 7.39/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.39/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1286,plain,
% 7.39/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_0,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.39/1.48      | ~ v1_relat_1(X1)
% 7.39/1.48      | v1_relat_1(X0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1311,plain,
% 7.39/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.39/1.48      | v1_relat_1(X1) != iProver_top
% 7.39/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2945,plain,
% 7.39/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.39/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1286,c_1311]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3057,plain,
% 7.39/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1310,c_2945]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_38,negated_conjecture,
% 7.39/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.39/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1283,plain,
% 7.39/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2946,plain,
% 7.39/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.39/1.48      | v1_relat_1(sK2) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1283,c_1311]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3060,plain,
% 7.39/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1310,c_2946]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_40,negated_conjecture,
% 7.39/1.48      ( v1_funct_1(sK2) ),
% 7.39/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1281,plain,
% 7.39/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_8,plain,
% 7.39/1.48      ( ~ v1_funct_1(X0)
% 7.39/1.48      | ~ v1_relat_1(X0)
% 7.39/1.48      | v1_relat_1(k2_funct_1(X0)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1305,plain,
% 7.39/1.48      ( v1_funct_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2,plain,
% 7.39/1.48      ( ~ v1_relat_1(X0)
% 7.39/1.48      | ~ v1_relat_1(X1)
% 7.39/1.48      | ~ v1_relat_1(X2)
% 7.39/1.48      | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1309,plain,
% 7.39/1.48      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.39/1.48      | v1_relat_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X2) != iProver_top
% 7.39/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4020,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.39/1.48      | v1_funct_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X1) != iProver_top
% 7.39/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1305,c_1309]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_9704,plain,
% 7.39/1.48      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.39/1.48      | v1_relat_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X1) != iProver_top
% 7.39/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1281,c_4020]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_9864,plain,
% 7.39/1.48      ( v1_relat_1(X1) != iProver_top
% 7.39/1.48      | v1_relat_1(X0) != iProver_top
% 7.39/1.48      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_9704,c_3060]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_9865,plain,
% 7.39/1.48      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.39/1.48      | v1_relat_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.39/1.48      inference(renaming,[status(thm)],[c_9864]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_9874,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.39/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_3060,c_9865]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_34,negated_conjecture,
% 7.39/1.48      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.39/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_27,plain,
% 7.39/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.39/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.39/1.48      | ~ v2_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | k2_relset_1(X1,X2,X0) != X2
% 7.39/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.39/1.48      | k1_xboole_0 = X2 ),
% 7.39/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1289,plain,
% 7.39/1.48      ( k2_relset_1(X0,X1,X2) != X1
% 7.39/1.48      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.39/1.48      | k1_xboole_0 = X1
% 7.39/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.39/1.48      | v2_funct_1(X2) != iProver_top
% 7.39/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3083,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.39/1.48      | sK1 = k1_xboole_0
% 7.39/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.39/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.39/1.48      | v2_funct_1(sK2) != iProver_top
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_34,c_1289]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_39,negated_conjecture,
% 7.39/1.48      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.39/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_32,negated_conjecture,
% 7.39/1.48      ( v2_funct_1(sK2) ),
% 7.39/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_30,negated_conjecture,
% 7.39/1.48      ( k1_xboole_0 != sK1 ),
% 7.39/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1357,plain,
% 7.39/1.48      ( ~ v1_funct_2(X0,X1,sK1)
% 7.39/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.39/1.48      | ~ v2_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | k2_relset_1(X1,sK1,X0) != sK1
% 7.39/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 7.39/1.48      | k1_xboole_0 = sK1 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1448,plain,
% 7.39/1.48      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.39/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.39/1.48      | ~ v2_funct_1(sK2)
% 7.39/1.48      | ~ v1_funct_1(sK2)
% 7.39/1.48      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.39/1.48      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.39/1.48      | k1_xboole_0 = sK1 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1357]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1650,plain,
% 7.39/1.48      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.39/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.39/1.48      | ~ v2_funct_1(sK2)
% 7.39/1.48      | ~ v1_funct_1(sK2)
% 7.39/1.48      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.39/1.48      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.39/1.48      | k1_xboole_0 = sK1 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1448]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3311,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_3083,c_40,c_39,c_38,c_34,c_32,c_30,c_1650]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_9878,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.39/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.39/1.48      inference(light_normalisation,[status(thm)],[c_9874,c_3311]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_9980,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_3057,c_9878]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_21,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.39/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X3)
% 7.39/1.48      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1294,plain,
% 7.39/1.48      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.39/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.39/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.39/1.48      | v1_funct_1(X5) != iProver_top
% 7.39/1.48      | v1_funct_1(X4) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4212,plain,
% 7.39/1.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.39/1.48      | v1_funct_1(X2) != iProver_top
% 7.39/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1286,c_1294]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_37,negated_conjecture,
% 7.39/1.48      ( v1_funct_1(sK3) ),
% 7.39/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_44,plain,
% 7.39/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4246,plain,
% 7.39/1.48      ( v1_funct_1(X2) != iProver_top
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.39/1.48      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_4212,c_44]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4247,plain,
% 7.39/1.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.39/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.39/1.48      inference(renaming,[status(thm)],[c_4246]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4254,plain,
% 7.39/1.48      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1283,c_4247]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_17,plain,
% 7.39/1.48      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.39/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.39/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.39/1.48      | X3 = X2 ),
% 7.39/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_33,negated_conjecture,
% 7.39/1.48      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_430,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.39/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.39/1.48      | X3 = X0
% 7.39/1.48      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.39/1.48      | k6_partfun1(sK0) != X3
% 7.39/1.48      | sK0 != X2
% 7.39/1.48      | sK0 != X1 ),
% 7.39/1.48      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_431,plain,
% 7.39/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.39/1.48      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.39/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.39/1.48      inference(unflattening,[status(thm)],[c_430]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_18,plain,
% 7.39/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.39/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_439,plain,
% 7.39/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.39/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.39/1.48      inference(forward_subsumption_resolution,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_431,c_18]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1279,plain,
% 7.39/1.48      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.39/1.48      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_19,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.39/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.39/1.48      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X3) ),
% 7.39/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1397,plain,
% 7.39/1.48      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.39/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.39/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.39/1.48      | ~ v1_funct_1(sK3)
% 7.39/1.48      | ~ v1_funct_1(sK2) ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2114,plain,
% 7.39/1.48      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_1279,c_40,c_38,c_37,c_35,c_439,c_1397]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4255,plain,
% 7.39/1.48      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.39/1.48      inference(light_normalisation,[status(thm)],[c_4254,c_2114]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_41,plain,
% 7.39/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4414,plain,
% 7.39/1.48      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_4255,c_41]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_24,plain,
% 7.39/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.39/1.48      | ~ v1_funct_2(X3,X2,X4)
% 7.39/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.39/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.39/1.48      | v2_funct_1(X3)
% 7.39/1.48      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 7.39/1.48      | ~ v1_funct_1(X3)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | k2_relset_1(X1,X2,X0) != X2
% 7.39/1.48      | k1_xboole_0 = X4 ),
% 7.39/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1292,plain,
% 7.39/1.48      ( k2_relset_1(X0,X1,X2) != X1
% 7.39/1.48      | k1_xboole_0 = X3
% 7.39/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.39/1.48      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.39/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.39/1.48      | v2_funct_1(X4) = iProver_top
% 7.39/1.48      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.39/1.48      | v1_funct_1(X2) != iProver_top
% 7.39/1.48      | v1_funct_1(X4) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4754,plain,
% 7.39/1.48      ( k1_xboole_0 = X0
% 7.39/1.48      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.39/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.39/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.39/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.39/1.48      | v2_funct_1(X1) = iProver_top
% 7.39/1.48      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.39/1.48      | v1_funct_1(X1) != iProver_top
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_34,c_1292]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_42,plain,
% 7.39/1.48      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_43,plain,
% 7.39/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4761,plain,
% 7.39/1.48      ( v1_funct_1(X1) != iProver_top
% 7.39/1.48      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.39/1.48      | v2_funct_1(X1) = iProver_top
% 7.39/1.48      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.39/1.48      | k1_xboole_0 = X0
% 7.39/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_4754,c_41,c_42,c_43]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4762,plain,
% 7.39/1.48      ( k1_xboole_0 = X0
% 7.39/1.48      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.39/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.39/1.48      | v2_funct_1(X1) = iProver_top
% 7.39/1.48      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.39/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.39/1.48      inference(renaming,[status(thm)],[c_4761]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4765,plain,
% 7.39/1.48      ( sK0 = k1_xboole_0
% 7.39/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.39/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.39/1.48      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.39/1.48      | v2_funct_1(sK3) = iProver_top
% 7.39/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_2114,c_4762]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_36,negated_conjecture,
% 7.39/1.48      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_45,plain,
% 7.39/1.48      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_46,plain,
% 7.39/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_31,negated_conjecture,
% 7.39/1.48      ( k1_xboole_0 != sK0 ),
% 7.39/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_727,plain,( X0 = X0 ),theory(equality) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_758,plain,
% 7.39/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_727]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_728,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1395,plain,
% 7.39/1.48      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_728]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1396,plain,
% 7.39/1.48      ( sK0 != k1_xboole_0
% 7.39/1.48      | k1_xboole_0 = sK0
% 7.39/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1395]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_9,plain,
% 7.39/1.48      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2964,plain,
% 7.39/1.48      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2965,plain,
% 7.39/1.48      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_2964]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4786,plain,
% 7.39/1.48      ( v2_funct_1(sK3) = iProver_top ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_4765,c_44,c_45,c_46,c_31,c_758,c_1396,c_2965]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_14,plain,
% 7.39/1.48      ( ~ v2_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | ~ v1_relat_1(X0)
% 7.39/1.48      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1299,plain,
% 7.39/1.48      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 7.39/1.48      | v2_funct_1(X0) != iProver_top
% 7.39/1.48      | v1_funct_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4791,plain,
% 7.39/1.48      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 7.39/1.48      | v1_funct_1(sK3) != iProver_top
% 7.39/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_4786,c_1299]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_22,plain,
% 7.39/1.48      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.39/1.48      | ~ v1_funct_2(X2,X0,X1)
% 7.39/1.48      | ~ v1_funct_2(X3,X1,X0)
% 7.39/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.39/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.39/1.48      | ~ v1_funct_1(X2)
% 7.39/1.48      | ~ v1_funct_1(X3)
% 7.39/1.48      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.39/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_443,plain,
% 7.39/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.39/1.48      | ~ v1_funct_2(X3,X2,X1)
% 7.39/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.39/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.39/1.48      | ~ v1_funct_1(X3)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.39/1.48      | k2_relset_1(X2,X1,X3) = X1
% 7.39/1.48      | k6_partfun1(X1) != k6_partfun1(sK0)
% 7.39/1.48      | sK0 != X1 ),
% 7.39/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_444,plain,
% 7.39/1.48      ( ~ v1_funct_2(X0,X1,sK0)
% 7.39/1.48      | ~ v1_funct_2(X2,sK0,X1)
% 7.39/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.39/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.39/1.48      | ~ v1_funct_1(X2)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.39/1.48      | k2_relset_1(X1,sK0,X0) = sK0
% 7.39/1.48      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.39/1.48      inference(unflattening,[status(thm)],[c_443]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_532,plain,
% 7.39/1.48      ( ~ v1_funct_2(X0,X1,sK0)
% 7.39/1.48      | ~ v1_funct_2(X2,sK0,X1)
% 7.39/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.39/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X2)
% 7.39/1.48      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.39/1.48      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.39/1.48      inference(equality_resolution_simp,[status(thm)],[c_444]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1278,plain,
% 7.39/1.48      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.39/1.48      | k2_relset_1(X0,sK0,X2) = sK0
% 7.39/1.48      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.39/1.48      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.39/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.39/1.48      | v1_funct_1(X2) != iProver_top
% 7.39/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1796,plain,
% 7.39/1.48      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.39/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.39/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.39/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.39/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.39/1.48      | v1_funct_1(sK3) != iProver_top
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.39/1.48      inference(equality_resolution,[status(thm)],[c_1278]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2121,plain,
% 7.39/1.48      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_1796,c_41,c_42,c_43,c_44,c_45,c_46]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_28,plain,
% 7.39/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.39/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.39/1.48      | ~ v2_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | k2_relset_1(X1,X2,X0) != X2
% 7.39/1.48      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.39/1.48      | k1_xboole_0 = X2 ),
% 7.39/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1288,plain,
% 7.39/1.48      ( k2_relset_1(X0,X1,X2) != X1
% 7.39/1.48      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.39/1.48      | k1_xboole_0 = X1
% 7.39/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.39/1.48      | v2_funct_1(X2) != iProver_top
% 7.39/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2969,plain,
% 7.39/1.48      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.39/1.48      | sK0 = k1_xboole_0
% 7.39/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.39/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.39/1.48      | v2_funct_1(sK3) != iProver_top
% 7.39/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_2121,c_1288]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3629,plain,
% 7.39/1.48      ( v2_funct_1(sK3) != iProver_top
% 7.39/1.48      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_2969,c_44,c_45,c_46,c_31,c_758,c_1396]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3630,plain,
% 7.39/1.48      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.39/1.48      | v2_funct_1(sK3) != iProver_top ),
% 7.39/1.48      inference(renaming,[status(thm)],[c_3629]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4795,plain,
% 7.39/1.48      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_4786,c_3630]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4797,plain,
% 7.39/1.48      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 7.39/1.48      | v1_funct_1(sK3) != iProver_top
% 7.39/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.39/1.48      inference(demodulation,[status(thm)],[c_4791,c_4795]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4,plain,
% 7.39/1.48      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.39/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4798,plain,
% 7.39/1.48      ( k1_relat_1(sK3) = sK1
% 7.39/1.48      | v1_funct_1(sK3) != iProver_top
% 7.39/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.39/1.48      inference(demodulation,[status(thm)],[c_4797,c_4]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_5000,plain,
% 7.39/1.48      ( k1_relat_1(sK3) = sK1 ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_4798,c_44,c_3057]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_5,plain,
% 7.39/1.48      ( ~ v1_relat_1(X0)
% 7.39/1.48      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.39/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1308,plain,
% 7.39/1.48      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.39/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3075,plain,
% 7.39/1.48      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_3057,c_1308]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_5003,plain,
% 7.39/1.48      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.39/1.48      inference(demodulation,[status(thm)],[c_5000,c_3075]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_6,plain,
% 7.39/1.48      ( ~ v1_relat_1(X0)
% 7.39/1.48      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.39/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1307,plain,
% 7.39/1.48      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.39/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2894,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 7.39/1.48      | v1_funct_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1305,c_1307]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4984,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 7.39/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1281,c_2894]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1287,plain,
% 7.39/1.48      ( v2_funct_1(sK2) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3106,plain,
% 7.39/1.48      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top
% 7.39/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1287,c_1299]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2968,plain,
% 7.39/1.48      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.39/1.48      | sK1 = k1_xboole_0
% 7.39/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.39/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.39/1.48      | v2_funct_1(sK2) != iProver_top
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_34,c_1288]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1358,plain,
% 7.39/1.48      ( ~ v1_funct_2(X0,X1,sK1)
% 7.39/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.39/1.48      | ~ v2_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | k2_relset_1(X1,sK1,X0) != sK1
% 7.39/1.48      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.39/1.48      | k1_xboole_0 = sK1 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_28]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1474,plain,
% 7.39/1.48      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.39/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.39/1.48      | ~ v2_funct_1(sK2)
% 7.39/1.48      | ~ v1_funct_1(sK2)
% 7.39/1.48      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.39/1.48      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 7.39/1.48      | k1_xboole_0 = sK1 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1358]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1663,plain,
% 7.39/1.48      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.39/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.39/1.48      | ~ v2_funct_1(sK2)
% 7.39/1.48      | ~ v1_funct_1(sK2)
% 7.39/1.48      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.39/1.48      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.39/1.48      | k1_xboole_0 = sK1 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1474]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3042,plain,
% 7.39/1.48      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_2968,c_40,c_39,c_38,c_34,c_32,c_30,c_1663]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3107,plain,
% 7.39/1.48      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top
% 7.39/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.39/1.48      inference(light_normalisation,[status(thm)],[c_3106,c_3042]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3108,plain,
% 7.39/1.48      ( k1_relat_1(sK2) = sK0
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top
% 7.39/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.39/1.48      inference(demodulation,[status(thm)],[c_3107,c_4]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3115,plain,
% 7.39/1.48      ( k1_relat_1(sK2) = sK0 ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_3108,c_41,c_3060]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_11,plain,
% 7.39/1.48      ( ~ v2_funct_1(X0)
% 7.39/1.48      | ~ v1_funct_1(X0)
% 7.39/1.48      | ~ v1_relat_1(X0)
% 7.39/1.48      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1302,plain,
% 7.39/1.48      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.39/1.48      | v2_funct_1(X0) != iProver_top
% 7.39/1.48      | v1_funct_1(X0) != iProver_top
% 7.39/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3021,plain,
% 7.39/1.48      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.39/1.48      | v1_funct_1(sK2) != iProver_top
% 7.39/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_1287,c_1302]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3072,plain,
% 7.39/1.48      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_3021,c_41,c_3060]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3117,plain,
% 7.39/1.48      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 7.39/1.48      inference(demodulation,[status(thm)],[c_3115,c_3072]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4987,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
% 7.39/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.39/1.48      inference(light_normalisation,[status(thm)],[c_4984,c_3117]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_5105,plain,
% 7.39/1.48      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.39/1.48      inference(global_propositional_subsumption,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_4987,c_3060]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_9987,plain,
% 7.39/1.48      ( k2_funct_1(sK2) = sK3 ),
% 7.39/1.48      inference(light_normalisation,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_9980,c_4414,c_5003,c_5105]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_29,negated_conjecture,
% 7.39/1.48      ( k2_funct_1(sK2) != sK3 ),
% 7.39/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(contradiction,plain,
% 7.39/1.48      ( $false ),
% 7.39/1.48      inference(minisat,[status(thm)],[c_9987,c_29]) ).
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.39/1.48  
% 7.39/1.48  ------                               Statistics
% 7.39/1.48  
% 7.39/1.48  ------ General
% 7.39/1.48  
% 7.39/1.48  abstr_ref_over_cycles:                  0
% 7.39/1.48  abstr_ref_under_cycles:                 0
% 7.39/1.48  gc_basic_clause_elim:                   0
% 7.39/1.48  forced_gc_time:                         0
% 7.39/1.48  parsing_time:                           0.014
% 7.39/1.48  unif_index_cands_time:                  0.
% 7.39/1.48  unif_index_add_time:                    0.
% 7.39/1.48  orderings_time:                         0.
% 7.39/1.48  out_proof_time:                         0.021
% 7.39/1.48  total_time:                             0.688
% 7.39/1.48  num_of_symbols:                         51
% 7.39/1.48  num_of_terms:                           17379
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing
% 7.39/1.48  
% 7.39/1.48  num_of_splits:                          0
% 7.39/1.48  num_of_split_atoms:                     0
% 7.39/1.48  num_of_reused_defs:                     0
% 7.39/1.48  num_eq_ax_congr_red:                    0
% 7.39/1.48  num_of_sem_filtered_clauses:            1
% 7.39/1.48  num_of_subtypes:                        0
% 7.39/1.48  monotx_restored_types:                  0
% 7.39/1.48  sat_num_of_epr_types:                   0
% 7.39/1.48  sat_num_of_non_cyclic_types:            0
% 7.39/1.48  sat_guarded_non_collapsed_types:        0
% 7.39/1.48  num_pure_diseq_elim:                    0
% 7.39/1.48  simp_replaced_by:                       0
% 7.39/1.48  res_preprocessed:                       194
% 7.39/1.48  prep_upred:                             0
% 7.39/1.48  prep_unflattend:                        12
% 7.39/1.48  smt_new_axioms:                         0
% 7.39/1.48  pred_elim_cands:                        5
% 7.39/1.48  pred_elim:                              1
% 7.39/1.48  pred_elim_cl:                           1
% 7.39/1.48  pred_elim_cycles:                       3
% 7.39/1.48  merged_defs:                            0
% 7.39/1.48  merged_defs_ncl:                        0
% 7.39/1.48  bin_hyper_res:                          0
% 7.39/1.48  prep_cycles:                            4
% 7.39/1.48  pred_elim_time:                         0.005
% 7.39/1.48  splitting_time:                         0.
% 7.39/1.48  sem_filter_time:                        0.
% 7.39/1.48  monotx_time:                            0.
% 7.39/1.48  subtype_inf_time:                       0.
% 7.39/1.48  
% 7.39/1.48  ------ Problem properties
% 7.39/1.48  
% 7.39/1.48  clauses:                                40
% 7.39/1.48  conjectures:                            11
% 7.39/1.48  epr:                                    7
% 7.39/1.48  horn:                                   36
% 7.39/1.48  ground:                                 12
% 7.39/1.48  unary:                                  17
% 7.39/1.48  binary:                                 4
% 7.39/1.48  lits:                                   137
% 7.39/1.48  lits_eq:                                32
% 7.39/1.48  fd_pure:                                0
% 7.39/1.48  fd_pseudo:                              0
% 7.39/1.48  fd_cond:                                4
% 7.39/1.48  fd_pseudo_cond:                         0
% 7.39/1.48  ac_symbols:                             0
% 7.39/1.48  
% 7.39/1.48  ------ Propositional Solver
% 7.39/1.48  
% 7.39/1.48  prop_solver_calls:                      31
% 7.39/1.48  prop_fast_solver_calls:                 1827
% 7.39/1.48  smt_solver_calls:                       0
% 7.39/1.48  smt_fast_solver_calls:                  0
% 7.39/1.48  prop_num_of_clauses:                    5323
% 7.39/1.48  prop_preprocess_simplified:             12842
% 7.39/1.48  prop_fo_subsumed:                       99
% 7.39/1.48  prop_solver_time:                       0.
% 7.39/1.48  smt_solver_time:                        0.
% 7.39/1.48  smt_fast_solver_time:                   0.
% 7.39/1.48  prop_fast_solver_time:                  0.
% 7.39/1.48  prop_unsat_core_time:                   0.001
% 7.39/1.48  
% 7.39/1.48  ------ QBF
% 7.39/1.48  
% 7.39/1.48  qbf_q_res:                              0
% 7.39/1.48  qbf_num_tautologies:                    0
% 7.39/1.48  qbf_prep_cycles:                        0
% 7.39/1.48  
% 7.39/1.48  ------ BMC1
% 7.39/1.48  
% 7.39/1.48  bmc1_current_bound:                     -1
% 7.39/1.48  bmc1_last_solved_bound:                 -1
% 7.39/1.48  bmc1_unsat_core_size:                   -1
% 7.39/1.48  bmc1_unsat_core_parents_size:           -1
% 7.39/1.48  bmc1_merge_next_fun:                    0
% 7.39/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.39/1.48  
% 7.39/1.48  ------ Instantiation
% 7.39/1.48  
% 7.39/1.48  inst_num_of_clauses:                    1313
% 7.39/1.48  inst_num_in_passive:                    465
% 7.39/1.48  inst_num_in_active:                     692
% 7.39/1.48  inst_num_in_unprocessed:                156
% 7.39/1.48  inst_num_of_loops:                      860
% 7.39/1.48  inst_num_of_learning_restarts:          0
% 7.39/1.48  inst_num_moves_active_passive:          165
% 7.39/1.48  inst_lit_activity:                      0
% 7.39/1.48  inst_lit_activity_moves:                1
% 7.39/1.48  inst_num_tautologies:                   0
% 7.39/1.48  inst_num_prop_implied:                  0
% 7.39/1.48  inst_num_existing_simplified:           0
% 7.39/1.48  inst_num_eq_res_simplified:             0
% 7.39/1.48  inst_num_child_elim:                    0
% 7.39/1.48  inst_num_of_dismatching_blockings:      203
% 7.39/1.48  inst_num_of_non_proper_insts:           1144
% 7.39/1.48  inst_num_of_duplicates:                 0
% 7.39/1.48  inst_inst_num_from_inst_to_res:         0
% 7.39/1.48  inst_dismatching_checking_time:         0.
% 7.39/1.48  
% 7.39/1.48  ------ Resolution
% 7.39/1.48  
% 7.39/1.48  res_num_of_clauses:                     0
% 7.39/1.48  res_num_in_passive:                     0
% 7.39/1.48  res_num_in_active:                      0
% 7.39/1.48  res_num_of_loops:                       198
% 7.39/1.48  res_forward_subset_subsumed:            78
% 7.39/1.48  res_backward_subset_subsumed:           0
% 7.39/1.48  res_forward_subsumed:                   0
% 7.39/1.48  res_backward_subsumed:                  0
% 7.39/1.48  res_forward_subsumption_resolution:     2
% 7.39/1.48  res_backward_subsumption_resolution:    0
% 7.39/1.48  res_clause_to_clause_subsumption:       588
% 7.39/1.48  res_orphan_elimination:                 0
% 7.39/1.48  res_tautology_del:                      21
% 7.39/1.48  res_num_eq_res_simplified:              1
% 7.39/1.48  res_num_sel_changes:                    0
% 7.39/1.48  res_moves_from_active_to_pass:          0
% 7.39/1.48  
% 7.39/1.48  ------ Superposition
% 7.39/1.48  
% 7.39/1.48  sup_time_total:                         0.
% 7.39/1.48  sup_time_generating:                    0.
% 7.39/1.48  sup_time_sim_full:                      0.
% 7.39/1.48  sup_time_sim_immed:                     0.
% 7.39/1.48  
% 7.39/1.48  sup_num_of_clauses:                     304
% 7.39/1.48  sup_num_in_active:                      151
% 7.39/1.48  sup_num_in_passive:                     153
% 7.39/1.48  sup_num_of_loops:                       170
% 7.39/1.48  sup_fw_superposition:                   209
% 7.39/1.48  sup_bw_superposition:                   102
% 7.39/1.48  sup_immediate_simplified:               71
% 7.39/1.48  sup_given_eliminated:                   1
% 7.39/1.48  comparisons_done:                       0
% 7.39/1.48  comparisons_avoided:                    4
% 7.39/1.48  
% 7.39/1.48  ------ Simplifications
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  sim_fw_subset_subsumed:                 7
% 7.39/1.48  sim_bw_subset_subsumed:                 12
% 7.39/1.48  sim_fw_subsumed:                        5
% 7.39/1.48  sim_bw_subsumed:                        2
% 7.39/1.48  sim_fw_subsumption_res:                 0
% 7.39/1.48  sim_bw_subsumption_res:                 0
% 7.39/1.48  sim_tautology_del:                      2
% 7.39/1.48  sim_eq_tautology_del:                   9
% 7.39/1.48  sim_eq_res_simp:                        0
% 7.39/1.48  sim_fw_demodulated:                     6
% 7.39/1.48  sim_bw_demodulated:                     15
% 7.39/1.48  sim_light_normalised:                   57
% 7.39/1.48  sim_joinable_taut:                      0
% 7.39/1.48  sim_joinable_simp:                      0
% 7.39/1.48  sim_ac_normalised:                      0
% 7.39/1.48  sim_smt_subsumption:                    0
% 7.39/1.48  
%------------------------------------------------------------------------------
