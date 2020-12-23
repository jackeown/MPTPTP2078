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

% Result     : Theorem 15.47s
% Output     : CNFRefutation 15.47s
% Verified   : 
% Statistics : Number of formulae       :  220 (2048 expanded)
%              Number of clauses        :  139 ( 563 expanded)
%              Number of leaves         :   22 ( 541 expanded)
%              Depth                    :   26
%              Number of atoms          :  822 (17758 expanded)
%              Number of equality atoms :  419 (6456 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f46,f45])).

fof(f81,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
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

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f86,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_403,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_404,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_488,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_404])).

cnf(c_1168,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_1726,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1168])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_41,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2052,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1726,c_37,c_38,c_39,c_40,c_41,c_42])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1178,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3047,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2052,c_1178])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_665,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_700,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_666,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1280,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1281,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_6,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2963,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2964,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2963])).

cnf(c_13,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_391,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_391,c_14])).

cnf(c_1169,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1282,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2045,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1169,c_36,c_34,c_33,c_31,c_399,c_1282])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f70])).

cnf(c_1182,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5377,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_1182])).

cnf(c_5408,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5377,c_37,c_38,c_39])).

cnf(c_5409,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5408])).

cnf(c_5412,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_5409])).

cnf(c_8063,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3047,c_40,c_41,c_42,c_27,c_700,c_1281,c_2964,c_5412])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1190,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8065,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8063,c_1190])).

cnf(c_1176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1188,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2295,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1176,c_1188])).

cnf(c_2298,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2295,c_2052])).

cnf(c_8066,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8065,c_2298])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1710,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_1711,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1710])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1960,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1961,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1960])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2966,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2967,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2966])).

cnf(c_42554,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8066,c_40,c_42,c_1711,c_1961,c_2967])).

cnf(c_1173,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2296,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1173,c_1188])).

cnf(c_2297,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2296,c_30])).

cnf(c_1189,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2254,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_1189])).

cnf(c_1171,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1194,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1197,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3053,plain,
    ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1197])).

cnf(c_9566,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1171,c_3053])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1177,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1191,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3089,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_1191])).

cnf(c_1974,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1975,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_3140,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3089,c_37,c_39,c_1975])).

cnf(c_9570,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(sK2,k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9566,c_3140])).

cnf(c_9673,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(sK2,k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9570,c_39,c_1975])).

cnf(c_9674,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(sK2,k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9673])).

cnf(c_9682,plain,
    ( k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2254,c_9674])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1196,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2358,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2254,c_1196])).

cnf(c_2359,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2358,c_2297])).

cnf(c_3046,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_1178])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1245,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1370,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_1587,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_3097,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3046,c_36,c_35,c_34,c_30,c_28,c_26,c_1587])).

cnf(c_9689,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_9682,c_2297,c_2359,c_3097])).

cnf(c_2,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_9690,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_9689,c_2])).

cnf(c_2253,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1189])).

cnf(c_1174,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9565,plain,
    ( k9_relat_1(k2_funct_1(sK3),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_3053])).

cnf(c_5518,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5412,c_40,c_41,c_42,c_27,c_700,c_1281,c_2964])).

cnf(c_5522,plain,
    ( k9_relat_1(k2_funct_1(sK3),X0) = k10_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5518,c_1191])).

cnf(c_5609,plain,
    ( k9_relat_1(k2_funct_1(sK3),X0) = k10_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5522,c_40,c_42,c_1711])).

cnf(c_9571,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k10_relat_1(sK3,k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9565,c_5609])).

cnf(c_9760,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k10_relat_1(sK3,k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9571,c_42,c_1711])).

cnf(c_9761,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k10_relat_1(sK3,k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9760])).

cnf(c_9768,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k10_relat_1(sK3,k2_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_2253,c_9761])).

cnf(c_2355,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2253,c_1196])).

cnf(c_2356,plain,
    ( k10_relat_1(sK3,sK0) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2355,c_2298])).

cnf(c_9777,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_9768,c_2298,c_2356,c_8063])).

cnf(c_9778,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_9777,c_2])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1184,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3511,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1184])).

cnf(c_4385,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3511,c_40])).

cnf(c_4386,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4385])).

cnf(c_4393,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_4386])).

cnf(c_4394,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4393,c_2045])).

cnf(c_4831,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4394,c_37])).

cnf(c_5053,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4831,c_1190])).

cnf(c_5054,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5053,c_2297,c_2298])).

cnf(c_5055,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5054])).

cnf(c_7423,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5055,c_37,c_39,c_40,c_41,c_42,c_27,c_700,c_1281,c_1711,c_1975,c_2964,c_5412])).

cnf(c_7424,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(renaming,[status(thm)],[c_7423])).

cnf(c_9904,plain,
    ( k2_funct_1(sK3) = sK2
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_9778,c_7424])).

cnf(c_9906,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_9904])).

cnf(c_42558,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42554,c_2297,c_9690,c_9906])).

cnf(c_42559,plain,
    ( k2_funct_1(sK2) = sK3
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_42558])).

cnf(c_25,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42559,c_25,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:50:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.47/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.47/2.48  
% 15.47/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.47/2.48  
% 15.47/2.48  ------  iProver source info
% 15.47/2.48  
% 15.47/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.47/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.47/2.48  git: non_committed_changes: false
% 15.47/2.48  git: last_make_outside_of_git: false
% 15.47/2.48  
% 15.47/2.48  ------ 
% 15.47/2.48  
% 15.47/2.48  ------ Input Options
% 15.47/2.48  
% 15.47/2.48  --out_options                           all
% 15.47/2.48  --tptp_safe_out                         true
% 15.47/2.48  --problem_path                          ""
% 15.47/2.48  --include_path                          ""
% 15.47/2.48  --clausifier                            res/vclausify_rel
% 15.47/2.48  --clausifier_options                    ""
% 15.47/2.48  --stdin                                 false
% 15.47/2.48  --stats_out                             all
% 15.47/2.48  
% 15.47/2.48  ------ General Options
% 15.47/2.48  
% 15.47/2.48  --fof                                   false
% 15.47/2.48  --time_out_real                         305.
% 15.47/2.48  --time_out_virtual                      -1.
% 15.47/2.48  --symbol_type_check                     false
% 15.47/2.48  --clausify_out                          false
% 15.47/2.48  --sig_cnt_out                           false
% 15.47/2.48  --trig_cnt_out                          false
% 15.47/2.48  --trig_cnt_out_tolerance                1.
% 15.47/2.48  --trig_cnt_out_sk_spl                   false
% 15.47/2.48  --abstr_cl_out                          false
% 15.47/2.48  
% 15.47/2.48  ------ Global Options
% 15.47/2.48  
% 15.47/2.48  --schedule                              default
% 15.47/2.48  --add_important_lit                     false
% 15.47/2.48  --prop_solver_per_cl                    1000
% 15.47/2.48  --min_unsat_core                        false
% 15.47/2.48  --soft_assumptions                      false
% 15.47/2.48  --soft_lemma_size                       3
% 15.47/2.48  --prop_impl_unit_size                   0
% 15.47/2.48  --prop_impl_unit                        []
% 15.47/2.48  --share_sel_clauses                     true
% 15.47/2.48  --reset_solvers                         false
% 15.47/2.48  --bc_imp_inh                            [conj_cone]
% 15.47/2.48  --conj_cone_tolerance                   3.
% 15.47/2.48  --extra_neg_conj                        none
% 15.47/2.48  --large_theory_mode                     true
% 15.47/2.48  --prolific_symb_bound                   200
% 15.47/2.48  --lt_threshold                          2000
% 15.47/2.48  --clause_weak_htbl                      true
% 15.47/2.48  --gc_record_bc_elim                     false
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing Options
% 15.47/2.48  
% 15.47/2.48  --preprocessing_flag                    true
% 15.47/2.48  --time_out_prep_mult                    0.1
% 15.47/2.48  --splitting_mode                        input
% 15.47/2.48  --splitting_grd                         true
% 15.47/2.48  --splitting_cvd                         false
% 15.47/2.48  --splitting_cvd_svl                     false
% 15.47/2.48  --splitting_nvd                         32
% 15.47/2.48  --sub_typing                            true
% 15.47/2.48  --prep_gs_sim                           true
% 15.47/2.48  --prep_unflatten                        true
% 15.47/2.48  --prep_res_sim                          true
% 15.47/2.48  --prep_upred                            true
% 15.47/2.48  --prep_sem_filter                       exhaustive
% 15.47/2.48  --prep_sem_filter_out                   false
% 15.47/2.48  --pred_elim                             true
% 15.47/2.48  --res_sim_input                         true
% 15.47/2.48  --eq_ax_congr_red                       true
% 15.47/2.48  --pure_diseq_elim                       true
% 15.47/2.48  --brand_transform                       false
% 15.47/2.48  --non_eq_to_eq                          false
% 15.47/2.48  --prep_def_merge                        true
% 15.47/2.48  --prep_def_merge_prop_impl              false
% 15.47/2.48  --prep_def_merge_mbd                    true
% 15.47/2.48  --prep_def_merge_tr_red                 false
% 15.47/2.48  --prep_def_merge_tr_cl                  false
% 15.47/2.48  --smt_preprocessing                     true
% 15.47/2.48  --smt_ac_axioms                         fast
% 15.47/2.48  --preprocessed_out                      false
% 15.47/2.48  --preprocessed_stats                    false
% 15.47/2.48  
% 15.47/2.48  ------ Abstraction refinement Options
% 15.47/2.48  
% 15.47/2.48  --abstr_ref                             []
% 15.47/2.48  --abstr_ref_prep                        false
% 15.47/2.48  --abstr_ref_until_sat                   false
% 15.47/2.48  --abstr_ref_sig_restrict                funpre
% 15.47/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.47/2.48  --abstr_ref_under                       []
% 15.47/2.48  
% 15.47/2.48  ------ SAT Options
% 15.47/2.48  
% 15.47/2.48  --sat_mode                              false
% 15.47/2.48  --sat_fm_restart_options                ""
% 15.47/2.48  --sat_gr_def                            false
% 15.47/2.48  --sat_epr_types                         true
% 15.47/2.48  --sat_non_cyclic_types                  false
% 15.47/2.48  --sat_finite_models                     false
% 15.47/2.48  --sat_fm_lemmas                         false
% 15.47/2.48  --sat_fm_prep                           false
% 15.47/2.48  --sat_fm_uc_incr                        true
% 15.47/2.48  --sat_out_model                         small
% 15.47/2.48  --sat_out_clauses                       false
% 15.47/2.48  
% 15.47/2.48  ------ QBF Options
% 15.47/2.48  
% 15.47/2.48  --qbf_mode                              false
% 15.47/2.48  --qbf_elim_univ                         false
% 15.47/2.48  --qbf_dom_inst                          none
% 15.47/2.48  --qbf_dom_pre_inst                      false
% 15.47/2.48  --qbf_sk_in                             false
% 15.47/2.48  --qbf_pred_elim                         true
% 15.47/2.48  --qbf_split                             512
% 15.47/2.48  
% 15.47/2.48  ------ BMC1 Options
% 15.47/2.48  
% 15.47/2.48  --bmc1_incremental                      false
% 15.47/2.48  --bmc1_axioms                           reachable_all
% 15.47/2.48  --bmc1_min_bound                        0
% 15.47/2.48  --bmc1_max_bound                        -1
% 15.47/2.48  --bmc1_max_bound_default                -1
% 15.47/2.48  --bmc1_symbol_reachability              true
% 15.47/2.48  --bmc1_property_lemmas                  false
% 15.47/2.48  --bmc1_k_induction                      false
% 15.47/2.48  --bmc1_non_equiv_states                 false
% 15.47/2.48  --bmc1_deadlock                         false
% 15.47/2.48  --bmc1_ucm                              false
% 15.47/2.48  --bmc1_add_unsat_core                   none
% 15.47/2.48  --bmc1_unsat_core_children              false
% 15.47/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.47/2.48  --bmc1_out_stat                         full
% 15.47/2.48  --bmc1_ground_init                      false
% 15.47/2.48  --bmc1_pre_inst_next_state              false
% 15.47/2.48  --bmc1_pre_inst_state                   false
% 15.47/2.48  --bmc1_pre_inst_reach_state             false
% 15.47/2.48  --bmc1_out_unsat_core                   false
% 15.47/2.48  --bmc1_aig_witness_out                  false
% 15.47/2.48  --bmc1_verbose                          false
% 15.47/2.48  --bmc1_dump_clauses_tptp                false
% 15.47/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.47/2.48  --bmc1_dump_file                        -
% 15.47/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.47/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.47/2.48  --bmc1_ucm_extend_mode                  1
% 15.47/2.48  --bmc1_ucm_init_mode                    2
% 15.47/2.48  --bmc1_ucm_cone_mode                    none
% 15.47/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.47/2.48  --bmc1_ucm_relax_model                  4
% 15.47/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.47/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.47/2.48  --bmc1_ucm_layered_model                none
% 15.47/2.48  --bmc1_ucm_max_lemma_size               10
% 15.47/2.48  
% 15.47/2.48  ------ AIG Options
% 15.47/2.48  
% 15.47/2.48  --aig_mode                              false
% 15.47/2.48  
% 15.47/2.48  ------ Instantiation Options
% 15.47/2.48  
% 15.47/2.48  --instantiation_flag                    true
% 15.47/2.48  --inst_sos_flag                         true
% 15.47/2.48  --inst_sos_phase                        true
% 15.47/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.47/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.47/2.48  --inst_lit_sel_side                     num_symb
% 15.47/2.48  --inst_solver_per_active                1400
% 15.47/2.48  --inst_solver_calls_frac                1.
% 15.47/2.48  --inst_passive_queue_type               priority_queues
% 15.47/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.47/2.48  --inst_passive_queues_freq              [25;2]
% 15.47/2.48  --inst_dismatching                      true
% 15.47/2.48  --inst_eager_unprocessed_to_passive     true
% 15.47/2.48  --inst_prop_sim_given                   true
% 15.47/2.48  --inst_prop_sim_new                     false
% 15.47/2.48  --inst_subs_new                         false
% 15.47/2.48  --inst_eq_res_simp                      false
% 15.47/2.48  --inst_subs_given                       false
% 15.47/2.48  --inst_orphan_elimination               true
% 15.47/2.48  --inst_learning_loop_flag               true
% 15.47/2.48  --inst_learning_start                   3000
% 15.47/2.48  --inst_learning_factor                  2
% 15.47/2.48  --inst_start_prop_sim_after_learn       3
% 15.47/2.48  --inst_sel_renew                        solver
% 15.47/2.48  --inst_lit_activity_flag                true
% 15.47/2.48  --inst_restr_to_given                   false
% 15.47/2.48  --inst_activity_threshold               500
% 15.47/2.48  --inst_out_proof                        true
% 15.47/2.48  
% 15.47/2.48  ------ Resolution Options
% 15.47/2.48  
% 15.47/2.48  --resolution_flag                       true
% 15.47/2.48  --res_lit_sel                           adaptive
% 15.47/2.48  --res_lit_sel_side                      none
% 15.47/2.48  --res_ordering                          kbo
% 15.47/2.48  --res_to_prop_solver                    active
% 15.47/2.48  --res_prop_simpl_new                    false
% 15.47/2.48  --res_prop_simpl_given                  true
% 15.47/2.48  --res_passive_queue_type                priority_queues
% 15.47/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.47/2.48  --res_passive_queues_freq               [15;5]
% 15.47/2.48  --res_forward_subs                      full
% 15.47/2.48  --res_backward_subs                     full
% 15.47/2.48  --res_forward_subs_resolution           true
% 15.47/2.48  --res_backward_subs_resolution          true
% 15.47/2.48  --res_orphan_elimination                true
% 15.47/2.48  --res_time_limit                        2.
% 15.47/2.48  --res_out_proof                         true
% 15.47/2.48  
% 15.47/2.48  ------ Superposition Options
% 15.47/2.48  
% 15.47/2.48  --superposition_flag                    true
% 15.47/2.48  --sup_passive_queue_type                priority_queues
% 15.47/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.47/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.47/2.48  --demod_completeness_check              fast
% 15.47/2.48  --demod_use_ground                      true
% 15.47/2.48  --sup_to_prop_solver                    passive
% 15.47/2.48  --sup_prop_simpl_new                    true
% 15.47/2.48  --sup_prop_simpl_given                  true
% 15.47/2.48  --sup_fun_splitting                     true
% 15.47/2.48  --sup_smt_interval                      50000
% 15.47/2.48  
% 15.47/2.48  ------ Superposition Simplification Setup
% 15.47/2.48  
% 15.47/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.47/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.47/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.47/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.47/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.47/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.47/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.47/2.48  --sup_immed_triv                        [TrivRules]
% 15.47/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_immed_bw_main                     []
% 15.47/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.47/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.47/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_input_bw                          []
% 15.47/2.48  
% 15.47/2.48  ------ Combination Options
% 15.47/2.48  
% 15.47/2.48  --comb_res_mult                         3
% 15.47/2.48  --comb_sup_mult                         2
% 15.47/2.48  --comb_inst_mult                        10
% 15.47/2.48  
% 15.47/2.48  ------ Debug Options
% 15.47/2.48  
% 15.47/2.48  --dbg_backtrace                         false
% 15.47/2.48  --dbg_dump_prop_clauses                 false
% 15.47/2.48  --dbg_dump_prop_clauses_file            -
% 15.47/2.48  --dbg_out_stat                          false
% 15.47/2.48  ------ Parsing...
% 15.47/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.47/2.48  ------ Proving...
% 15.47/2.48  ------ Problem Properties 
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  clauses                                 36
% 15.47/2.48  conjectures                             11
% 15.47/2.48  EPR                                     7
% 15.47/2.48  Horn                                    32
% 15.47/2.48  unary                                   16
% 15.47/2.48  binary                                  4
% 15.47/2.48  lits                                    128
% 15.47/2.48  lits eq                                 31
% 15.47/2.48  fd_pure                                 0
% 15.47/2.48  fd_pseudo                               0
% 15.47/2.48  fd_cond                                 4
% 15.47/2.48  fd_pseudo_cond                          1
% 15.47/2.48  AC symbols                              0
% 15.47/2.48  
% 15.47/2.48  ------ Schedule dynamic 5 is on 
% 15.47/2.48  
% 15.47/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  ------ 
% 15.47/2.48  Current options:
% 15.47/2.48  ------ 
% 15.47/2.48  
% 15.47/2.48  ------ Input Options
% 15.47/2.48  
% 15.47/2.48  --out_options                           all
% 15.47/2.48  --tptp_safe_out                         true
% 15.47/2.48  --problem_path                          ""
% 15.47/2.48  --include_path                          ""
% 15.47/2.48  --clausifier                            res/vclausify_rel
% 15.47/2.48  --clausifier_options                    ""
% 15.47/2.48  --stdin                                 false
% 15.47/2.48  --stats_out                             all
% 15.47/2.48  
% 15.47/2.48  ------ General Options
% 15.47/2.48  
% 15.47/2.48  --fof                                   false
% 15.47/2.48  --time_out_real                         305.
% 15.47/2.48  --time_out_virtual                      -1.
% 15.47/2.48  --symbol_type_check                     false
% 15.47/2.48  --clausify_out                          false
% 15.47/2.48  --sig_cnt_out                           false
% 15.47/2.48  --trig_cnt_out                          false
% 15.47/2.48  --trig_cnt_out_tolerance                1.
% 15.47/2.48  --trig_cnt_out_sk_spl                   false
% 15.47/2.48  --abstr_cl_out                          false
% 15.47/2.48  
% 15.47/2.48  ------ Global Options
% 15.47/2.48  
% 15.47/2.48  --schedule                              default
% 15.47/2.48  --add_important_lit                     false
% 15.47/2.48  --prop_solver_per_cl                    1000
% 15.47/2.48  --min_unsat_core                        false
% 15.47/2.48  --soft_assumptions                      false
% 15.47/2.48  --soft_lemma_size                       3
% 15.47/2.48  --prop_impl_unit_size                   0
% 15.47/2.48  --prop_impl_unit                        []
% 15.47/2.48  --share_sel_clauses                     true
% 15.47/2.48  --reset_solvers                         false
% 15.47/2.48  --bc_imp_inh                            [conj_cone]
% 15.47/2.48  --conj_cone_tolerance                   3.
% 15.47/2.48  --extra_neg_conj                        none
% 15.47/2.48  --large_theory_mode                     true
% 15.47/2.48  --prolific_symb_bound                   200
% 15.47/2.48  --lt_threshold                          2000
% 15.47/2.48  --clause_weak_htbl                      true
% 15.47/2.48  --gc_record_bc_elim                     false
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing Options
% 15.47/2.48  
% 15.47/2.48  --preprocessing_flag                    true
% 15.47/2.48  --time_out_prep_mult                    0.1
% 15.47/2.48  --splitting_mode                        input
% 15.47/2.48  --splitting_grd                         true
% 15.47/2.48  --splitting_cvd                         false
% 15.47/2.48  --splitting_cvd_svl                     false
% 15.47/2.48  --splitting_nvd                         32
% 15.47/2.48  --sub_typing                            true
% 15.47/2.48  --prep_gs_sim                           true
% 15.47/2.48  --prep_unflatten                        true
% 15.47/2.48  --prep_res_sim                          true
% 15.47/2.48  --prep_upred                            true
% 15.47/2.48  --prep_sem_filter                       exhaustive
% 15.47/2.48  --prep_sem_filter_out                   false
% 15.47/2.48  --pred_elim                             true
% 15.47/2.48  --res_sim_input                         true
% 15.47/2.48  --eq_ax_congr_red                       true
% 15.47/2.48  --pure_diseq_elim                       true
% 15.47/2.48  --brand_transform                       false
% 15.47/2.48  --non_eq_to_eq                          false
% 15.47/2.48  --prep_def_merge                        true
% 15.47/2.48  --prep_def_merge_prop_impl              false
% 15.47/2.48  --prep_def_merge_mbd                    true
% 15.47/2.48  --prep_def_merge_tr_red                 false
% 15.47/2.48  --prep_def_merge_tr_cl                  false
% 15.47/2.48  --smt_preprocessing                     true
% 15.47/2.48  --smt_ac_axioms                         fast
% 15.47/2.48  --preprocessed_out                      false
% 15.47/2.48  --preprocessed_stats                    false
% 15.47/2.48  
% 15.47/2.48  ------ Abstraction refinement Options
% 15.47/2.48  
% 15.47/2.48  --abstr_ref                             []
% 15.47/2.48  --abstr_ref_prep                        false
% 15.47/2.48  --abstr_ref_until_sat                   false
% 15.47/2.48  --abstr_ref_sig_restrict                funpre
% 15.47/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.47/2.48  --abstr_ref_under                       []
% 15.47/2.48  
% 15.47/2.48  ------ SAT Options
% 15.47/2.48  
% 15.47/2.48  --sat_mode                              false
% 15.47/2.48  --sat_fm_restart_options                ""
% 15.47/2.48  --sat_gr_def                            false
% 15.47/2.48  --sat_epr_types                         true
% 15.47/2.48  --sat_non_cyclic_types                  false
% 15.47/2.48  --sat_finite_models                     false
% 15.47/2.48  --sat_fm_lemmas                         false
% 15.47/2.48  --sat_fm_prep                           false
% 15.47/2.48  --sat_fm_uc_incr                        true
% 15.47/2.48  --sat_out_model                         small
% 15.47/2.48  --sat_out_clauses                       false
% 15.47/2.48  
% 15.47/2.48  ------ QBF Options
% 15.47/2.48  
% 15.47/2.48  --qbf_mode                              false
% 15.47/2.48  --qbf_elim_univ                         false
% 15.47/2.48  --qbf_dom_inst                          none
% 15.47/2.48  --qbf_dom_pre_inst                      false
% 15.47/2.48  --qbf_sk_in                             false
% 15.47/2.48  --qbf_pred_elim                         true
% 15.47/2.48  --qbf_split                             512
% 15.47/2.48  
% 15.47/2.48  ------ BMC1 Options
% 15.47/2.48  
% 15.47/2.48  --bmc1_incremental                      false
% 15.47/2.48  --bmc1_axioms                           reachable_all
% 15.47/2.48  --bmc1_min_bound                        0
% 15.47/2.48  --bmc1_max_bound                        -1
% 15.47/2.48  --bmc1_max_bound_default                -1
% 15.47/2.48  --bmc1_symbol_reachability              true
% 15.47/2.48  --bmc1_property_lemmas                  false
% 15.47/2.48  --bmc1_k_induction                      false
% 15.47/2.48  --bmc1_non_equiv_states                 false
% 15.47/2.48  --bmc1_deadlock                         false
% 15.47/2.48  --bmc1_ucm                              false
% 15.47/2.48  --bmc1_add_unsat_core                   none
% 15.47/2.48  --bmc1_unsat_core_children              false
% 15.47/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.47/2.48  --bmc1_out_stat                         full
% 15.47/2.48  --bmc1_ground_init                      false
% 15.47/2.48  --bmc1_pre_inst_next_state              false
% 15.47/2.48  --bmc1_pre_inst_state                   false
% 15.47/2.48  --bmc1_pre_inst_reach_state             false
% 15.47/2.48  --bmc1_out_unsat_core                   false
% 15.47/2.48  --bmc1_aig_witness_out                  false
% 15.47/2.48  --bmc1_verbose                          false
% 15.47/2.48  --bmc1_dump_clauses_tptp                false
% 15.47/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.47/2.48  --bmc1_dump_file                        -
% 15.47/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.47/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.47/2.48  --bmc1_ucm_extend_mode                  1
% 15.47/2.48  --bmc1_ucm_init_mode                    2
% 15.47/2.48  --bmc1_ucm_cone_mode                    none
% 15.47/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.47/2.48  --bmc1_ucm_relax_model                  4
% 15.47/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.47/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.47/2.48  --bmc1_ucm_layered_model                none
% 15.47/2.48  --bmc1_ucm_max_lemma_size               10
% 15.47/2.48  
% 15.47/2.48  ------ AIG Options
% 15.47/2.48  
% 15.47/2.48  --aig_mode                              false
% 15.47/2.48  
% 15.47/2.48  ------ Instantiation Options
% 15.47/2.48  
% 15.47/2.48  --instantiation_flag                    true
% 15.47/2.48  --inst_sos_flag                         true
% 15.47/2.48  --inst_sos_phase                        true
% 15.47/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.47/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.47/2.48  --inst_lit_sel_side                     none
% 15.47/2.48  --inst_solver_per_active                1400
% 15.47/2.48  --inst_solver_calls_frac                1.
% 15.47/2.48  --inst_passive_queue_type               priority_queues
% 15.47/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.47/2.48  --inst_passive_queues_freq              [25;2]
% 15.47/2.48  --inst_dismatching                      true
% 15.47/2.48  --inst_eager_unprocessed_to_passive     true
% 15.47/2.48  --inst_prop_sim_given                   true
% 15.47/2.48  --inst_prop_sim_new                     false
% 15.47/2.48  --inst_subs_new                         false
% 15.47/2.48  --inst_eq_res_simp                      false
% 15.47/2.48  --inst_subs_given                       false
% 15.47/2.48  --inst_orphan_elimination               true
% 15.47/2.48  --inst_learning_loop_flag               true
% 15.47/2.48  --inst_learning_start                   3000
% 15.47/2.48  --inst_learning_factor                  2
% 15.47/2.48  --inst_start_prop_sim_after_learn       3
% 15.47/2.48  --inst_sel_renew                        solver
% 15.47/2.48  --inst_lit_activity_flag                true
% 15.47/2.48  --inst_restr_to_given                   false
% 15.47/2.48  --inst_activity_threshold               500
% 15.47/2.48  --inst_out_proof                        true
% 15.47/2.48  
% 15.47/2.48  ------ Resolution Options
% 15.47/2.48  
% 15.47/2.48  --resolution_flag                       false
% 15.47/2.48  --res_lit_sel                           adaptive
% 15.47/2.48  --res_lit_sel_side                      none
% 15.47/2.48  --res_ordering                          kbo
% 15.47/2.48  --res_to_prop_solver                    active
% 15.47/2.48  --res_prop_simpl_new                    false
% 15.47/2.48  --res_prop_simpl_given                  true
% 15.47/2.48  --res_passive_queue_type                priority_queues
% 15.47/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.47/2.48  --res_passive_queues_freq               [15;5]
% 15.47/2.48  --res_forward_subs                      full
% 15.47/2.48  --res_backward_subs                     full
% 15.47/2.48  --res_forward_subs_resolution           true
% 15.47/2.48  --res_backward_subs_resolution          true
% 15.47/2.48  --res_orphan_elimination                true
% 15.47/2.48  --res_time_limit                        2.
% 15.47/2.48  --res_out_proof                         true
% 15.47/2.48  
% 15.47/2.48  ------ Superposition Options
% 15.47/2.48  
% 15.47/2.48  --superposition_flag                    true
% 15.47/2.48  --sup_passive_queue_type                priority_queues
% 15.47/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.47/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.47/2.48  --demod_completeness_check              fast
% 15.47/2.48  --demod_use_ground                      true
% 15.47/2.48  --sup_to_prop_solver                    passive
% 15.47/2.48  --sup_prop_simpl_new                    true
% 15.47/2.48  --sup_prop_simpl_given                  true
% 15.47/2.48  --sup_fun_splitting                     true
% 15.47/2.48  --sup_smt_interval                      50000
% 15.47/2.48  
% 15.47/2.48  ------ Superposition Simplification Setup
% 15.47/2.48  
% 15.47/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.47/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.47/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.47/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.47/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.47/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.47/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.47/2.48  --sup_immed_triv                        [TrivRules]
% 15.47/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_immed_bw_main                     []
% 15.47/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.47/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.47/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.47/2.48  --sup_input_bw                          []
% 15.47/2.48  
% 15.47/2.48  ------ Combination Options
% 15.47/2.48  
% 15.47/2.48  --comb_res_mult                         3
% 15.47/2.48  --comb_sup_mult                         2
% 15.47/2.48  --comb_inst_mult                        10
% 15.47/2.48  
% 15.47/2.48  ------ Debug Options
% 15.47/2.48  
% 15.47/2.48  --dbg_backtrace                         false
% 15.47/2.48  --dbg_dump_prop_clauses                 false
% 15.47/2.48  --dbg_dump_prop_clauses_file            -
% 15.47/2.48  --dbg_out_stat                          false
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  ------ Proving...
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  % SZS status Theorem for theBenchmark.p
% 15.47/2.48  
% 15.47/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.47/2.48  
% 15.47/2.48  fof(f15,axiom,(
% 15.47/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f36,plain,(
% 15.47/2.48    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.47/2.48    inference(ennf_transformation,[],[f15])).
% 15.47/2.48  
% 15.47/2.48  fof(f37,plain,(
% 15.47/2.48    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.47/2.48    inference(flattening,[],[f36])).
% 15.47/2.48  
% 15.47/2.48  fof(f67,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f37])).
% 15.47/2.48  
% 15.47/2.48  fof(f18,conjecture,(
% 15.47/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f19,negated_conjecture,(
% 15.47/2.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.47/2.48    inference(negated_conjecture,[],[f18])).
% 15.47/2.48  
% 15.47/2.48  fof(f42,plain,(
% 15.47/2.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.47/2.48    inference(ennf_transformation,[],[f19])).
% 15.47/2.48  
% 15.47/2.48  fof(f43,plain,(
% 15.47/2.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.47/2.48    inference(flattening,[],[f42])).
% 15.47/2.48  
% 15.47/2.48  fof(f46,plain,(
% 15.47/2.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f45,plain,(
% 15.47/2.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 15.47/2.48    introduced(choice_axiom,[])).
% 15.47/2.48  
% 15.47/2.48  fof(f47,plain,(
% 15.47/2.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 15.47/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f46,f45])).
% 15.47/2.48  
% 15.47/2.48  fof(f81,plain,(
% 15.47/2.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f74,plain,(
% 15.47/2.48    v1_funct_1(sK2)),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f75,plain,(
% 15.47/2.48    v1_funct_2(sK2,sK0,sK1)),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f76,plain,(
% 15.47/2.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f77,plain,(
% 15.47/2.48    v1_funct_1(sK3)),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f78,plain,(
% 15.47/2.48    v1_funct_2(sK3,sK1,sK0)),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f79,plain,(
% 15.47/2.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f17,axiom,(
% 15.47/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f40,plain,(
% 15.47/2.48    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.47/2.48    inference(ennf_transformation,[],[f17])).
% 15.47/2.48  
% 15.47/2.48  fof(f41,plain,(
% 15.47/2.48    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.47/2.48    inference(flattening,[],[f40])).
% 15.47/2.48  
% 15.47/2.48  fof(f72,plain,(
% 15.47/2.48    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f41])).
% 15.47/2.48  
% 15.47/2.48  fof(f83,plain,(
% 15.47/2.48    k1_xboole_0 != sK0),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f5,axiom,(
% 15.47/2.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f55,plain,(
% 15.47/2.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 15.47/2.48    inference(cnf_transformation,[],[f5])).
% 15.47/2.48  
% 15.47/2.48  fof(f14,axiom,(
% 15.47/2.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f66,plain,(
% 15.47/2.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f14])).
% 15.47/2.48  
% 15.47/2.48  fof(f88,plain,(
% 15.47/2.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 15.47/2.48    inference(definition_unfolding,[],[f55,f66])).
% 15.47/2.48  
% 15.47/2.48  fof(f10,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f30,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.47/2.48    inference(ennf_transformation,[],[f10])).
% 15.47/2.48  
% 15.47/2.48  fof(f31,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.47/2.48    inference(flattening,[],[f30])).
% 15.47/2.48  
% 15.47/2.48  fof(f44,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.47/2.48    inference(nnf_transformation,[],[f31])).
% 15.47/2.48  
% 15.47/2.48  fof(f60,plain,(
% 15.47/2.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.47/2.48    inference(cnf_transformation,[],[f44])).
% 15.47/2.48  
% 15.47/2.48  fof(f11,axiom,(
% 15.47/2.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f62,plain,(
% 15.47/2.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.47/2.48    inference(cnf_transformation,[],[f11])).
% 15.47/2.48  
% 15.47/2.48  fof(f91,plain,(
% 15.47/2.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.47/2.48    inference(definition_unfolding,[],[f62,f66])).
% 15.47/2.48  
% 15.47/2.48  fof(f12,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f32,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.47/2.48    inference(ennf_transformation,[],[f12])).
% 15.47/2.48  
% 15.47/2.48  fof(f33,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.47/2.48    inference(flattening,[],[f32])).
% 15.47/2.48  
% 15.47/2.48  fof(f64,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f33])).
% 15.47/2.48  
% 15.47/2.48  fof(f80,plain,(
% 15.47/2.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f16,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f38,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 15.47/2.48    inference(ennf_transformation,[],[f16])).
% 15.47/2.48  
% 15.47/2.48  fof(f39,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 15.47/2.48    inference(flattening,[],[f38])).
% 15.47/2.48  
% 15.47/2.48  fof(f70,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f39])).
% 15.47/2.48  
% 15.47/2.48  fof(f7,axiom,(
% 15.47/2.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f26,plain,(
% 15.47/2.48    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.47/2.48    inference(ennf_transformation,[],[f7])).
% 15.47/2.48  
% 15.47/2.48  fof(f27,plain,(
% 15.47/2.48    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.47/2.48    inference(flattening,[],[f26])).
% 15.47/2.48  
% 15.47/2.48  fof(f57,plain,(
% 15.47/2.48    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f27])).
% 15.47/2.48  
% 15.47/2.48  fof(f90,plain,(
% 15.47/2.48    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.47/2.48    inference(definition_unfolding,[],[f57,f66])).
% 15.47/2.48  
% 15.47/2.48  fof(f9,axiom,(
% 15.47/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f29,plain,(
% 15.47/2.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.47/2.48    inference(ennf_transformation,[],[f9])).
% 15.47/2.48  
% 15.47/2.48  fof(f59,plain,(
% 15.47/2.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.47/2.48    inference(cnf_transformation,[],[f29])).
% 15.47/2.48  
% 15.47/2.48  fof(f8,axiom,(
% 15.47/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f28,plain,(
% 15.47/2.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.47/2.48    inference(ennf_transformation,[],[f8])).
% 15.47/2.48  
% 15.47/2.48  fof(f58,plain,(
% 15.47/2.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.47/2.48    inference(cnf_transformation,[],[f28])).
% 15.47/2.48  
% 15.47/2.48  fof(f4,axiom,(
% 15.47/2.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f22,plain,(
% 15.47/2.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.47/2.48    inference(ennf_transformation,[],[f4])).
% 15.47/2.48  
% 15.47/2.48  fof(f23,plain,(
% 15.47/2.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.47/2.48    inference(flattening,[],[f22])).
% 15.47/2.48  
% 15.47/2.48  fof(f53,plain,(
% 15.47/2.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f23])).
% 15.47/2.48  
% 15.47/2.48  fof(f52,plain,(
% 15.47/2.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f23])).
% 15.47/2.48  
% 15.47/2.48  fof(f1,axiom,(
% 15.47/2.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f20,plain,(
% 15.47/2.48    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.47/2.48    inference(ennf_transformation,[],[f1])).
% 15.47/2.48  
% 15.47/2.48  fof(f48,plain,(
% 15.47/2.48    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f20])).
% 15.47/2.48  
% 15.47/2.48  fof(f82,plain,(
% 15.47/2.48    v2_funct_1(sK2)),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f6,axiom,(
% 15.47/2.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f24,plain,(
% 15.47/2.48    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.47/2.48    inference(ennf_transformation,[],[f6])).
% 15.47/2.48  
% 15.47/2.48  fof(f25,plain,(
% 15.47/2.48    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.47/2.48    inference(flattening,[],[f24])).
% 15.47/2.48  
% 15.47/2.48  fof(f56,plain,(
% 15.47/2.48    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f25])).
% 15.47/2.48  
% 15.47/2.48  fof(f2,axiom,(
% 15.47/2.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f21,plain,(
% 15.47/2.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 15.47/2.48    inference(ennf_transformation,[],[f2])).
% 15.47/2.48  
% 15.47/2.48  fof(f49,plain,(
% 15.47/2.48    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f21])).
% 15.47/2.48  
% 15.47/2.48  fof(f84,plain,(
% 15.47/2.48    k1_xboole_0 != sK1),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  fof(f3,axiom,(
% 15.47/2.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f51,plain,(
% 15.47/2.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 15.47/2.48    inference(cnf_transformation,[],[f3])).
% 15.47/2.48  
% 15.47/2.48  fof(f86,plain,(
% 15.47/2.48    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 15.47/2.48    inference(definition_unfolding,[],[f51,f66])).
% 15.47/2.48  
% 15.47/2.48  fof(f13,axiom,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.47/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.48  
% 15.47/2.48  fof(f34,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.47/2.48    inference(ennf_transformation,[],[f13])).
% 15.47/2.48  
% 15.47/2.48  fof(f35,plain,(
% 15.47/2.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.47/2.48    inference(flattening,[],[f34])).
% 15.47/2.48  
% 15.47/2.48  fof(f65,plain,(
% 15.47/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.47/2.48    inference(cnf_transformation,[],[f35])).
% 15.47/2.48  
% 15.47/2.48  fof(f85,plain,(
% 15.47/2.48    k2_funct_1(sK2) != sK3),
% 15.47/2.48    inference(cnf_transformation,[],[f47])).
% 15.47/2.48  
% 15.47/2.48  cnf(c_18,plain,
% 15.47/2.48      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 15.47/2.48      | ~ v1_funct_2(X2,X0,X1)
% 15.47/2.48      | ~ v1_funct_2(X3,X1,X0)
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 15.47/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.47/2.48      | ~ v1_funct_1(X2)
% 15.47/2.48      | ~ v1_funct_1(X3)
% 15.47/2.48      | k2_relset_1(X1,X0,X3) = X0 ),
% 15.47/2.48      inference(cnf_transformation,[],[f67]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_29,negated_conjecture,
% 15.47/2.48      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f81]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_403,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.47/2.48      | ~ v1_funct_2(X3,X2,X1)
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X3)
% 15.47/2.48      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.47/2.48      | k2_relset_1(X1,X2,X0) = X2
% 15.47/2.48      | k6_partfun1(X2) != k6_partfun1(sK0)
% 15.47/2.48      | sK0 != X2 ),
% 15.47/2.48      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_404,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,X1,sK0)
% 15.47/2.48      | ~ v1_funct_2(X2,sK0,X1)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 15.47/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X2)
% 15.47/2.48      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.47/2.48      | k2_relset_1(X1,sK0,X0) = sK0
% 15.47/2.48      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 15.47/2.48      inference(unflattening,[status(thm)],[c_403]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_488,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,X1,sK0)
% 15.47/2.48      | ~ v1_funct_2(X2,sK0,X1)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 15.47/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X2)
% 15.47/2.48      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.47/2.48      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 15.47/2.48      inference(equality_resolution_simp,[status(thm)],[c_404]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1168,plain,
% 15.47/2.48      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.47/2.48      | k2_relset_1(X0,sK0,X2) = sK0
% 15.47/2.48      | v1_funct_2(X2,X0,sK0) != iProver_top
% 15.47/2.48      | v1_funct_2(X1,sK0,X0) != iProver_top
% 15.47/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 15.47/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 15.47/2.48      | v1_funct_1(X2) != iProver_top
% 15.47/2.48      | v1_funct_1(X1) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1726,plain,
% 15.47/2.48      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 15.47/2.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.47/2.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.47/2.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.47/2.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top ),
% 15.47/2.48      inference(equality_resolution,[status(thm)],[c_1168]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_36,negated_conjecture,
% 15.47/2.48      ( v1_funct_1(sK2) ),
% 15.47/2.48      inference(cnf_transformation,[],[f74]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_37,plain,
% 15.47/2.48      ( v1_funct_1(sK2) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_35,negated_conjecture,
% 15.47/2.48      ( v1_funct_2(sK2,sK0,sK1) ),
% 15.47/2.48      inference(cnf_transformation,[],[f75]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_38,plain,
% 15.47/2.48      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_34,negated_conjecture,
% 15.47/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.47/2.48      inference(cnf_transformation,[],[f76]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_39,plain,
% 15.47/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_33,negated_conjecture,
% 15.47/2.48      ( v1_funct_1(sK3) ),
% 15.47/2.48      inference(cnf_transformation,[],[f77]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_40,plain,
% 15.47/2.48      ( v1_funct_1(sK3) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_32,negated_conjecture,
% 15.47/2.48      ( v1_funct_2(sK3,sK1,sK0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f78]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_41,plain,
% 15.47/2.48      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_31,negated_conjecture,
% 15.47/2.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 15.47/2.48      inference(cnf_transformation,[],[f79]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_42,plain,
% 15.47/2.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2052,plain,
% 15.47/2.48      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_1726,c_37,c_38,c_39,c_40,c_41,c_42]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_24,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | ~ v2_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | k2_relset_1(X1,X2,X0) != X2
% 15.47/2.48      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 15.47/2.48      | k1_xboole_0 = X2 ),
% 15.47/2.48      inference(cnf_transformation,[],[f72]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1178,plain,
% 15.47/2.48      ( k2_relset_1(X0,X1,X2) != X1
% 15.47/2.48      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 15.47/2.48      | k1_xboole_0 = X1
% 15.47/2.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.47/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.47/2.48      | v2_funct_1(X2) != iProver_top
% 15.47/2.48      | v1_funct_1(X2) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3047,plain,
% 15.47/2.48      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 15.47/2.48      | sK0 = k1_xboole_0
% 15.47/2.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.47/2.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.47/2.48      | v2_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_2052,c_1178]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_27,negated_conjecture,
% 15.47/2.48      ( k1_xboole_0 != sK0 ),
% 15.47/2.48      inference(cnf_transformation,[],[f83]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_665,plain,( X0 = X0 ),theory(equality) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_700,plain,
% 15.47/2.48      ( k1_xboole_0 = k1_xboole_0 ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_665]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_666,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1280,plain,
% 15.47/2.48      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_666]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1281,plain,
% 15.47/2.48      ( sK0 != k1_xboole_0
% 15.47/2.48      | k1_xboole_0 = sK0
% 15.47/2.48      | k1_xboole_0 != k1_xboole_0 ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_1280]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_6,plain,
% 15.47/2.48      ( v2_funct_1(k6_partfun1(X0)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f88]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2963,plain,
% 15.47/2.48      ( v2_funct_1(k6_partfun1(sK0)) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_6]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2964,plain,
% 15.47/2.48      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_2963]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_13,plain,
% 15.47/2.48      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.47/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.47/2.48      | X3 = X2 ),
% 15.47/2.48      inference(cnf_transformation,[],[f60]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_390,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | X3 = X0
% 15.47/2.48      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 15.47/2.48      | k6_partfun1(sK0) != X3
% 15.47/2.48      | sK0 != X2
% 15.47/2.48      | sK0 != X1 ),
% 15.47/2.48      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_391,plain,
% 15.47/2.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.47/2.48      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.47/2.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.47/2.48      inference(unflattening,[status(thm)],[c_390]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_14,plain,
% 15.47/2.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.47/2.48      inference(cnf_transformation,[],[f91]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_399,plain,
% 15.47/2.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.47/2.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.47/2.48      inference(forward_subsumption_resolution,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_391,c_14]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1169,plain,
% 15.47/2.48      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.47/2.48      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_15,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.47/2.48      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X3) ),
% 15.47/2.48      inference(cnf_transformation,[],[f64]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1282,plain,
% 15.47/2.48      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.47/2.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.47/2.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.47/2.48      | ~ v1_funct_1(sK3)
% 15.47/2.48      | ~ v1_funct_1(sK2) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_15]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2045,plain,
% 15.47/2.48      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_1169,c_36,c_34,c_33,c_31,c_399,c_1282]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_30,negated_conjecture,
% 15.47/2.48      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 15.47/2.48      inference(cnf_transformation,[],[f80]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_20,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,X1,X2)
% 15.47/2.48      | ~ v1_funct_2(X3,X4,X1)
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | v2_funct_1(X0)
% 15.47/2.48      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X3)
% 15.47/2.48      | k2_relset_1(X4,X1,X3) != X1
% 15.47/2.48      | k1_xboole_0 = X2 ),
% 15.47/2.48      inference(cnf_transformation,[],[f70]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1182,plain,
% 15.47/2.48      ( k2_relset_1(X0,X1,X2) != X1
% 15.47/2.48      | k1_xboole_0 = X3
% 15.47/2.48      | v1_funct_2(X4,X1,X3) != iProver_top
% 15.47/2.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.47/2.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 15.47/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.47/2.48      | v2_funct_1(X4) = iProver_top
% 15.47/2.48      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 15.47/2.48      | v1_funct_1(X4) != iProver_top
% 15.47/2.48      | v1_funct_1(X2) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5377,plain,
% 15.47/2.48      ( k1_xboole_0 = X0
% 15.47/2.48      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.47/2.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.47/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 15.47/2.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.47/2.48      | v2_funct_1(X1) = iProver_top
% 15.47/2.48      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 15.47/2.48      | v1_funct_1(X1) != iProver_top
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_30,c_1182]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5408,plain,
% 15.47/2.48      ( v1_funct_1(X1) != iProver_top
% 15.47/2.48      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 15.47/2.48      | v2_funct_1(X1) = iProver_top
% 15.47/2.48      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.47/2.48      | k1_xboole_0 = X0
% 15.47/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_5377,c_37,c_38,c_39]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5409,plain,
% 15.47/2.48      ( k1_xboole_0 = X0
% 15.47/2.48      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.47/2.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 15.47/2.48      | v2_funct_1(X1) = iProver_top
% 15.47/2.48      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 15.47/2.48      | v1_funct_1(X1) != iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_5408]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5412,plain,
% 15.47/2.48      ( sK0 = k1_xboole_0
% 15.47/2.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.47/2.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.47/2.48      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 15.47/2.48      | v2_funct_1(sK3) = iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_2045,c_5409]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_8063,plain,
% 15.47/2.48      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_3047,c_40,c_41,c_42,c_27,c_700,c_1281,c_2964,c_5412]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9,plain,
% 15.47/2.48      ( ~ v2_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X1)
% 15.47/2.48      | ~ v1_relat_1(X1)
% 15.47/2.48      | ~ v1_relat_1(X0)
% 15.47/2.48      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 15.47/2.48      | k2_funct_1(X0) = X1
% 15.47/2.48      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 15.47/2.48      inference(cnf_transformation,[],[f90]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1190,plain,
% 15.47/2.48      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 15.47/2.48      | k2_funct_1(X1) = X0
% 15.47/2.48      | k1_relat_1(X1) != k2_relat_1(X0)
% 15.47/2.48      | v2_funct_1(X1) != iProver_top
% 15.47/2.48      | v1_funct_1(X1) != iProver_top
% 15.47/2.48      | v1_funct_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(X1) != iProver_top
% 15.47/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_8065,plain,
% 15.47/2.48      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 15.47/2.48      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 15.47/2.48      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 15.47/2.48      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 15.47/2.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_8063,c_1190]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1176,plain,
% 15.47/2.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_11,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f59]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1188,plain,
% 15.47/2.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.47/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2295,plain,
% 15.47/2.48      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1176,c_1188]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2298,plain,
% 15.47/2.48      ( k2_relat_1(sK3) = sK0 ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_2295,c_2052]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_8066,plain,
% 15.47/2.48      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 15.47/2.48      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 15.47/2.48      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 15.47/2.48      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 15.47/2.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_8065,c_2298]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_10,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | v1_relat_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f58]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1333,plain,
% 15.47/2.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.47/2.48      | v1_relat_1(sK3) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_10]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1710,plain,
% 15.47/2.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.47/2.48      | v1_relat_1(sK3) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_1333]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1711,plain,
% 15.47/2.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_1710]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_4,plain,
% 15.47/2.48      ( ~ v1_funct_1(X0)
% 15.47/2.48      | v1_funct_1(k2_funct_1(X0))
% 15.47/2.48      | ~ v1_relat_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f53]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1960,plain,
% 15.47/2.48      ( v1_funct_1(k2_funct_1(sK3))
% 15.47/2.48      | ~ v1_funct_1(sK3)
% 15.47/2.48      | ~ v1_relat_1(sK3) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_4]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1961,plain,
% 15.47/2.48      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_1960]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5,plain,
% 15.47/2.48      ( ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_relat_1(X0)
% 15.47/2.48      | v1_relat_1(k2_funct_1(X0)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f52]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2966,plain,
% 15.47/2.48      ( ~ v1_funct_1(sK3)
% 15.47/2.48      | v1_relat_1(k2_funct_1(sK3))
% 15.47/2.48      | ~ v1_relat_1(sK3) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_5]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2967,plain,
% 15.47/2.48      ( v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_2966]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_42554,plain,
% 15.47/2.48      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 15.47/2.48      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 15.47/2.48      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 15.47/2.48      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_8066,c_40,c_42,c_1711,c_1961,c_2967]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1173,plain,
% 15.47/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2296,plain,
% 15.47/2.48      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1173,c_1188]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2297,plain,
% 15.47/2.48      ( k2_relat_1(sK2) = sK1 ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_2296,c_30]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1189,plain,
% 15.47/2.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.47/2.48      | v1_relat_1(X0) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2254,plain,
% 15.47/2.48      ( v1_relat_1(sK2) = iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1173,c_1189]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1171,plain,
% 15.47/2.48      ( v1_funct_1(sK2) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1194,plain,
% 15.47/2.48      ( v1_funct_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_0,plain,
% 15.47/2.48      ( ~ v1_relat_1(X0)
% 15.47/2.48      | ~ v1_relat_1(X1)
% 15.47/2.48      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 15.47/2.48      inference(cnf_transformation,[],[f48]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1197,plain,
% 15.47/2.48      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 15.47/2.48      | v1_relat_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(X1) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3053,plain,
% 15.47/2.48      ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
% 15.47/2.48      | v1_funct_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(X1) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1194,c_1197]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9566,plain,
% 15.47/2.48      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2)))
% 15.47/2.48      | v1_relat_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(sK2) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1171,c_3053]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_28,negated_conjecture,
% 15.47/2.48      ( v2_funct_1(sK2) ),
% 15.47/2.48      inference(cnf_transformation,[],[f82]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1177,plain,
% 15.47/2.48      ( v2_funct_1(sK2) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_8,plain,
% 15.47/2.48      ( ~ v2_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_relat_1(X0)
% 15.47/2.48      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 15.47/2.48      inference(cnf_transformation,[],[f56]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1191,plain,
% 15.47/2.48      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 15.47/2.48      | v2_funct_1(X0) != iProver_top
% 15.47/2.48      | v1_funct_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3089,plain,
% 15.47/2.48      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top
% 15.47/2.48      | v1_relat_1(sK2) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1177,c_1191]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1974,plain,
% 15.47/2.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.47/2.48      | v1_relat_1(sK2) ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_10]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1975,plain,
% 15.47/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.47/2.48      | v1_relat_1(sK2) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3140,plain,
% 15.47/2.48      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_3089,c_37,c_39,c_1975]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9570,plain,
% 15.47/2.48      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(sK2,k2_relat_1(X0))
% 15.47/2.48      | v1_relat_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(sK2) != iProver_top ),
% 15.47/2.48      inference(demodulation,[status(thm)],[c_9566,c_3140]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9673,plain,
% 15.47/2.48      ( v1_relat_1(X0) != iProver_top
% 15.47/2.48      | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(sK2,k2_relat_1(X0)) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_9570,c_39,c_1975]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9674,plain,
% 15.47/2.48      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(sK2,k2_relat_1(X0))
% 15.47/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_9673]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9682,plain,
% 15.47/2.48      ( k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_2254,c_9674]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1,plain,
% 15.47/2.48      ( ~ v1_relat_1(X0)
% 15.47/2.48      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f49]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1196,plain,
% 15.47/2.48      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 15.47/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2358,plain,
% 15.47/2.48      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_2254,c_1196]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2359,plain,
% 15.47/2.48      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_2358,c_2297]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3046,plain,
% 15.47/2.48      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 15.47/2.48      | sK1 = k1_xboole_0
% 15.47/2.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.47/2.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.47/2.48      | v2_funct_1(sK2) != iProver_top
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_30,c_1178]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_26,negated_conjecture,
% 15.47/2.48      ( k1_xboole_0 != sK1 ),
% 15.47/2.48      inference(cnf_transformation,[],[f84]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1245,plain,
% 15.47/2.48      ( ~ v1_funct_2(X0,X1,sK1)
% 15.47/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 15.47/2.48      | ~ v2_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | k2_relset_1(X1,sK1,X0) != sK1
% 15.47/2.48      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 15.47/2.48      | k1_xboole_0 = sK1 ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_24]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1370,plain,
% 15.47/2.48      ( ~ v1_funct_2(sK2,X0,sK1)
% 15.47/2.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 15.47/2.48      | ~ v2_funct_1(sK2)
% 15.47/2.48      | ~ v1_funct_1(sK2)
% 15.47/2.48      | k2_relset_1(X0,sK1,sK2) != sK1
% 15.47/2.48      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 15.47/2.48      | k1_xboole_0 = sK1 ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_1245]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1587,plain,
% 15.47/2.48      ( ~ v1_funct_2(sK2,sK0,sK1)
% 15.47/2.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.47/2.48      | ~ v2_funct_1(sK2)
% 15.47/2.48      | ~ v1_funct_1(sK2)
% 15.47/2.48      | k2_relset_1(sK0,sK1,sK2) != sK1
% 15.47/2.48      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 15.47/2.48      | k1_xboole_0 = sK1 ),
% 15.47/2.48      inference(instantiation,[status(thm)],[c_1370]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3097,plain,
% 15.47/2.48      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_3046,c_36,c_35,c_34,c_30,c_28,c_26,c_1587]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9689,plain,
% 15.47/2.48      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 15.47/2.48      inference(light_normalisation,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_9682,c_2297,c_2359,c_3097]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2,plain,
% 15.47/2.48      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 15.47/2.48      inference(cnf_transformation,[],[f86]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9690,plain,
% 15.47/2.48      ( k1_relat_1(sK2) = sK0 ),
% 15.47/2.48      inference(demodulation,[status(thm)],[c_9689,c_2]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2253,plain,
% 15.47/2.48      ( v1_relat_1(sK3) = iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1176,c_1189]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1174,plain,
% 15.47/2.48      ( v1_funct_1(sK3) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9565,plain,
% 15.47/2.48      ( k9_relat_1(k2_funct_1(sK3),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3)))
% 15.47/2.48      | v1_relat_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1174,c_3053]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5518,plain,
% 15.47/2.48      ( v2_funct_1(sK3) = iProver_top ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_5412,c_40,c_41,c_42,c_27,c_700,c_1281,c_2964]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5522,plain,
% 15.47/2.48      ( k9_relat_1(k2_funct_1(sK3),X0) = k10_relat_1(sK3,X0)
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_5518,c_1191]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5609,plain,
% 15.47/2.48      ( k9_relat_1(k2_funct_1(sK3),X0) = k10_relat_1(sK3,X0) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_5522,c_40,c_42,c_1711]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9571,plain,
% 15.47/2.48      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k10_relat_1(sK3,k2_relat_1(X0))
% 15.47/2.48      | v1_relat_1(X0) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top ),
% 15.47/2.48      inference(demodulation,[status(thm)],[c_9565,c_5609]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9760,plain,
% 15.47/2.48      ( v1_relat_1(X0) != iProver_top
% 15.47/2.48      | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k10_relat_1(sK3,k2_relat_1(X0)) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_9571,c_42,c_1711]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9761,plain,
% 15.47/2.48      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k10_relat_1(sK3,k2_relat_1(X0))
% 15.47/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_9760]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9768,plain,
% 15.47/2.48      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k10_relat_1(sK3,k2_relat_1(sK3)) ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_2253,c_9761]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2355,plain,
% 15.47/2.48      ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_2253,c_1196]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_2356,plain,
% 15.47/2.48      ( k10_relat_1(sK3,sK0) = k1_relat_1(sK3) ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_2355,c_2298]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9777,plain,
% 15.47/2.48      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 15.47/2.48      inference(light_normalisation,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_9768,c_2298,c_2356,c_8063]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9778,plain,
% 15.47/2.48      ( k1_relat_1(sK3) = sK1 ),
% 15.47/2.48      inference(demodulation,[status(thm)],[c_9777,c_2]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_17,plain,
% 15.47/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.47/2.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.47/2.48      | ~ v1_funct_1(X0)
% 15.47/2.48      | ~ v1_funct_1(X3)
% 15.47/2.48      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.47/2.48      inference(cnf_transformation,[],[f65]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_1184,plain,
% 15.47/2.48      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.47/2.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.47/2.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.47/2.48      | v1_funct_1(X5) != iProver_top
% 15.47/2.48      | v1_funct_1(X4) != iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_3511,plain,
% 15.47/2.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.47/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.47/2.48      | v1_funct_1(X2) != iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1176,c_1184]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_4385,plain,
% 15.47/2.48      ( v1_funct_1(X2) != iProver_top
% 15.47/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.47/2.48      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_3511,c_40]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_4386,plain,
% 15.47/2.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.47/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.47/2.48      | v1_funct_1(X2) != iProver_top ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_4385]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_4393,plain,
% 15.47/2.48      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_1173,c_4386]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_4394,plain,
% 15.47/2.48      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_4393,c_2045]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_4831,plain,
% 15.47/2.48      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_4394,c_37]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5053,plain,
% 15.47/2.48      ( k2_funct_1(sK3) = sK2
% 15.47/2.48      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 15.47/2.48      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 15.47/2.48      | v2_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top
% 15.47/2.48      | v1_relat_1(sK2) != iProver_top ),
% 15.47/2.48      inference(superposition,[status(thm)],[c_4831,c_1190]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5054,plain,
% 15.47/2.48      ( k2_funct_1(sK3) = sK2
% 15.47/2.48      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 15.47/2.48      | k1_relat_1(sK3) != sK1
% 15.47/2.48      | v2_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top
% 15.47/2.48      | v1_relat_1(sK2) != iProver_top ),
% 15.47/2.48      inference(light_normalisation,[status(thm)],[c_5053,c_2297,c_2298]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_5055,plain,
% 15.47/2.48      ( k2_funct_1(sK3) = sK2
% 15.47/2.48      | k1_relat_1(sK3) != sK1
% 15.47/2.48      | v2_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_funct_1(sK3) != iProver_top
% 15.47/2.48      | v1_funct_1(sK2) != iProver_top
% 15.47/2.48      | v1_relat_1(sK3) != iProver_top
% 15.47/2.48      | v1_relat_1(sK2) != iProver_top ),
% 15.47/2.48      inference(equality_resolution_simp,[status(thm)],[c_5054]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_7423,plain,
% 15.47/2.48      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 15.47/2.48      inference(global_propositional_subsumption,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_5055,c_37,c_39,c_40,c_41,c_42,c_27,c_700,c_1281,
% 15.47/2.48                 c_1711,c_1975,c_2964,c_5412]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_7424,plain,
% 15.47/2.48      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 15.47/2.48      inference(renaming,[status(thm)],[c_7423]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9904,plain,
% 15.47/2.48      ( k2_funct_1(sK3) = sK2 | sK1 != sK1 ),
% 15.47/2.48      inference(demodulation,[status(thm)],[c_9778,c_7424]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_9906,plain,
% 15.47/2.48      ( k2_funct_1(sK3) = sK2 ),
% 15.47/2.48      inference(equality_resolution_simp,[status(thm)],[c_9904]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_42558,plain,
% 15.47/2.48      ( k2_funct_1(sK2) = sK3
% 15.47/2.48      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 15.47/2.48      | sK0 != sK0
% 15.47/2.48      | v2_funct_1(sK2) != iProver_top ),
% 15.47/2.48      inference(light_normalisation,
% 15.47/2.48                [status(thm)],
% 15.47/2.48                [c_42554,c_2297,c_9690,c_9906]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_42559,plain,
% 15.47/2.48      ( k2_funct_1(sK2) = sK3 | v2_funct_1(sK2) != iProver_top ),
% 15.47/2.48      inference(equality_resolution_simp,[status(thm)],[c_42558]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_25,negated_conjecture,
% 15.47/2.48      ( k2_funct_1(sK2) != sK3 ),
% 15.47/2.48      inference(cnf_transformation,[],[f85]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(c_44,plain,
% 15.47/2.48      ( v2_funct_1(sK2) = iProver_top ),
% 15.47/2.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.47/2.48  
% 15.47/2.48  cnf(contradiction,plain,
% 15.47/2.48      ( $false ),
% 15.47/2.48      inference(minisat,[status(thm)],[c_42559,c_25,c_44]) ).
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.47/2.48  
% 15.47/2.48  ------                               Statistics
% 15.47/2.48  
% 15.47/2.48  ------ General
% 15.47/2.48  
% 15.47/2.48  abstr_ref_over_cycles:                  0
% 15.47/2.48  abstr_ref_under_cycles:                 0
% 15.47/2.48  gc_basic_clause_elim:                   0
% 15.47/2.48  forced_gc_time:                         0
% 15.47/2.48  parsing_time:                           0.013
% 15.47/2.48  unif_index_cands_time:                  0.
% 15.47/2.48  unif_index_add_time:                    0.
% 15.47/2.48  orderings_time:                         0.
% 15.47/2.48  out_proof_time:                         0.02
% 15.47/2.48  total_time:                             1.744
% 15.47/2.48  num_of_symbols:                         53
% 15.47/2.48  num_of_terms:                           66212
% 15.47/2.48  
% 15.47/2.48  ------ Preprocessing
% 15.47/2.48  
% 15.47/2.48  num_of_splits:                          0
% 15.47/2.48  num_of_split_atoms:                     0
% 15.47/2.48  num_of_reused_defs:                     0
% 15.47/2.48  num_eq_ax_congr_red:                    3
% 15.47/2.48  num_of_sem_filtered_clauses:            1
% 15.47/2.48  num_of_subtypes:                        0
% 15.47/2.48  monotx_restored_types:                  0
% 15.47/2.48  sat_num_of_epr_types:                   0
% 15.47/2.48  sat_num_of_non_cyclic_types:            0
% 15.47/2.48  sat_guarded_non_collapsed_types:        0
% 15.47/2.48  num_pure_diseq_elim:                    0
% 15.47/2.48  simp_replaced_by:                       0
% 15.47/2.48  res_preprocessed:                       182
% 15.47/2.48  prep_upred:                             0
% 15.47/2.48  prep_unflattend:                        12
% 15.47/2.48  smt_new_axioms:                         0
% 15.47/2.48  pred_elim_cands:                        5
% 15.47/2.48  pred_elim:                              1
% 15.47/2.48  pred_elim_cl:                           1
% 15.47/2.48  pred_elim_cycles:                       3
% 15.47/2.48  merged_defs:                            0
% 15.47/2.48  merged_defs_ncl:                        0
% 15.47/2.48  bin_hyper_res:                          0
% 15.47/2.48  prep_cycles:                            4
% 15.47/2.48  pred_elim_time:                         0.005
% 15.47/2.48  splitting_time:                         0.
% 15.47/2.48  sem_filter_time:                        0.
% 15.47/2.48  monotx_time:                            0.002
% 15.47/2.48  subtype_inf_time:                       0.
% 15.47/2.48  
% 15.47/2.48  ------ Problem properties
% 15.47/2.48  
% 15.47/2.48  clauses:                                36
% 15.47/2.48  conjectures:                            11
% 15.47/2.48  epr:                                    7
% 15.47/2.48  horn:                                   32
% 15.47/2.48  ground:                                 12
% 15.47/2.48  unary:                                  16
% 15.47/2.48  binary:                                 4
% 15.47/2.48  lits:                                   128
% 15.47/2.48  lits_eq:                                31
% 15.47/2.48  fd_pure:                                0
% 15.47/2.48  fd_pseudo:                              0
% 15.47/2.48  fd_cond:                                4
% 15.47/2.48  fd_pseudo_cond:                         1
% 15.47/2.48  ac_symbols:                             0
% 15.47/2.48  
% 15.47/2.48  ------ Propositional Solver
% 15.47/2.48  
% 15.47/2.48  prop_solver_calls:                      42
% 15.47/2.48  prop_fast_solver_calls:                 3324
% 15.47/2.48  smt_solver_calls:                       0
% 15.47/2.48  smt_fast_solver_calls:                  0
% 15.47/2.48  prop_num_of_clauses:                    22184
% 15.47/2.48  prop_preprocess_simplified:             34583
% 15.47/2.48  prop_fo_subsumed:                       557
% 15.47/2.48  prop_solver_time:                       0.
% 15.47/2.48  smt_solver_time:                        0.
% 15.47/2.48  smt_fast_solver_time:                   0.
% 15.47/2.48  prop_fast_solver_time:                  0.
% 15.47/2.48  prop_unsat_core_time:                   0.003
% 15.47/2.48  
% 15.47/2.48  ------ QBF
% 15.47/2.48  
% 15.47/2.48  qbf_q_res:                              0
% 15.47/2.48  qbf_num_tautologies:                    0
% 15.47/2.48  qbf_prep_cycles:                        0
% 15.47/2.48  
% 15.47/2.48  ------ BMC1
% 15.47/2.48  
% 15.47/2.48  bmc1_current_bound:                     -1
% 15.47/2.48  bmc1_last_solved_bound:                 -1
% 15.47/2.48  bmc1_unsat_core_size:                   -1
% 15.47/2.48  bmc1_unsat_core_parents_size:           -1
% 15.47/2.48  bmc1_merge_next_fun:                    0
% 15.47/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.47/2.48  
% 15.47/2.48  ------ Instantiation
% 15.47/2.48  
% 15.47/2.48  inst_num_of_clauses:                    410
% 15.47/2.48  inst_num_in_passive:                    79
% 15.47/2.48  inst_num_in_active:                     2892
% 15.47/2.48  inst_num_in_unprocessed:                155
% 15.47/2.48  inst_num_of_loops:                      3179
% 15.47/2.48  inst_num_of_learning_restarts:          1
% 15.47/2.48  inst_num_moves_active_passive:          281
% 15.47/2.48  inst_lit_activity:                      0
% 15.47/2.48  inst_lit_activity_moves:                4
% 15.47/2.48  inst_num_tautologies:                   0
% 15.47/2.48  inst_num_prop_implied:                  0
% 15.47/2.48  inst_num_existing_simplified:           0
% 15.47/2.48  inst_num_eq_res_simplified:             0
% 15.47/2.48  inst_num_child_elim:                    0
% 15.47/2.48  inst_num_of_dismatching_blockings:      1250
% 15.47/2.48  inst_num_of_non_proper_insts:           4269
% 15.47/2.48  inst_num_of_duplicates:                 0
% 15.47/2.48  inst_inst_num_from_inst_to_res:         0
% 15.47/2.48  inst_dismatching_checking_time:         0.
% 15.47/2.48  
% 15.47/2.48  ------ Resolution
% 15.47/2.48  
% 15.47/2.48  res_num_of_clauses:                     54
% 15.47/2.48  res_num_in_passive:                     54
% 15.47/2.48  res_num_in_active:                      0
% 15.47/2.48  res_num_of_loops:                       186
% 15.47/2.48  res_forward_subset_subsumed:            273
% 15.47/2.48  res_backward_subset_subsumed:           0
% 15.47/2.48  res_forward_subsumed:                   0
% 15.47/2.48  res_backward_subsumed:                  0
% 15.47/2.48  res_forward_subsumption_resolution:     2
% 15.47/2.48  res_backward_subsumption_resolution:    0
% 15.47/2.48  res_clause_to_clause_subsumption:       5941
% 15.47/2.48  res_orphan_elimination:                 0
% 15.47/2.48  res_tautology_del:                      186
% 15.47/2.48  res_num_eq_res_simplified:              1
% 15.47/2.48  res_num_sel_changes:                    0
% 15.47/2.48  res_moves_from_active_to_pass:          0
% 15.47/2.48  
% 15.47/2.48  ------ Superposition
% 15.47/2.48  
% 15.47/2.48  sup_time_total:                         0.
% 15.47/2.48  sup_time_generating:                    0.
% 15.47/2.48  sup_time_sim_full:                      0.
% 15.47/2.48  sup_time_sim_immed:                     0.
% 15.47/2.48  
% 15.47/2.48  sup_num_of_clauses:                     2223
% 15.47/2.48  sup_num_in_active:                      614
% 15.47/2.48  sup_num_in_passive:                     1609
% 15.47/2.48  sup_num_of_loops:                       635
% 15.47/2.48  sup_fw_superposition:                   1292
% 15.47/2.48  sup_bw_superposition:                   1081
% 15.47/2.48  sup_immediate_simplified:               760
% 15.47/2.48  sup_given_eliminated:                   0
% 15.47/2.48  comparisons_done:                       0
% 15.47/2.48  comparisons_avoided:                    4
% 15.47/2.48  
% 15.47/2.48  ------ Simplifications
% 15.47/2.48  
% 15.47/2.48  
% 15.47/2.48  sim_fw_subset_subsumed:                 15
% 15.47/2.48  sim_bw_subset_subsumed:                 67
% 15.47/2.48  sim_fw_subsumed:                        9
% 15.47/2.48  sim_bw_subsumed:                        0
% 15.47/2.48  sim_fw_subsumption_res:                 0
% 15.47/2.48  sim_bw_subsumption_res:                 0
% 15.47/2.48  sim_tautology_del:                      0
% 15.47/2.48  sim_eq_tautology_del:                   88
% 15.47/2.48  sim_eq_res_simp:                        3
% 15.47/2.48  sim_fw_demodulated:                     94
% 15.47/2.48  sim_bw_demodulated:                     9
% 15.47/2.48  sim_light_normalised:                   761
% 15.47/2.48  sim_joinable_taut:                      0
% 15.47/2.48  sim_joinable_simp:                      0
% 15.47/2.48  sim_ac_normalised:                      0
% 15.47/2.48  sim_smt_subsumption:                    0
% 15.47/2.48  
%------------------------------------------------------------------------------
