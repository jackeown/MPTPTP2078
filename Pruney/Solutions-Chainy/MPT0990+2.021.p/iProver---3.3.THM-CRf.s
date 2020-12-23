%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:00 EST 2020

% Result     : Theorem 24.12s
% Output     : CNFRefutation 24.12s
% Verified   : 
% Statistics : Number of formulae       :  221 (5441 expanded)
%              Number of clauses        :  137 (1571 expanded)
%              Number of leaves         :   23 (1429 expanded)
%              Depth                    :   27
%              Number of atoms          :  893 (47545 expanded)
%              Number of equality atoms :  450 (17640 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f47,f46])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f72,plain,(
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

fof(f77,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f54,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f86,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f13,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1790,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1772,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1775,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1787,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3418,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1787])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4116,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_41])).

cnf(c_4117,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4116])).

cnf(c_4125,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_4117])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4317,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4125,c_38])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1776,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4319,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4317,c_1776])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1789,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4321,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4317,c_1789])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6070,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4321,c_38,c_40,c_41,c_43])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1791,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6080,plain,
    ( k5_relat_1(sK2,sK3) = X0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6070,c_1791])).

cnf(c_8502,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4319,c_6080])).

cnf(c_8524,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(superposition,[status(thm)],[c_1790,c_8502])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1782,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5743,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_1782])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5781,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5743,c_38,c_39,c_40])).

cnf(c_5782,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5781])).

cnf(c_5785,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4317,c_5782])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1231,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1266,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_1232,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1896,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1897,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_5877,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5785,c_41,c_42,c_43,c_28,c_1266,c_1897])).

cnf(c_8618,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8524,c_5877])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4980,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4981,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4980])).

cnf(c_8642,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8618,c_4981])).

cnf(c_1773,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1795,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2821,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_1795])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1910,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2196,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_2197,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2196])).

cnf(c_3211,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2821,c_43,c_2197])).

cnf(c_8647,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_8642,c_3211])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1794,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8938,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8647,c_1794])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | v2_funct_2(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1785,plain,
    ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v2_funct_2(X3,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4863,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v2_funct_2(sK3,sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4317,c_1785])).

cnf(c_6915,plain,
    ( v2_funct_2(sK3,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4863,c_38,c_39,c_40,c_41,c_42,c_43,c_4319])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_13,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_363,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_375,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_7])).

cnf(c_1769,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_2715,plain,
    ( k2_relat_1(sK3) = sK0
    | v2_funct_2(sK3,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1769])).

cnf(c_6919,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(superposition,[status(thm)],[c_6915,c_2715])).

cnf(c_8939,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8938,c_6919])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_45,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2496,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2497,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2496])).

cnf(c_8624,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8524,c_1794])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1779,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4756,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_1779])).

cnf(c_1770,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1796,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2827,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_1796])).

cnf(c_3302,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2827,c_40,c_45,c_2497])).

cnf(c_4757,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4756,c_3302])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1871,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1872,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_4984,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4757,c_38,c_39,c_40,c_45,c_27,c_1266,c_1872])).

cnf(c_0,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4999,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4984,c_0])).

cnf(c_5001,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_4999,c_0])).

cnf(c_8625,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8624,c_5001,c_6919])).

cnf(c_8626,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8625])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1786,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4868,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4317,c_1786])).

cnf(c_2850,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
    | ~ v1_funct_2(X0,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3310,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_8161,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4868,c_37,c_36,c_35,c_34,c_33,c_32,c_30,c_3310])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1778,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8166,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8161,c_1778])).

cnf(c_21439,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8166,c_41,c_42,c_43,c_28,c_1266,c_1897,c_4981,c_8618])).

cnf(c_21441,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_21439,c_8647])).

cnf(c_21466,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_21441,c_0])).

cnf(c_21468,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_21466,c_0])).

cnf(c_1236,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_50815,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_50875,plain,
    ( v2_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_50815])).

cnf(c_63645,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_50875])).

cnf(c_63646,plain,
    ( k2_funct_1(sK3) != sK2
    | v2_funct_1(k2_funct_1(sK3)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63645])).

cnf(c_1237,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_56768,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_64552,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_56768])).

cnf(c_64553,plain,
    ( k2_funct_1(sK3) != sK2
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64552])).

cnf(c_77666,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8939,c_38,c_40,c_41,c_43,c_45,c_2197,c_2497,c_4981,c_8618,c_8626,c_21468,c_63646,c_64553])).

cnf(c_3335,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_1778])).

cnf(c_2822,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_1795])).

cnf(c_3216,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2822,c_40,c_45,c_2497])).

cnf(c_3336,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3335,c_3216])).

cnf(c_4929,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3336,c_38,c_39,c_40,c_45,c_27,c_1266,c_1872])).

cnf(c_4938,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4929,c_0])).

cnf(c_4940,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_4938,c_0])).

cnf(c_74051,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8626,c_38,c_40,c_41,c_43,c_2197,c_2497,c_4981,c_8618,c_21468])).

cnf(c_77670,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_77666,c_4940,c_5001,c_21468,c_74051])).

cnf(c_77671,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_77670])).

cnf(c_26,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_77671,c_26,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 24.12/3.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.12/3.52  
% 24.12/3.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 24.12/3.52  
% 24.12/3.52  ------  iProver source info
% 24.12/3.52  
% 24.12/3.52  git: date: 2020-06-30 10:37:57 +0100
% 24.12/3.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 24.12/3.52  git: non_committed_changes: false
% 24.12/3.52  git: last_make_outside_of_git: false
% 24.12/3.52  
% 24.12/3.52  ------ 
% 24.12/3.52  
% 24.12/3.52  ------ Input Options
% 24.12/3.52  
% 24.12/3.52  --out_options                           all
% 24.12/3.52  --tptp_safe_out                         true
% 24.12/3.52  --problem_path                          ""
% 24.12/3.52  --include_path                          ""
% 24.12/3.52  --clausifier                            res/vclausify_rel
% 24.12/3.52  --clausifier_options                    ""
% 24.12/3.52  --stdin                                 false
% 24.12/3.52  --stats_out                             all
% 24.12/3.52  
% 24.12/3.52  ------ General Options
% 24.12/3.52  
% 24.12/3.52  --fof                                   false
% 24.12/3.52  --time_out_real                         305.
% 24.12/3.52  --time_out_virtual                      -1.
% 24.12/3.52  --symbol_type_check                     false
% 24.12/3.52  --clausify_out                          false
% 24.12/3.52  --sig_cnt_out                           false
% 24.12/3.52  --trig_cnt_out                          false
% 24.12/3.52  --trig_cnt_out_tolerance                1.
% 24.12/3.52  --trig_cnt_out_sk_spl                   false
% 24.12/3.52  --abstr_cl_out                          false
% 24.12/3.52  
% 24.12/3.52  ------ Global Options
% 24.12/3.52  
% 24.12/3.52  --schedule                              default
% 24.12/3.52  --add_important_lit                     false
% 24.12/3.52  --prop_solver_per_cl                    1000
% 24.12/3.52  --min_unsat_core                        false
% 24.12/3.52  --soft_assumptions                      false
% 24.12/3.52  --soft_lemma_size                       3
% 24.12/3.52  --prop_impl_unit_size                   0
% 24.12/3.52  --prop_impl_unit                        []
% 24.12/3.52  --share_sel_clauses                     true
% 24.12/3.52  --reset_solvers                         false
% 24.12/3.52  --bc_imp_inh                            [conj_cone]
% 24.12/3.52  --conj_cone_tolerance                   3.
% 24.12/3.52  --extra_neg_conj                        none
% 24.12/3.52  --large_theory_mode                     true
% 24.12/3.52  --prolific_symb_bound                   200
% 24.12/3.52  --lt_threshold                          2000
% 24.12/3.52  --clause_weak_htbl                      true
% 24.12/3.52  --gc_record_bc_elim                     false
% 24.12/3.52  
% 24.12/3.52  ------ Preprocessing Options
% 24.12/3.52  
% 24.12/3.52  --preprocessing_flag                    true
% 24.12/3.52  --time_out_prep_mult                    0.1
% 24.12/3.52  --splitting_mode                        input
% 24.12/3.52  --splitting_grd                         true
% 24.12/3.52  --splitting_cvd                         false
% 24.12/3.52  --splitting_cvd_svl                     false
% 24.12/3.52  --splitting_nvd                         32
% 24.12/3.52  --sub_typing                            true
% 24.12/3.52  --prep_gs_sim                           true
% 24.12/3.52  --prep_unflatten                        true
% 24.12/3.52  --prep_res_sim                          true
% 24.12/3.52  --prep_upred                            true
% 24.12/3.52  --prep_sem_filter                       exhaustive
% 24.12/3.52  --prep_sem_filter_out                   false
% 24.12/3.52  --pred_elim                             true
% 24.12/3.52  --res_sim_input                         true
% 24.12/3.52  --eq_ax_congr_red                       true
% 24.12/3.52  --pure_diseq_elim                       true
% 24.12/3.52  --brand_transform                       false
% 24.12/3.52  --non_eq_to_eq                          false
% 24.12/3.52  --prep_def_merge                        true
% 24.12/3.52  --prep_def_merge_prop_impl              false
% 24.12/3.52  --prep_def_merge_mbd                    true
% 24.12/3.52  --prep_def_merge_tr_red                 false
% 24.12/3.52  --prep_def_merge_tr_cl                  false
% 24.12/3.52  --smt_preprocessing                     true
% 24.12/3.52  --smt_ac_axioms                         fast
% 24.12/3.52  --preprocessed_out                      false
% 24.12/3.52  --preprocessed_stats                    false
% 24.12/3.52  
% 24.12/3.52  ------ Abstraction refinement Options
% 24.12/3.52  
% 24.12/3.52  --abstr_ref                             []
% 24.12/3.52  --abstr_ref_prep                        false
% 24.12/3.52  --abstr_ref_until_sat                   false
% 24.12/3.52  --abstr_ref_sig_restrict                funpre
% 24.12/3.52  --abstr_ref_af_restrict_to_split_sk     false
% 24.12/3.52  --abstr_ref_under                       []
% 24.12/3.52  
% 24.12/3.52  ------ SAT Options
% 24.12/3.52  
% 24.12/3.52  --sat_mode                              false
% 24.12/3.52  --sat_fm_restart_options                ""
% 24.12/3.52  --sat_gr_def                            false
% 24.12/3.52  --sat_epr_types                         true
% 24.12/3.52  --sat_non_cyclic_types                  false
% 24.12/3.52  --sat_finite_models                     false
% 24.12/3.52  --sat_fm_lemmas                         false
% 24.12/3.52  --sat_fm_prep                           false
% 24.12/3.52  --sat_fm_uc_incr                        true
% 24.12/3.52  --sat_out_model                         small
% 24.12/3.52  --sat_out_clauses                       false
% 24.12/3.52  
% 24.12/3.52  ------ QBF Options
% 24.12/3.52  
% 24.12/3.52  --qbf_mode                              false
% 24.12/3.52  --qbf_elim_univ                         false
% 24.12/3.52  --qbf_dom_inst                          none
% 24.12/3.52  --qbf_dom_pre_inst                      false
% 24.12/3.52  --qbf_sk_in                             false
% 24.12/3.52  --qbf_pred_elim                         true
% 24.12/3.52  --qbf_split                             512
% 24.12/3.52  
% 24.12/3.52  ------ BMC1 Options
% 24.12/3.52  
% 24.12/3.52  --bmc1_incremental                      false
% 24.12/3.52  --bmc1_axioms                           reachable_all
% 24.12/3.52  --bmc1_min_bound                        0
% 24.12/3.52  --bmc1_max_bound                        -1
% 24.12/3.52  --bmc1_max_bound_default                -1
% 24.12/3.52  --bmc1_symbol_reachability              true
% 24.12/3.52  --bmc1_property_lemmas                  false
% 24.12/3.52  --bmc1_k_induction                      false
% 24.12/3.52  --bmc1_non_equiv_states                 false
% 24.12/3.52  --bmc1_deadlock                         false
% 24.12/3.52  --bmc1_ucm                              false
% 24.12/3.52  --bmc1_add_unsat_core                   none
% 24.12/3.52  --bmc1_unsat_core_children              false
% 24.12/3.52  --bmc1_unsat_core_extrapolate_axioms    false
% 24.12/3.52  --bmc1_out_stat                         full
% 24.12/3.52  --bmc1_ground_init                      false
% 24.12/3.52  --bmc1_pre_inst_next_state              false
% 24.12/3.52  --bmc1_pre_inst_state                   false
% 24.12/3.52  --bmc1_pre_inst_reach_state             false
% 24.12/3.52  --bmc1_out_unsat_core                   false
% 24.12/3.52  --bmc1_aig_witness_out                  false
% 24.12/3.52  --bmc1_verbose                          false
% 24.12/3.52  --bmc1_dump_clauses_tptp                false
% 24.12/3.52  --bmc1_dump_unsat_core_tptp             false
% 24.12/3.52  --bmc1_dump_file                        -
% 24.12/3.52  --bmc1_ucm_expand_uc_limit              128
% 24.12/3.52  --bmc1_ucm_n_expand_iterations          6
% 24.12/3.52  --bmc1_ucm_extend_mode                  1
% 24.12/3.52  --bmc1_ucm_init_mode                    2
% 24.12/3.52  --bmc1_ucm_cone_mode                    none
% 24.12/3.52  --bmc1_ucm_reduced_relation_type        0
% 24.12/3.52  --bmc1_ucm_relax_model                  4
% 24.12/3.52  --bmc1_ucm_full_tr_after_sat            true
% 24.12/3.52  --bmc1_ucm_expand_neg_assumptions       false
% 24.12/3.52  --bmc1_ucm_layered_model                none
% 24.12/3.52  --bmc1_ucm_max_lemma_size               10
% 24.12/3.52  
% 24.12/3.52  ------ AIG Options
% 24.12/3.52  
% 24.12/3.52  --aig_mode                              false
% 24.12/3.52  
% 24.12/3.52  ------ Instantiation Options
% 24.12/3.52  
% 24.12/3.52  --instantiation_flag                    true
% 24.12/3.52  --inst_sos_flag                         true
% 24.12/3.52  --inst_sos_phase                        true
% 24.12/3.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 24.12/3.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 24.12/3.52  --inst_lit_sel_side                     num_symb
% 24.12/3.52  --inst_solver_per_active                1400
% 24.12/3.52  --inst_solver_calls_frac                1.
% 24.12/3.52  --inst_passive_queue_type               priority_queues
% 24.12/3.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 24.12/3.52  --inst_passive_queues_freq              [25;2]
% 24.12/3.52  --inst_dismatching                      true
% 24.12/3.52  --inst_eager_unprocessed_to_passive     true
% 24.12/3.52  --inst_prop_sim_given                   true
% 24.12/3.52  --inst_prop_sim_new                     false
% 24.12/3.52  --inst_subs_new                         false
% 24.12/3.52  --inst_eq_res_simp                      false
% 24.12/3.52  --inst_subs_given                       false
% 24.12/3.52  --inst_orphan_elimination               true
% 24.12/3.52  --inst_learning_loop_flag               true
% 24.12/3.52  --inst_learning_start                   3000
% 24.12/3.52  --inst_learning_factor                  2
% 24.12/3.52  --inst_start_prop_sim_after_learn       3
% 24.12/3.52  --inst_sel_renew                        solver
% 24.12/3.52  --inst_lit_activity_flag                true
% 24.12/3.52  --inst_restr_to_given                   false
% 24.12/3.52  --inst_activity_threshold               500
% 24.12/3.52  --inst_out_proof                        true
% 24.12/3.52  
% 24.12/3.52  ------ Resolution Options
% 24.12/3.52  
% 24.12/3.52  --resolution_flag                       true
% 24.12/3.52  --res_lit_sel                           adaptive
% 24.12/3.52  --res_lit_sel_side                      none
% 24.12/3.52  --res_ordering                          kbo
% 24.12/3.52  --res_to_prop_solver                    active
% 24.12/3.52  --res_prop_simpl_new                    false
% 24.12/3.52  --res_prop_simpl_given                  true
% 24.12/3.52  --res_passive_queue_type                priority_queues
% 24.12/3.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 24.12/3.52  --res_passive_queues_freq               [15;5]
% 24.12/3.52  --res_forward_subs                      full
% 24.12/3.52  --res_backward_subs                     full
% 24.12/3.52  --res_forward_subs_resolution           true
% 24.12/3.52  --res_backward_subs_resolution          true
% 24.12/3.52  --res_orphan_elimination                true
% 24.12/3.52  --res_time_limit                        2.
% 24.12/3.52  --res_out_proof                         true
% 24.12/3.52  
% 24.12/3.52  ------ Superposition Options
% 24.12/3.52  
% 24.12/3.52  --superposition_flag                    true
% 24.12/3.52  --sup_passive_queue_type                priority_queues
% 24.12/3.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 24.12/3.52  --sup_passive_queues_freq               [8;1;4]
% 24.12/3.52  --demod_completeness_check              fast
% 24.12/3.52  --demod_use_ground                      true
% 24.12/3.52  --sup_to_prop_solver                    passive
% 24.12/3.52  --sup_prop_simpl_new                    true
% 24.12/3.52  --sup_prop_simpl_given                  true
% 24.12/3.52  --sup_fun_splitting                     true
% 24.12/3.52  --sup_smt_interval                      50000
% 24.12/3.52  
% 24.12/3.52  ------ Superposition Simplification Setup
% 24.12/3.52  
% 24.12/3.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 24.12/3.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 24.12/3.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 24.12/3.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 24.12/3.52  --sup_full_triv                         [TrivRules;PropSubs]
% 24.12/3.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 24.12/3.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 24.12/3.52  --sup_immed_triv                        [TrivRules]
% 24.12/3.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 24.12/3.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 24.12/3.52  --sup_immed_bw_main                     []
% 24.12/3.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 24.12/3.52  --sup_input_triv                        [Unflattening;TrivRules]
% 24.12/3.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 24.12/3.52  --sup_input_bw                          []
% 24.12/3.52  
% 24.12/3.52  ------ Combination Options
% 24.12/3.52  
% 24.12/3.52  --comb_res_mult                         3
% 24.12/3.52  --comb_sup_mult                         2
% 24.12/3.52  --comb_inst_mult                        10
% 24.12/3.52  
% 24.12/3.52  ------ Debug Options
% 24.12/3.52  
% 24.12/3.52  --dbg_backtrace                         false
% 24.12/3.52  --dbg_dump_prop_clauses                 false
% 24.12/3.52  --dbg_dump_prop_clauses_file            -
% 24.12/3.52  --dbg_out_stat                          false
% 24.12/3.52  ------ Parsing...
% 24.12/3.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 24.12/3.52  
% 24.12/3.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 24.12/3.52  
% 24.12/3.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 24.12/3.52  
% 24.12/3.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 24.12/3.52  ------ Proving...
% 24.12/3.52  ------ Problem Properties 
% 24.12/3.52  
% 24.12/3.52  
% 24.12/3.52  clauses                                 37
% 24.12/3.52  conjectures                             12
% 24.12/3.52  EPR                                     7
% 24.12/3.52  Horn                                    33
% 24.12/3.52  unary                                   17
% 24.12/3.52  binary                                  3
% 24.12/3.52  lits                                    137
% 24.12/3.52  lits eq                                 27
% 24.12/3.52  fd_pure                                 0
% 24.12/3.52  fd_pseudo                               0
% 24.12/3.52  fd_cond                                 4
% 24.12/3.52  fd_pseudo_cond                          3
% 24.12/3.52  AC symbols                              0
% 24.12/3.52  
% 24.12/3.52  ------ Schedule dynamic 5 is on 
% 24.12/3.52  
% 24.12/3.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 24.12/3.52  
% 24.12/3.52  
% 24.12/3.52  ------ 
% 24.12/3.52  Current options:
% 24.12/3.52  ------ 
% 24.12/3.52  
% 24.12/3.52  ------ Input Options
% 24.12/3.52  
% 24.12/3.52  --out_options                           all
% 24.12/3.52  --tptp_safe_out                         true
% 24.12/3.52  --problem_path                          ""
% 24.12/3.52  --include_path                          ""
% 24.12/3.52  --clausifier                            res/vclausify_rel
% 24.12/3.52  --clausifier_options                    ""
% 24.12/3.52  --stdin                                 false
% 24.12/3.52  --stats_out                             all
% 24.12/3.52  
% 24.12/3.52  ------ General Options
% 24.12/3.52  
% 24.12/3.52  --fof                                   false
% 24.12/3.52  --time_out_real                         305.
% 24.12/3.52  --time_out_virtual                      -1.
% 24.12/3.52  --symbol_type_check                     false
% 24.12/3.52  --clausify_out                          false
% 24.12/3.52  --sig_cnt_out                           false
% 24.12/3.52  --trig_cnt_out                          false
% 24.12/3.52  --trig_cnt_out_tolerance                1.
% 24.12/3.52  --trig_cnt_out_sk_spl                   false
% 24.12/3.52  --abstr_cl_out                          false
% 24.12/3.52  
% 24.12/3.52  ------ Global Options
% 24.12/3.52  
% 24.12/3.52  --schedule                              default
% 24.12/3.52  --add_important_lit                     false
% 24.12/3.52  --prop_solver_per_cl                    1000
% 24.12/3.52  --min_unsat_core                        false
% 24.12/3.52  --soft_assumptions                      false
% 24.12/3.52  --soft_lemma_size                       3
% 24.12/3.52  --prop_impl_unit_size                   0
% 24.12/3.52  --prop_impl_unit                        []
% 24.12/3.52  --share_sel_clauses                     true
% 24.12/3.52  --reset_solvers                         false
% 24.12/3.52  --bc_imp_inh                            [conj_cone]
% 24.12/3.52  --conj_cone_tolerance                   3.
% 24.12/3.52  --extra_neg_conj                        none
% 24.12/3.52  --large_theory_mode                     true
% 24.12/3.52  --prolific_symb_bound                   200
% 24.12/3.52  --lt_threshold                          2000
% 24.12/3.52  --clause_weak_htbl                      true
% 24.12/3.52  --gc_record_bc_elim                     false
% 24.12/3.52  
% 24.12/3.52  ------ Preprocessing Options
% 24.12/3.52  
% 24.12/3.52  --preprocessing_flag                    true
% 24.12/3.52  --time_out_prep_mult                    0.1
% 24.12/3.52  --splitting_mode                        input
% 24.12/3.52  --splitting_grd                         true
% 24.12/3.52  --splitting_cvd                         false
% 24.12/3.52  --splitting_cvd_svl                     false
% 24.12/3.52  --splitting_nvd                         32
% 24.12/3.52  --sub_typing                            true
% 24.12/3.52  --prep_gs_sim                           true
% 24.12/3.52  --prep_unflatten                        true
% 24.12/3.52  --prep_res_sim                          true
% 24.12/3.52  --prep_upred                            true
% 24.12/3.52  --prep_sem_filter                       exhaustive
% 24.12/3.52  --prep_sem_filter_out                   false
% 24.12/3.52  --pred_elim                             true
% 24.12/3.52  --res_sim_input                         true
% 24.12/3.52  --eq_ax_congr_red                       true
% 24.12/3.52  --pure_diseq_elim                       true
% 24.12/3.52  --brand_transform                       false
% 24.12/3.52  --non_eq_to_eq                          false
% 24.12/3.52  --prep_def_merge                        true
% 24.12/3.52  --prep_def_merge_prop_impl              false
% 24.12/3.52  --prep_def_merge_mbd                    true
% 24.12/3.52  --prep_def_merge_tr_red                 false
% 24.12/3.52  --prep_def_merge_tr_cl                  false
% 24.12/3.52  --smt_preprocessing                     true
% 24.12/3.52  --smt_ac_axioms                         fast
% 24.12/3.52  --preprocessed_out                      false
% 24.12/3.52  --preprocessed_stats                    false
% 24.12/3.52  
% 24.12/3.52  ------ Abstraction refinement Options
% 24.12/3.52  
% 24.12/3.52  --abstr_ref                             []
% 24.12/3.52  --abstr_ref_prep                        false
% 24.12/3.52  --abstr_ref_until_sat                   false
% 24.12/3.52  --abstr_ref_sig_restrict                funpre
% 24.12/3.52  --abstr_ref_af_restrict_to_split_sk     false
% 24.12/3.52  --abstr_ref_under                       []
% 24.12/3.52  
% 24.12/3.52  ------ SAT Options
% 24.12/3.52  
% 24.12/3.52  --sat_mode                              false
% 24.12/3.52  --sat_fm_restart_options                ""
% 24.12/3.52  --sat_gr_def                            false
% 24.12/3.52  --sat_epr_types                         true
% 24.12/3.52  --sat_non_cyclic_types                  false
% 24.12/3.52  --sat_finite_models                     false
% 24.12/3.52  --sat_fm_lemmas                         false
% 24.12/3.52  --sat_fm_prep                           false
% 24.12/3.52  --sat_fm_uc_incr                        true
% 24.12/3.52  --sat_out_model                         small
% 24.12/3.52  --sat_out_clauses                       false
% 24.12/3.52  
% 24.12/3.52  ------ QBF Options
% 24.12/3.52  
% 24.12/3.52  --qbf_mode                              false
% 24.12/3.52  --qbf_elim_univ                         false
% 24.12/3.52  --qbf_dom_inst                          none
% 24.12/3.52  --qbf_dom_pre_inst                      false
% 24.12/3.52  --qbf_sk_in                             false
% 24.12/3.52  --qbf_pred_elim                         true
% 24.12/3.52  --qbf_split                             512
% 24.12/3.52  
% 24.12/3.52  ------ BMC1 Options
% 24.12/3.52  
% 24.12/3.52  --bmc1_incremental                      false
% 24.12/3.52  --bmc1_axioms                           reachable_all
% 24.12/3.52  --bmc1_min_bound                        0
% 24.12/3.52  --bmc1_max_bound                        -1
% 24.12/3.52  --bmc1_max_bound_default                -1
% 24.12/3.52  --bmc1_symbol_reachability              true
% 24.12/3.52  --bmc1_property_lemmas                  false
% 24.12/3.52  --bmc1_k_induction                      false
% 24.12/3.52  --bmc1_non_equiv_states                 false
% 24.12/3.52  --bmc1_deadlock                         false
% 24.12/3.52  --bmc1_ucm                              false
% 24.12/3.52  --bmc1_add_unsat_core                   none
% 24.12/3.52  --bmc1_unsat_core_children              false
% 24.12/3.52  --bmc1_unsat_core_extrapolate_axioms    false
% 24.12/3.52  --bmc1_out_stat                         full
% 24.12/3.52  --bmc1_ground_init                      false
% 24.12/3.52  --bmc1_pre_inst_next_state              false
% 24.12/3.52  --bmc1_pre_inst_state                   false
% 24.12/3.52  --bmc1_pre_inst_reach_state             false
% 24.12/3.52  --bmc1_out_unsat_core                   false
% 24.12/3.52  --bmc1_aig_witness_out                  false
% 24.12/3.52  --bmc1_verbose                          false
% 24.12/3.52  --bmc1_dump_clauses_tptp                false
% 24.12/3.52  --bmc1_dump_unsat_core_tptp             false
% 24.12/3.52  --bmc1_dump_file                        -
% 24.12/3.52  --bmc1_ucm_expand_uc_limit              128
% 24.12/3.52  --bmc1_ucm_n_expand_iterations          6
% 24.12/3.52  --bmc1_ucm_extend_mode                  1
% 24.12/3.52  --bmc1_ucm_init_mode                    2
% 24.12/3.52  --bmc1_ucm_cone_mode                    none
% 24.12/3.52  --bmc1_ucm_reduced_relation_type        0
% 24.12/3.52  --bmc1_ucm_relax_model                  4
% 24.12/3.52  --bmc1_ucm_full_tr_after_sat            true
% 24.12/3.52  --bmc1_ucm_expand_neg_assumptions       false
% 24.12/3.52  --bmc1_ucm_layered_model                none
% 24.12/3.52  --bmc1_ucm_max_lemma_size               10
% 24.12/3.52  
% 24.12/3.52  ------ AIG Options
% 24.12/3.52  
% 24.12/3.52  --aig_mode                              false
% 24.12/3.52  
% 24.12/3.52  ------ Instantiation Options
% 24.12/3.52  
% 24.12/3.52  --instantiation_flag                    true
% 24.12/3.52  --inst_sos_flag                         true
% 24.12/3.52  --inst_sos_phase                        true
% 24.12/3.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 24.12/3.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 24.12/3.52  --inst_lit_sel_side                     none
% 24.12/3.52  --inst_solver_per_active                1400
% 24.12/3.52  --inst_solver_calls_frac                1.
% 24.12/3.52  --inst_passive_queue_type               priority_queues
% 24.12/3.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 24.12/3.52  --inst_passive_queues_freq              [25;2]
% 24.12/3.52  --inst_dismatching                      true
% 24.12/3.52  --inst_eager_unprocessed_to_passive     true
% 24.12/3.52  --inst_prop_sim_given                   true
% 24.12/3.52  --inst_prop_sim_new                     false
% 24.12/3.52  --inst_subs_new                         false
% 24.12/3.52  --inst_eq_res_simp                      false
% 24.12/3.52  --inst_subs_given                       false
% 24.12/3.52  --inst_orphan_elimination               true
% 24.12/3.52  --inst_learning_loop_flag               true
% 24.12/3.52  --inst_learning_start                   3000
% 24.12/3.52  --inst_learning_factor                  2
% 24.12/3.52  --inst_start_prop_sim_after_learn       3
% 24.12/3.52  --inst_sel_renew                        solver
% 24.12/3.52  --inst_lit_activity_flag                true
% 24.12/3.52  --inst_restr_to_given                   false
% 24.12/3.52  --inst_activity_threshold               500
% 24.12/3.52  --inst_out_proof                        true
% 24.12/3.52  
% 24.12/3.52  ------ Resolution Options
% 24.12/3.52  
% 24.12/3.52  --resolution_flag                       false
% 24.12/3.52  --res_lit_sel                           adaptive
% 24.12/3.52  --res_lit_sel_side                      none
% 24.12/3.52  --res_ordering                          kbo
% 24.12/3.52  --res_to_prop_solver                    active
% 24.12/3.52  --res_prop_simpl_new                    false
% 24.12/3.52  --res_prop_simpl_given                  true
% 24.12/3.52  --res_passive_queue_type                priority_queues
% 24.12/3.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 24.12/3.52  --res_passive_queues_freq               [15;5]
% 24.12/3.52  --res_forward_subs                      full
% 24.12/3.52  --res_backward_subs                     full
% 24.12/3.52  --res_forward_subs_resolution           true
% 24.12/3.52  --res_backward_subs_resolution          true
% 24.12/3.52  --res_orphan_elimination                true
% 24.12/3.52  --res_time_limit                        2.
% 24.12/3.52  --res_out_proof                         true
% 24.12/3.52  
% 24.12/3.52  ------ Superposition Options
% 24.12/3.52  
% 24.12/3.52  --superposition_flag                    true
% 24.12/3.52  --sup_passive_queue_type                priority_queues
% 24.12/3.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 24.12/3.52  --sup_passive_queues_freq               [8;1;4]
% 24.12/3.52  --demod_completeness_check              fast
% 24.12/3.52  --demod_use_ground                      true
% 24.12/3.52  --sup_to_prop_solver                    passive
% 24.12/3.52  --sup_prop_simpl_new                    true
% 24.12/3.52  --sup_prop_simpl_given                  true
% 24.12/3.52  --sup_fun_splitting                     true
% 24.12/3.52  --sup_smt_interval                      50000
% 24.12/3.52  
% 24.12/3.52  ------ Superposition Simplification Setup
% 24.12/3.52  
% 24.12/3.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 24.12/3.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 24.12/3.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 24.12/3.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 24.12/3.52  --sup_full_triv                         [TrivRules;PropSubs]
% 24.12/3.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 24.12/3.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 24.12/3.52  --sup_immed_triv                        [TrivRules]
% 24.12/3.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 24.12/3.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 24.12/3.52  --sup_immed_bw_main                     []
% 24.12/3.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 24.12/3.52  --sup_input_triv                        [Unflattening;TrivRules]
% 24.12/3.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 24.12/3.52  --sup_input_bw                          []
% 24.12/3.52  
% 24.12/3.52  ------ Combination Options
% 24.12/3.52  
% 24.12/3.52  --comb_res_mult                         3
% 24.12/3.52  --comb_sup_mult                         2
% 24.12/3.52  --comb_inst_mult                        10
% 24.12/3.52  
% 24.12/3.52  ------ Debug Options
% 24.12/3.52  
% 24.12/3.52  --dbg_backtrace                         false
% 24.12/3.52  --dbg_dump_prop_clauses                 false
% 24.12/3.52  --dbg_dump_prop_clauses_file            -
% 24.12/3.52  --dbg_out_stat                          false
% 24.12/3.52  
% 24.12/3.52  
% 24.12/3.52  
% 24.12/3.52  
% 24.12/3.52  ------ Proving...
% 24.12/3.52  
% 24.12/3.52  
% 24.12/3.52  % SZS status Theorem for theBenchmark.p
% 24.12/3.52  
% 24.12/3.52  % SZS output start CNFRefutation for theBenchmark.p
% 24.12/3.52  
% 24.12/3.52  fof(f8,axiom,(
% 24.12/3.52    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f60,plain,(
% 24.12/3.52    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 24.12/3.52    inference(cnf_transformation,[],[f8])).
% 24.12/3.52  
% 24.12/3.52  fof(f12,axiom,(
% 24.12/3.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f66,plain,(
% 24.12/3.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f12])).
% 24.12/3.52  
% 24.12/3.52  fof(f95,plain,(
% 24.12/3.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 24.12/3.52    inference(definition_unfolding,[],[f60,f66])).
% 24.12/3.52  
% 24.12/3.52  fof(f17,conjecture,(
% 24.12/3.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f18,negated_conjecture,(
% 24.12/3.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 24.12/3.52    inference(negated_conjecture,[],[f17])).
% 24.12/3.52  
% 24.12/3.52  fof(f42,plain,(
% 24.12/3.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 24.12/3.52    inference(ennf_transformation,[],[f18])).
% 24.12/3.52  
% 24.12/3.52  fof(f43,plain,(
% 24.12/3.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 24.12/3.52    inference(flattening,[],[f42])).
% 24.12/3.52  
% 24.12/3.52  fof(f47,plain,(
% 24.12/3.52    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 24.12/3.52    introduced(choice_axiom,[])).
% 24.12/3.52  
% 24.12/3.52  fof(f46,plain,(
% 24.12/3.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 24.12/3.52    introduced(choice_axiom,[])).
% 24.12/3.52  
% 24.12/3.52  fof(f48,plain,(
% 24.12/3.52    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 24.12/3.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f47,f46])).
% 24.12/3.52  
% 24.12/3.52  fof(f78,plain,(
% 24.12/3.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f81,plain,(
% 24.12/3.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f11,axiom,(
% 24.12/3.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f32,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 24.12/3.52    inference(ennf_transformation,[],[f11])).
% 24.12/3.52  
% 24.12/3.52  fof(f33,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 24.12/3.52    inference(flattening,[],[f32])).
% 24.12/3.52  
% 24.12/3.52  fof(f65,plain,(
% 24.12/3.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f33])).
% 24.12/3.52  
% 24.12/3.52  fof(f79,plain,(
% 24.12/3.52    v1_funct_1(sK3)),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f76,plain,(
% 24.12/3.52    v1_funct_1(sK2)),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f83,plain,(
% 24.12/3.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f10,axiom,(
% 24.12/3.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f30,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 24.12/3.52    inference(ennf_transformation,[],[f10])).
% 24.12/3.52  
% 24.12/3.52  fof(f31,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 24.12/3.52    inference(flattening,[],[f30])).
% 24.12/3.52  
% 24.12/3.52  fof(f64,plain,(
% 24.12/3.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f31])).
% 24.12/3.52  
% 24.12/3.52  fof(f7,axiom,(
% 24.12/3.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f26,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 24.12/3.52    inference(ennf_transformation,[],[f7])).
% 24.12/3.52  
% 24.12/3.52  fof(f27,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 24.12/3.52    inference(flattening,[],[f26])).
% 24.12/3.52  
% 24.12/3.52  fof(f44,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 24.12/3.52    inference(nnf_transformation,[],[f27])).
% 24.12/3.52  
% 24.12/3.52  fof(f58,plain,(
% 24.12/3.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 24.12/3.52    inference(cnf_transformation,[],[f44])).
% 24.12/3.52  
% 24.12/3.52  fof(f82,plain,(
% 24.12/3.52    k2_relset_1(sK0,sK1,sK2) = sK1),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f15,axiom,(
% 24.12/3.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f38,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 24.12/3.52    inference(ennf_transformation,[],[f15])).
% 24.12/3.52  
% 24.12/3.52  fof(f39,plain,(
% 24.12/3.52    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 24.12/3.52    inference(flattening,[],[f38])).
% 24.12/3.52  
% 24.12/3.52  fof(f72,plain,(
% 24.12/3.52    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f39])).
% 24.12/3.52  
% 24.12/3.52  fof(f77,plain,(
% 24.12/3.52    v1_funct_2(sK2,sK0,sK1)),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f80,plain,(
% 24.12/3.52    v1_funct_2(sK3,sK1,sK0)),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f85,plain,(
% 24.12/3.52    k1_xboole_0 != sK0),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f2,axiom,(
% 24.12/3.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f52,plain,(
% 24.12/3.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 24.12/3.52    inference(cnf_transformation,[],[f2])).
% 24.12/3.52  
% 24.12/3.52  fof(f90,plain,(
% 24.12/3.52    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 24.12/3.52    inference(definition_unfolding,[],[f52,f66])).
% 24.12/3.52  
% 24.12/3.52  fof(f3,axiom,(
% 24.12/3.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f20,plain,(
% 24.12/3.52    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 24.12/3.52    inference(ennf_transformation,[],[f3])).
% 24.12/3.52  
% 24.12/3.52  fof(f21,plain,(
% 24.12/3.52    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 24.12/3.52    inference(flattening,[],[f20])).
% 24.12/3.52  
% 24.12/3.52  fof(f53,plain,(
% 24.12/3.52    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f21])).
% 24.12/3.52  
% 24.12/3.52  fof(f93,plain,(
% 24.12/3.52    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 24.12/3.52    inference(definition_unfolding,[],[f53,f66])).
% 24.12/3.52  
% 24.12/3.52  fof(f5,axiom,(
% 24.12/3.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f24,plain,(
% 24.12/3.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 24.12/3.52    inference(ennf_transformation,[],[f5])).
% 24.12/3.52  
% 24.12/3.52  fof(f56,plain,(
% 24.12/3.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 24.12/3.52    inference(cnf_transformation,[],[f24])).
% 24.12/3.52  
% 24.12/3.52  fof(f4,axiom,(
% 24.12/3.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f22,plain,(
% 24.12/3.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 24.12/3.52    inference(ennf_transformation,[],[f4])).
% 24.12/3.52  
% 24.12/3.52  fof(f23,plain,(
% 24.12/3.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 24.12/3.52    inference(flattening,[],[f22])).
% 24.12/3.52  
% 24.12/3.52  fof(f55,plain,(
% 24.12/3.52    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f23])).
% 24.12/3.52  
% 24.12/3.52  fof(f94,plain,(
% 24.12/3.52    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 24.12/3.52    inference(definition_unfolding,[],[f55,f66])).
% 24.12/3.52  
% 24.12/3.52  fof(f14,axiom,(
% 24.12/3.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f36,plain,(
% 24.12/3.52    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 24.12/3.52    inference(ennf_transformation,[],[f14])).
% 24.12/3.52  
% 24.12/3.52  fof(f37,plain,(
% 24.12/3.52    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 24.12/3.52    inference(flattening,[],[f36])).
% 24.12/3.52  
% 24.12/3.52  fof(f69,plain,(
% 24.12/3.52    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f37])).
% 24.12/3.52  
% 24.12/3.52  fof(f6,axiom,(
% 24.12/3.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f19,plain,(
% 24.12/3.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 24.12/3.52    inference(pure_predicate_removal,[],[f6])).
% 24.12/3.52  
% 24.12/3.52  fof(f25,plain,(
% 24.12/3.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 24.12/3.52    inference(ennf_transformation,[],[f19])).
% 24.12/3.52  
% 24.12/3.52  fof(f57,plain,(
% 24.12/3.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 24.12/3.52    inference(cnf_transformation,[],[f25])).
% 24.12/3.52  
% 24.12/3.52  fof(f9,axiom,(
% 24.12/3.52    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f28,plain,(
% 24.12/3.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 24.12/3.52    inference(ennf_transformation,[],[f9])).
% 24.12/3.52  
% 24.12/3.52  fof(f29,plain,(
% 24.12/3.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 24.12/3.52    inference(flattening,[],[f28])).
% 24.12/3.52  
% 24.12/3.52  fof(f45,plain,(
% 24.12/3.52    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 24.12/3.52    inference(nnf_transformation,[],[f29])).
% 24.12/3.52  
% 24.12/3.52  fof(f61,plain,(
% 24.12/3.52    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f45])).
% 24.12/3.52  
% 24.12/3.52  fof(f84,plain,(
% 24.12/3.52    v2_funct_1(sK2)),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f16,axiom,(
% 24.12/3.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f40,plain,(
% 24.12/3.52    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 24.12/3.52    inference(ennf_transformation,[],[f16])).
% 24.12/3.52  
% 24.12/3.52  fof(f41,plain,(
% 24.12/3.52    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 24.12/3.52    inference(flattening,[],[f40])).
% 24.12/3.52  
% 24.12/3.52  fof(f75,plain,(
% 24.12/3.52    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f41])).
% 24.12/3.52  
% 24.12/3.52  fof(f54,plain,(
% 24.12/3.52    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f21])).
% 24.12/3.52  
% 24.12/3.52  fof(f92,plain,(
% 24.12/3.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 24.12/3.52    inference(definition_unfolding,[],[f54,f66])).
% 24.12/3.52  
% 24.12/3.52  fof(f86,plain,(
% 24.12/3.52    k1_xboole_0 != sK1),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  fof(f1,axiom,(
% 24.12/3.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f50,plain,(
% 24.12/3.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 24.12/3.52    inference(cnf_transformation,[],[f1])).
% 24.12/3.52  
% 24.12/3.52  fof(f88,plain,(
% 24.12/3.52    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 24.12/3.52    inference(definition_unfolding,[],[f50,f66])).
% 24.12/3.52  
% 24.12/3.52  fof(f13,axiom,(
% 24.12/3.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 24.12/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 24.12/3.52  
% 24.12/3.52  fof(f34,plain,(
% 24.12/3.52    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 24.12/3.52    inference(ennf_transformation,[],[f13])).
% 24.12/3.52  
% 24.12/3.52  fof(f35,plain,(
% 24.12/3.52    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 24.12/3.52    inference(flattening,[],[f34])).
% 24.12/3.52  
% 24.12/3.52  fof(f67,plain,(
% 24.12/3.52    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f35])).
% 24.12/3.52  
% 24.12/3.52  fof(f74,plain,(
% 24.12/3.52    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 24.12/3.52    inference(cnf_transformation,[],[f41])).
% 24.12/3.52  
% 24.12/3.52  fof(f87,plain,(
% 24.12/3.52    k2_funct_1(sK2) != sK3),
% 24.12/3.52    inference(cnf_transformation,[],[f48])).
% 24.12/3.52  
% 24.12/3.52  cnf(c_11,plain,
% 24.12/3.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 24.12/3.52      inference(cnf_transformation,[],[f95]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1790,plain,
% 24.12/3.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_35,negated_conjecture,
% 24.12/3.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 24.12/3.52      inference(cnf_transformation,[],[f78]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1772,plain,
% 24.12/3.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_32,negated_conjecture,
% 24.12/3.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 24.12/3.52      inference(cnf_transformation,[],[f81]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1775,plain,
% 24.12/3.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_16,plain,
% 24.12/3.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.12/3.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 24.12/3.52      | ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v1_funct_1(X3)
% 24.12/3.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 24.12/3.52      inference(cnf_transformation,[],[f65]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1787,plain,
% 24.12/3.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 24.12/3.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 24.12/3.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | v1_funct_1(X5) != iProver_top
% 24.12/3.52      | v1_funct_1(X4) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_3418,plain,
% 24.12/3.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 24.12/3.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | v1_funct_1(X2) != iProver_top
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_1775,c_1787]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_34,negated_conjecture,
% 24.12/3.52      ( v1_funct_1(sK3) ),
% 24.12/3.52      inference(cnf_transformation,[],[f79]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_41,plain,
% 24.12/3.52      ( v1_funct_1(sK3) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4116,plain,
% 24.12/3.52      ( v1_funct_1(X2) != iProver_top
% 24.12/3.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_3418,c_41]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4117,plain,
% 24.12/3.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 24.12/3.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | v1_funct_1(X2) != iProver_top ),
% 24.12/3.52      inference(renaming,[status(thm)],[c_4116]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4125,plain,
% 24.12/3.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_1772,c_4117]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_37,negated_conjecture,
% 24.12/3.52      ( v1_funct_1(sK2) ),
% 24.12/3.52      inference(cnf_transformation,[],[f76]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_38,plain,
% 24.12/3.52      ( v1_funct_1(sK2) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4317,plain,
% 24.12/3.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_4125,c_38]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_30,negated_conjecture,
% 24.12/3.52      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 24.12/3.52      inference(cnf_transformation,[],[f83]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1776,plain,
% 24.12/3.52      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4319,plain,
% 24.12/3.52      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 24.12/3.52      inference(demodulation,[status(thm)],[c_4317,c_1776]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_14,plain,
% 24.12/3.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.12/3.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 24.12/3.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 24.12/3.52      | ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v1_funct_1(X3) ),
% 24.12/3.52      inference(cnf_transformation,[],[f64]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1789,plain,
% 24.12/3.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 24.12/3.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 24.12/3.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 24.12/3.52      | v1_funct_1(X0) != iProver_top
% 24.12/3.52      | v1_funct_1(X3) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4321,plain,
% 24.12/3.52      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 24.12/3.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 24.12/3.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_4317,c_1789]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_40,plain,
% 24.12/3.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_43,plain,
% 24.12/3.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_6070,plain,
% 24.12/3.52      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_4321,c_38,c_40,c_41,c_43]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_10,plain,
% 24.12/3.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 24.12/3.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 24.12/3.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 24.12/3.52      | X3 = X2 ),
% 24.12/3.52      inference(cnf_transformation,[],[f58]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1791,plain,
% 24.12/3.52      ( X0 = X1
% 24.12/3.52      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 24.12/3.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 24.12/3.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_6080,plain,
% 24.12/3.52      ( k5_relat_1(sK2,sK3) = X0
% 24.12/3.52      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
% 24.12/3.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_6070,c_1791]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8502,plain,
% 24.12/3.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 24.12/3.52      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_4319,c_6080]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8524,plain,
% 24.12/3.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_1790,c_8502]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_31,negated_conjecture,
% 24.12/3.52      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 24.12/3.52      inference(cnf_transformation,[],[f82]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_21,plain,
% 24.12/3.52      ( ~ v1_funct_2(X0,X1,X2)
% 24.12/3.52      | ~ v1_funct_2(X3,X4,X1)
% 24.12/3.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 24.12/3.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.12/3.52      | ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v1_funct_1(X3)
% 24.12/3.52      | v2_funct_1(X0)
% 24.12/3.52      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 24.12/3.52      | k2_relset_1(X4,X1,X3) != X1
% 24.12/3.52      | k1_xboole_0 = X2 ),
% 24.12/3.52      inference(cnf_transformation,[],[f72]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1782,plain,
% 24.12/3.52      ( k2_relset_1(X0,X1,X2) != X1
% 24.12/3.52      | k1_xboole_0 = X3
% 24.12/3.52      | v1_funct_2(X4,X1,X3) != iProver_top
% 24.12/3.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 24.12/3.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 24.12/3.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | v1_funct_1(X4) != iProver_top
% 24.12/3.52      | v1_funct_1(X2) != iProver_top
% 24.12/3.52      | v2_funct_1(X4) = iProver_top
% 24.12/3.52      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_5743,plain,
% 24.12/3.52      ( k1_xboole_0 = X0
% 24.12/3.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 24.12/3.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 24.12/3.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 24.12/3.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_funct_1(X1) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(X1) = iProver_top
% 24.12/3.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_31,c_1782]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_36,negated_conjecture,
% 24.12/3.52      ( v1_funct_2(sK2,sK0,sK1) ),
% 24.12/3.52      inference(cnf_transformation,[],[f77]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_39,plain,
% 24.12/3.52      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_5781,plain,
% 24.12/3.52      ( v1_funct_1(X1) != iProver_top
% 24.12/3.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 24.12/3.52      | k1_xboole_0 = X0
% 24.12/3.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 24.12/3.52      | v2_funct_1(X1) = iProver_top
% 24.12/3.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_5743,c_38,c_39,c_40]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_5782,plain,
% 24.12/3.52      ( k1_xboole_0 = X0
% 24.12/3.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 24.12/3.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 24.12/3.52      | v1_funct_1(X1) != iProver_top
% 24.12/3.52      | v2_funct_1(X1) = iProver_top
% 24.12/3.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 24.12/3.52      inference(renaming,[status(thm)],[c_5781]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_5785,plain,
% 24.12/3.52      ( sK0 = k1_xboole_0
% 24.12/3.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 24.12/3.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 24.12/3.52      | v2_funct_1(sK3) = iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_4317,c_5782]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_33,negated_conjecture,
% 24.12/3.52      ( v1_funct_2(sK3,sK1,sK0) ),
% 24.12/3.52      inference(cnf_transformation,[],[f80]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_42,plain,
% 24.12/3.52      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_28,negated_conjecture,
% 24.12/3.52      ( k1_xboole_0 != sK0 ),
% 24.12/3.52      inference(cnf_transformation,[],[f85]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1231,plain,( X0 = X0 ),theory(equality) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1266,plain,
% 24.12/3.52      ( k1_xboole_0 = k1_xboole_0 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_1231]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1232,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1896,plain,
% 24.12/3.52      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_1232]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1897,plain,
% 24.12/3.52      ( sK0 != k1_xboole_0
% 24.12/3.52      | k1_xboole_0 = sK0
% 24.12/3.52      | k1_xboole_0 != k1_xboole_0 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_1896]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_5877,plain,
% 24.12/3.52      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 24.12/3.52      | v2_funct_1(sK3) = iProver_top ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_5785,c_41,c_42,c_43,c_28,c_1266,c_1897]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8618,plain,
% 24.12/3.52      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 24.12/3.52      | v2_funct_1(sK3) = iProver_top ),
% 24.12/3.52      inference(demodulation,[status(thm)],[c_8524,c_5877]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2,plain,
% 24.12/3.52      ( v2_funct_1(k6_partfun1(X0)) ),
% 24.12/3.52      inference(cnf_transformation,[],[f90]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4980,plain,
% 24.12/3.52      ( v2_funct_1(k6_partfun1(sK0)) ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_2]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4981,plain,
% 24.12/3.52      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_4980]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8642,plain,
% 24.12/3.52      ( v2_funct_1(sK3) = iProver_top ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_8618,c_4981]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1773,plain,
% 24.12/3.52      ( v1_funct_1(sK3) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_5,plain,
% 24.12/3.52      ( ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v1_relat_1(X0)
% 24.12/3.52      | ~ v2_funct_1(X0)
% 24.12/3.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 24.12/3.52      inference(cnf_transformation,[],[f93]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1795,plain,
% 24.12/3.52      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 24.12/3.52      | v1_funct_1(X0) != iProver_top
% 24.12/3.52      | v1_relat_1(X0) != iProver_top
% 24.12/3.52      | v2_funct_1(X0) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2821,plain,
% 24.12/3.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 24.12/3.52      | v1_relat_1(sK3) != iProver_top
% 24.12/3.52      | v2_funct_1(sK3) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_1773,c_1795]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_7,plain,
% 24.12/3.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.12/3.52      | v1_relat_1(X0) ),
% 24.12/3.52      inference(cnf_transformation,[],[f56]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1910,plain,
% 24.12/3.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 24.12/3.52      | v1_relat_1(sK3) ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_7]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2196,plain,
% 24.12/3.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 24.12/3.52      | v1_relat_1(sK3) ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_1910]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2197,plain,
% 24.12/3.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 24.12/3.52      | v1_relat_1(sK3) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_2196]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_3211,plain,
% 24.12/3.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 24.12/3.52      | v2_funct_1(sK3) != iProver_top ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_2821,c_43,c_2197]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8647,plain,
% 24.12/3.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_8642,c_3211]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_6,plain,
% 24.12/3.52      ( ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v1_funct_1(X1)
% 24.12/3.52      | ~ v1_relat_1(X0)
% 24.12/3.52      | ~ v1_relat_1(X1)
% 24.12/3.52      | ~ v2_funct_1(X0)
% 24.12/3.52      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 24.12/3.52      | k2_funct_1(X0) = X1
% 24.12/3.52      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 24.12/3.52      inference(cnf_transformation,[],[f94]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1794,plain,
% 24.12/3.52      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 24.12/3.52      | k2_funct_1(X1) = X0
% 24.12/3.52      | k1_relat_1(X1) != k2_relat_1(X0)
% 24.12/3.52      | v1_funct_1(X1) != iProver_top
% 24.12/3.52      | v1_funct_1(X0) != iProver_top
% 24.12/3.52      | v1_relat_1(X1) != iProver_top
% 24.12/3.52      | v1_relat_1(X0) != iProver_top
% 24.12/3.52      | v2_funct_1(X1) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8938,plain,
% 24.12/3.52      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 24.12/3.52      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 24.12/3.52      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 24.12/3.52      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 24.12/3.52      | v1_relat_1(sK3) != iProver_top
% 24.12/3.52      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_8647,c_1794]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_18,plain,
% 24.12/3.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 24.12/3.52      | ~ v1_funct_2(X3,X1,X0)
% 24.12/3.52      | ~ v1_funct_2(X2,X0,X1)
% 24.12/3.52      | v2_funct_2(X3,X0)
% 24.12/3.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 24.12/3.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 24.12/3.52      | ~ v1_funct_1(X3)
% 24.12/3.52      | ~ v1_funct_1(X2) ),
% 24.12/3.52      inference(cnf_transformation,[],[f69]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1785,plain,
% 24.12/3.52      ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 24.12/3.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 24.12/3.52      | v1_funct_2(X3,X1,X0) != iProver_top
% 24.12/3.52      | v2_funct_2(X3,X0) = iProver_top
% 24.12/3.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 24.12/3.52      | v1_funct_1(X2) != iProver_top
% 24.12/3.52      | v1_funct_1(X3) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4863,plain,
% 24.12/3.52      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) != iProver_top
% 24.12/3.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 24.12/3.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 24.12/3.52      | v2_funct_2(sK3,sK0) = iProver_top
% 24.12/3.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 24.12/3.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_4317,c_1785]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_6915,plain,
% 24.12/3.52      ( v2_funct_2(sK3,sK0) = iProver_top ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_4863,c_38,c_39,c_40,c_41,c_42,c_43,c_4319]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8,plain,
% 24.12/3.52      ( v5_relat_1(X0,X1)
% 24.12/3.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 24.12/3.52      inference(cnf_transformation,[],[f57]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_13,plain,
% 24.12/3.52      ( ~ v2_funct_2(X0,X1)
% 24.12/3.52      | ~ v5_relat_1(X0,X1)
% 24.12/3.52      | ~ v1_relat_1(X0)
% 24.12/3.52      | k2_relat_1(X0) = X1 ),
% 24.12/3.52      inference(cnf_transformation,[],[f61]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_363,plain,
% 24.12/3.52      ( ~ v2_funct_2(X0,X1)
% 24.12/3.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 24.12/3.52      | ~ v1_relat_1(X0)
% 24.12/3.52      | k2_relat_1(X0) = X1 ),
% 24.12/3.52      inference(resolution,[status(thm)],[c_8,c_13]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_375,plain,
% 24.12/3.52      ( ~ v2_funct_2(X0,X1)
% 24.12/3.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 24.12/3.52      | k2_relat_1(X0) = X1 ),
% 24.12/3.52      inference(forward_subsumption_resolution,[status(thm)],[c_363,c_7]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1769,plain,
% 24.12/3.52      ( k2_relat_1(X0) = X1
% 24.12/3.52      | v2_funct_2(X0,X1) != iProver_top
% 24.12/3.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2715,plain,
% 24.12/3.52      ( k2_relat_1(sK3) = sK0 | v2_funct_2(sK3,sK0) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_1775,c_1769]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_6919,plain,
% 24.12/3.52      ( k2_relat_1(sK3) = sK0 ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_6915,c_2715]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8939,plain,
% 24.12/3.52      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 24.12/3.52      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 24.12/3.52      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 24.12/3.52      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 24.12/3.52      | v1_relat_1(sK3) != iProver_top
% 24.12/3.52      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 24.12/3.52      inference(light_normalisation,[status(thm)],[c_8938,c_6919]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_29,negated_conjecture,
% 24.12/3.52      ( v2_funct_1(sK2) ),
% 24.12/3.52      inference(cnf_transformation,[],[f84]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_45,plain,
% 24.12/3.52      ( v2_funct_1(sK2) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2496,plain,
% 24.12/3.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 24.12/3.52      | v1_relat_1(sK2) ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_7]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2497,plain,
% 24.12/3.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_relat_1(sK2) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_2496]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8624,plain,
% 24.12/3.52      ( k2_funct_1(sK3) = sK2
% 24.12/3.52      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 24.12/3.52      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top
% 24.12/3.52      | v1_relat_1(sK3) != iProver_top
% 24.12/3.52      | v1_relat_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK3) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_8524,c_1794]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_24,plain,
% 24.12/3.52      ( ~ v1_funct_2(X0,X1,X2)
% 24.12/3.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.12/3.52      | ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v2_funct_1(X0)
% 24.12/3.52      | k2_relset_1(X1,X2,X0) != X2
% 24.12/3.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 24.12/3.52      | k1_xboole_0 = X2 ),
% 24.12/3.52      inference(cnf_transformation,[],[f75]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1779,plain,
% 24.12/3.52      ( k2_relset_1(X0,X1,X2) != X1
% 24.12/3.52      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 24.12/3.52      | k1_xboole_0 = X1
% 24.12/3.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 24.12/3.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | v1_funct_1(X2) != iProver_top
% 24.12/3.52      | v2_funct_1(X2) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4756,plain,
% 24.12/3.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 24.12/3.52      | sK1 = k1_xboole_0
% 24.12/3.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 24.12/3.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_31,c_1779]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1770,plain,
% 24.12/3.52      ( v1_funct_1(sK2) = iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4,plain,
% 24.12/3.52      ( ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v1_relat_1(X0)
% 24.12/3.52      | ~ v2_funct_1(X0)
% 24.12/3.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 24.12/3.52      inference(cnf_transformation,[],[f92]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1796,plain,
% 24.12/3.52      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 24.12/3.52      | v1_funct_1(X0) != iProver_top
% 24.12/3.52      | v1_relat_1(X0) != iProver_top
% 24.12/3.52      | v2_funct_1(X0) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2827,plain,
% 24.12/3.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 24.12/3.52      | v1_relat_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_1770,c_1796]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_3302,plain,
% 24.12/3.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_2827,c_40,c_45,c_2497]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4757,plain,
% 24.12/3.52      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
% 24.12/3.52      | sK1 = k1_xboole_0
% 24.12/3.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 24.12/3.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(demodulation,[status(thm)],[c_4756,c_3302]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_27,negated_conjecture,
% 24.12/3.52      ( k1_xboole_0 != sK1 ),
% 24.12/3.52      inference(cnf_transformation,[],[f86]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1871,plain,
% 24.12/3.52      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_1232]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1872,plain,
% 24.12/3.52      ( sK1 != k1_xboole_0
% 24.12/3.52      | k1_xboole_0 = sK1
% 24.12/3.52      | k1_xboole_0 != k1_xboole_0 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_1871]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4984,plain,
% 24.12/3.52      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_4757,c_38,c_39,c_40,c_45,c_27,c_1266,c_1872]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_0,plain,
% 24.12/3.52      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 24.12/3.52      inference(cnf_transformation,[],[f88]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4999,plain,
% 24.12/3.52      ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_4984,c_0]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_5001,plain,
% 24.12/3.52      ( k2_relat_1(sK2) = sK1 ),
% 24.12/3.52      inference(demodulation,[status(thm)],[c_4999,c_0]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8625,plain,
% 24.12/3.52      ( k2_funct_1(sK3) = sK2
% 24.12/3.52      | k1_relat_1(sK3) != sK1
% 24.12/3.52      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top
% 24.12/3.52      | v1_relat_1(sK3) != iProver_top
% 24.12/3.52      | v1_relat_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK3) != iProver_top ),
% 24.12/3.52      inference(light_normalisation,[status(thm)],[c_8624,c_5001,c_6919]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8626,plain,
% 24.12/3.52      ( k2_funct_1(sK3) = sK2
% 24.12/3.52      | k1_relat_1(sK3) != sK1
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top
% 24.12/3.52      | v1_relat_1(sK3) != iProver_top
% 24.12/3.52      | v1_relat_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK3) != iProver_top ),
% 24.12/3.52      inference(equality_resolution_simp,[status(thm)],[c_8625]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_17,plain,
% 24.12/3.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 24.12/3.52      | ~ v1_funct_2(X2,X0,X1)
% 24.12/3.52      | ~ v1_funct_2(X3,X1,X0)
% 24.12/3.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 24.12/3.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 24.12/3.52      | ~ v1_funct_1(X2)
% 24.12/3.52      | ~ v1_funct_1(X3)
% 24.12/3.52      | k2_relset_1(X1,X0,X3) = X0 ),
% 24.12/3.52      inference(cnf_transformation,[],[f67]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1786,plain,
% 24.12/3.52      ( k2_relset_1(X0,X1,X2) = X1
% 24.12/3.52      | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
% 24.12/3.52      | v1_funct_2(X3,X1,X0) != iProver_top
% 24.12/3.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 24.12/3.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 24.12/3.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | v1_funct_1(X3) != iProver_top
% 24.12/3.52      | v1_funct_1(X2) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4868,plain,
% 24.12/3.52      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 24.12/3.52      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) != iProver_top
% 24.12/3.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 24.12/3.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 24.12/3.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 24.12/3.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_4317,c_1786]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2850,plain,
% 24.12/3.52      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
% 24.12/3.52      | ~ v1_funct_2(X0,sK0,sK1)
% 24.12/3.52      | ~ v1_funct_2(sK3,sK1,sK0)
% 24.12/3.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 24.12/3.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 24.12/3.52      | ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v1_funct_1(sK3)
% 24.12/3.52      | k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_17]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_3310,plain,
% 24.12/3.52      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
% 24.12/3.52      | ~ v1_funct_2(sK3,sK1,sK0)
% 24.12/3.52      | ~ v1_funct_2(sK2,sK0,sK1)
% 24.12/3.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 24.12/3.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 24.12/3.52      | ~ v1_funct_1(sK3)
% 24.12/3.52      | ~ v1_funct_1(sK2)
% 24.12/3.52      | k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_2850]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8161,plain,
% 24.12/3.52      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_4868,c_37,c_36,c_35,c_34,c_33,c_32,c_30,c_3310]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_25,plain,
% 24.12/3.52      ( ~ v1_funct_2(X0,X1,X2)
% 24.12/3.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.12/3.52      | ~ v1_funct_1(X0)
% 24.12/3.52      | ~ v2_funct_1(X0)
% 24.12/3.52      | k2_relset_1(X1,X2,X0) != X2
% 24.12/3.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 24.12/3.52      | k1_xboole_0 = X2 ),
% 24.12/3.52      inference(cnf_transformation,[],[f74]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1778,plain,
% 24.12/3.52      ( k2_relset_1(X0,X1,X2) != X1
% 24.12/3.52      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 24.12/3.52      | k1_xboole_0 = X1
% 24.12/3.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 24.12/3.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 24.12/3.52      | v1_funct_1(X2) != iProver_top
% 24.12/3.52      | v2_funct_1(X2) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_8166,plain,
% 24.12/3.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 24.12/3.52      | sK0 = k1_xboole_0
% 24.12/3.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 24.12/3.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK3) != iProver_top
% 24.12/3.52      | v2_funct_1(sK3) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_8161,c_1778]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_21439,plain,
% 24.12/3.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_8166,c_41,c_42,c_43,c_28,c_1266,c_1897,c_4981,c_8618]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_21441,plain,
% 24.12/3.52      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 24.12/3.52      inference(demodulation,[status(thm)],[c_21439,c_8647]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_21466,plain,
% 24.12/3.52      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_21441,c_0]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_21468,plain,
% 24.12/3.52      ( k1_relat_1(sK3) = sK1 ),
% 24.12/3.52      inference(demodulation,[status(thm)],[c_21466,c_0]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1236,plain,
% 24.12/3.52      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 24.12/3.52      theory(equality) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_50815,plain,
% 24.12/3.52      ( v2_funct_1(X0) | ~ v2_funct_1(sK2) | X0 != sK2 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_1236]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_50875,plain,
% 24.12/3.52      ( v2_funct_1(k2_funct_1(X0))
% 24.12/3.52      | ~ v2_funct_1(sK2)
% 24.12/3.52      | k2_funct_1(X0) != sK2 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_50815]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_63645,plain,
% 24.12/3.52      ( v2_funct_1(k2_funct_1(sK3))
% 24.12/3.52      | ~ v2_funct_1(sK2)
% 24.12/3.52      | k2_funct_1(sK3) != sK2 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_50875]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_63646,plain,
% 24.12/3.52      ( k2_funct_1(sK3) != sK2
% 24.12/3.52      | v2_funct_1(k2_funct_1(sK3)) = iProver_top
% 24.12/3.52      | v2_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_63645]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_1237,plain,
% 24.12/3.52      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 24.12/3.52      theory(equality) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_56768,plain,
% 24.12/3.52      ( v1_relat_1(X0) | ~ v1_relat_1(sK2) | X0 != sK2 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_1237]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_64552,plain,
% 24.12/3.52      ( v1_relat_1(k2_funct_1(sK3))
% 24.12/3.52      | ~ v1_relat_1(sK2)
% 24.12/3.52      | k2_funct_1(sK3) != sK2 ),
% 24.12/3.52      inference(instantiation,[status(thm)],[c_56768]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_64553,plain,
% 24.12/3.52      ( k2_funct_1(sK3) != sK2
% 24.12/3.52      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 24.12/3.52      | v1_relat_1(sK2) != iProver_top ),
% 24.12/3.52      inference(predicate_to_equality,[status(thm)],[c_64552]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_77666,plain,
% 24.12/3.52      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 24.12/3.52      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 24.12/3.52      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 24.12/3.52      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_8939,c_38,c_40,c_41,c_43,c_45,c_2197,c_2497,c_4981,
% 24.12/3.52                 c_8618,c_8626,c_21468,c_63646,c_64553]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_3335,plain,
% 24.12/3.52      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 24.12/3.52      | sK1 = k1_xboole_0
% 24.12/3.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 24.12/3.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_31,c_1778]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_2822,plain,
% 24.12/3.52      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 24.12/3.52      | v1_relat_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_1770,c_1795]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_3216,plain,
% 24.12/3.52      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_2822,c_40,c_45,c_2497]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_3336,plain,
% 24.12/3.52      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 24.12/3.52      | sK1 = k1_xboole_0
% 24.12/3.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 24.12/3.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top
% 24.12/3.52      | v2_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(demodulation,[status(thm)],[c_3335,c_3216]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4929,plain,
% 24.12/3.52      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_3336,c_38,c_39,c_40,c_45,c_27,c_1266,c_1872]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4938,plain,
% 24.12/3.52      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 24.12/3.52      inference(superposition,[status(thm)],[c_4929,c_0]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_4940,plain,
% 24.12/3.52      ( k1_relat_1(sK2) = sK0 ),
% 24.12/3.52      inference(demodulation,[status(thm)],[c_4938,c_0]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_74051,plain,
% 24.12/3.52      ( k2_funct_1(sK3) = sK2 ),
% 24.12/3.52      inference(global_propositional_subsumption,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_8626,c_38,c_40,c_41,c_43,c_2197,c_2497,c_4981,c_8618,
% 24.12/3.52                 c_21468]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_77670,plain,
% 24.12/3.52      ( k2_funct_1(sK2) = sK3
% 24.12/3.52      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 24.12/3.52      | sK0 != sK0
% 24.12/3.52      | v1_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(light_normalisation,
% 24.12/3.52                [status(thm)],
% 24.12/3.52                [c_77666,c_4940,c_5001,c_21468,c_74051]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_77671,plain,
% 24.12/3.52      ( k2_funct_1(sK2) = sK3 | v1_funct_1(sK2) != iProver_top ),
% 24.12/3.52      inference(equality_resolution_simp,[status(thm)],[c_77670]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(c_26,negated_conjecture,
% 24.12/3.52      ( k2_funct_1(sK2) != sK3 ),
% 24.12/3.52      inference(cnf_transformation,[],[f87]) ).
% 24.12/3.52  
% 24.12/3.52  cnf(contradiction,plain,
% 24.12/3.52      ( $false ),
% 24.12/3.52      inference(minisat,[status(thm)],[c_77671,c_26,c_38]) ).
% 24.12/3.52  
% 24.12/3.52  
% 24.12/3.52  % SZS output end CNFRefutation for theBenchmark.p
% 24.12/3.52  
% 24.12/3.52  ------                               Statistics
% 24.12/3.52  
% 24.12/3.52  ------ General
% 24.12/3.52  
% 24.12/3.52  abstr_ref_over_cycles:                  0
% 24.12/3.52  abstr_ref_under_cycles:                 0
% 24.12/3.52  gc_basic_clause_elim:                   0
% 24.12/3.52  forced_gc_time:                         0
% 24.12/3.52  parsing_time:                           0.008
% 24.12/3.52  unif_index_cands_time:                  0.
% 24.12/3.52  unif_index_add_time:                    0.
% 24.12/3.52  orderings_time:                         0.
% 24.12/3.52  out_proof_time:                         0.031
% 24.12/3.52  total_time:                             2.994
% 24.12/3.52  num_of_symbols:                         53
% 24.12/3.52  num_of_terms:                           96257
% 24.12/3.52  
% 24.12/3.52  ------ Preprocessing
% 24.12/3.52  
% 24.12/3.52  num_of_splits:                          0
% 24.12/3.52  num_of_split_atoms:                     0
% 24.12/3.52  num_of_reused_defs:                     0
% 24.12/3.52  num_eq_ax_congr_red:                    4
% 24.12/3.52  num_of_sem_filtered_clauses:            1
% 24.12/3.52  num_of_subtypes:                        0
% 24.12/3.52  monotx_restored_types:                  0
% 24.12/3.52  sat_num_of_epr_types:                   0
% 24.12/3.52  sat_num_of_non_cyclic_types:            0
% 24.12/3.52  sat_guarded_non_collapsed_types:        0
% 24.12/3.52  num_pure_diseq_elim:                    0
% 24.12/3.52  simp_replaced_by:                       0
% 24.12/3.52  res_preprocessed:                       186
% 24.12/3.52  prep_upred:                             0
% 24.12/3.52  prep_unflattend:                        50
% 24.12/3.52  smt_new_axioms:                         0
% 24.12/3.52  pred_elim_cands:                        7
% 24.12/3.52  pred_elim:                              1
% 24.12/3.52  pred_elim_cl:                           1
% 24.12/3.52  pred_elim_cycles:                       5
% 24.12/3.52  merged_defs:                            0
% 24.12/3.52  merged_defs_ncl:                        0
% 24.12/3.52  bin_hyper_res:                          0
% 24.12/3.52  prep_cycles:                            4
% 24.12/3.52  pred_elim_time:                         0.011
% 24.12/3.52  splitting_time:                         0.
% 24.12/3.52  sem_filter_time:                        0.
% 24.12/3.52  monotx_time:                            0.
% 24.12/3.52  subtype_inf_time:                       0.
% 24.12/3.52  
% 24.12/3.52  ------ Problem properties
% 24.12/3.52  
% 24.12/3.52  clauses:                                37
% 24.12/3.52  conjectures:                            12
% 24.12/3.52  epr:                                    7
% 24.12/3.52  horn:                                   33
% 24.12/3.52  ground:                                 12
% 24.12/3.52  unary:                                  17
% 24.12/3.52  binary:                                 3
% 24.12/3.52  lits:                                   137
% 24.12/3.52  lits_eq:                                27
% 24.12/3.52  fd_pure:                                0
% 24.12/3.52  fd_pseudo:                              0
% 24.12/3.52  fd_cond:                                4
% 24.12/3.52  fd_pseudo_cond:                         3
% 24.12/3.52  ac_symbols:                             0
% 24.12/3.52  
% 24.12/3.52  ------ Propositional Solver
% 24.12/3.52  
% 24.12/3.52  prop_solver_calls:                      44
% 24.12/3.52  prop_fast_solver_calls:                 5539
% 24.12/3.52  smt_solver_calls:                       0
% 24.12/3.52  smt_fast_solver_calls:                  0
% 24.12/3.52  prop_num_of_clauses:                    36297
% 24.12/3.52  prop_preprocess_simplified:             55591
% 24.12/3.52  prop_fo_subsumed:                       1457
% 24.12/3.52  prop_solver_time:                       0.
% 24.12/3.52  smt_solver_time:                        0.
% 24.12/3.52  smt_fast_solver_time:                   0.
% 24.12/3.52  prop_fast_solver_time:                  0.
% 24.12/3.52  prop_unsat_core_time:                   0.006
% 24.12/3.52  
% 24.12/3.52  ------ QBF
% 24.12/3.52  
% 24.12/3.52  qbf_q_res:                              0
% 24.12/3.52  qbf_num_tautologies:                    0
% 24.12/3.52  qbf_prep_cycles:                        0
% 24.12/3.52  
% 24.12/3.52  ------ BMC1
% 24.12/3.52  
% 24.12/3.52  bmc1_current_bound:                     -1
% 24.12/3.52  bmc1_last_solved_bound:                 -1
% 24.12/3.52  bmc1_unsat_core_size:                   -1
% 24.12/3.52  bmc1_unsat_core_parents_size:           -1
% 24.12/3.52  bmc1_merge_next_fun:                    0
% 24.12/3.52  bmc1_unsat_core_clauses_time:           0.
% 24.12/3.52  
% 24.12/3.52  ------ Instantiation
% 24.12/3.52  
% 24.12/3.52  inst_num_of_clauses:                    3356
% 24.12/3.52  inst_num_in_passive:                    363
% 24.12/3.52  inst_num_in_active:                     4354
% 24.12/3.52  inst_num_in_unprocessed:                1431
% 24.12/3.52  inst_num_of_loops:                      4569
% 24.12/3.52  inst_num_of_learning_restarts:          1
% 24.12/3.52  inst_num_moves_active_passive:          207
% 24.12/3.52  inst_lit_activity:                      0
% 24.12/3.52  inst_lit_activity_moves:                1
% 24.12/3.52  inst_num_tautologies:                   0
% 24.12/3.52  inst_num_prop_implied:                  0
% 24.12/3.52  inst_num_existing_simplified:           0
% 24.12/3.52  inst_num_eq_res_simplified:             0
% 24.12/3.52  inst_num_child_elim:                    0
% 24.12/3.52  inst_num_of_dismatching_blockings:      6975
% 24.12/3.52  inst_num_of_non_proper_insts:           10052
% 24.12/3.52  inst_num_of_duplicates:                 0
% 24.12/3.52  inst_inst_num_from_inst_to_res:         0
% 24.12/3.52  inst_dismatching_checking_time:         0.
% 24.12/3.52  
% 24.12/3.52  ------ Resolution
% 24.12/3.52  
% 24.12/3.52  res_num_of_clauses:                     55
% 24.12/3.52  res_num_in_passive:                     55
% 24.12/3.52  res_num_in_active:                      0
% 24.12/3.52  res_num_of_loops:                       190
% 24.12/3.52  res_forward_subset_subsumed:            757
% 24.12/3.52  res_backward_subset_subsumed:           24
% 24.12/3.52  res_forward_subsumed:                   0
% 24.12/3.52  res_backward_subsumed:                  0
% 24.12/3.52  res_forward_subsumption_resolution:     6
% 24.12/3.52  res_backward_subsumption_resolution:    0
% 24.12/3.52  res_clause_to_clause_subsumption:       9485
% 24.12/3.52  res_orphan_elimination:                 0
% 24.12/3.52  res_tautology_del:                      493
% 24.12/3.52  res_num_eq_res_simplified:              0
% 24.12/3.52  res_num_sel_changes:                    0
% 24.12/3.52  res_moves_from_active_to_pass:          0
% 24.12/3.52  
% 24.12/3.52  ------ Superposition
% 24.12/3.52  
% 24.12/3.52  sup_time_total:                         0.
% 24.12/3.52  sup_time_generating:                    0.
% 24.12/3.52  sup_time_sim_full:                      0.
% 24.12/3.52  sup_time_sim_immed:                     0.
% 24.12/3.52  
% 24.12/3.52  sup_num_of_clauses:                     4622
% 24.12/3.52  sup_num_in_active:                      880
% 24.12/3.52  sup_num_in_passive:                     3742
% 24.12/3.52  sup_num_of_loops:                       913
% 24.12/3.52  sup_fw_superposition:                   1286
% 24.12/3.52  sup_bw_superposition:                   4071
% 24.12/3.52  sup_immediate_simplified:               1591
% 24.12/3.52  sup_given_eliminated:                   3
% 24.12/3.52  comparisons_done:                       0
% 24.12/3.52  comparisons_avoided:                    0
% 24.12/3.52  
% 24.12/3.52  ------ Simplifications
% 24.12/3.52  
% 24.12/3.52  
% 24.12/3.52  sim_fw_subset_subsumed:                 118
% 24.12/3.52  sim_bw_subset_subsumed:                 161
% 24.12/3.52  sim_fw_subsumed:                        57
% 24.12/3.52  sim_bw_subsumed:                        1
% 24.12/3.52  sim_fw_subsumption_res:                 0
% 24.12/3.52  sim_bw_subsumption_res:                 0
% 24.12/3.52  sim_tautology_del:                      0
% 24.12/3.52  sim_eq_tautology_del:                   60
% 24.12/3.52  sim_eq_res_simp:                        2
% 24.12/3.52  sim_fw_demodulated:                     462
% 24.12/3.52  sim_bw_demodulated:                     24
% 24.12/3.52  sim_light_normalised:                   1097
% 24.12/3.52  sim_joinable_taut:                      0
% 24.12/3.52  sim_joinable_simp:                      0
% 24.12/3.52  sim_ac_normalised:                      0
% 24.12/3.52  sim_smt_subsumption:                    0
% 24.12/3.52  
%------------------------------------------------------------------------------
