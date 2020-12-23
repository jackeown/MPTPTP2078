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
% DateTime   : Thu Dec  3 12:03:15 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :  233 (2065 expanded)
%              Number of clauses        :  155 ( 616 expanded)
%              Number of leaves         :   22 ( 520 expanded)
%              Depth                    :   23
%              Number of atoms          :  887 (17275 expanded)
%              Number of equality atoms :  400 (6042 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f47,f46])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f63,f67])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f89,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_700,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1316,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1303,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_2184,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1303])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_698,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1318,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_723,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1297,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_727,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_relat_1(X2_48)
    | k5_relat_1(k5_relat_1(X2_48,X1_48),X0_48) = k5_relat_1(X2_48,k5_relat_1(X1_48,X0_48)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1293,plain,
    ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
    | v1_relat_1(X2_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_2768,plain,
    ( k5_relat_1(sK3,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK3,X0_48),X1_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_2184,c_1293])).

cnf(c_5012,plain,
    ( k5_relat_1(k5_relat_1(sK3,k2_funct_1(X0_48)),X1_48) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(X0_48),X1_48))
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_2768])).

cnf(c_19923,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1318,c_5012])).

cnf(c_13,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_408,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_416,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_408,c_14])).

cnf(c_693,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_1323,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1392,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1787,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1323,c_36,c_34,c_33,c_31,c_693,c_1392])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_420,plain,
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

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_421])).

cnf(c_692,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK0)
    | ~ v1_funct_2(X1_48,sK0,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_507])).

cnf(c_1324,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_1790,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k6_partfun1(sK0)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1324,c_1787])).

cnf(c_1794,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_1790])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1400,plain,
    ( ~ v1_funct_2(X0_48,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1402,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_729,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1444,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1916,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1794,c_36,c_35,c_34,c_33,c_32,c_31,c_1402,c_1444])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_706,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1314,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_3522,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1916,c_1314])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_703,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_701,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1366,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK0,X0_48) != sK0
    | k1_xboole_0 = sK0
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1436,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) != sK0
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_733,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1458,plain,
    ( X0_48 != X1_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1513,plain,
    ( X0_48 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_1672,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1513])).

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
    inference(cnf_transformation,[],[f71])).

cnf(c_710,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(X1_48,X2_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49)))
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k1_partfun1(X2_49,X0_49,X0_49,X1_49,X1_48,X0_48))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X2_49,X0_49,X1_48) != X0_49
    | k1_xboole_0 = X1_49 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1466,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(sK3,X1_49,X2_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X2_49 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1634,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(sK3,X1_49,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,sK0)))
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,sK0,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_1748,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_742,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1858,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_48 ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_2363,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v2_funct_1(k6_partfun1(sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1858])).

cnf(c_5,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_722,plain,
    ( v2_funct_1(k6_partfun1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2981,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_18666,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3522,c_36,c_35,c_34,c_33,c_32,c_31,c_703,c_701,c_693,c_1392,c_1402,c_1436,c_1444,c_1672,c_1748,c_2363,c_2981])).

cnf(c_19932,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19923,c_18666])).

cnf(c_25440,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19932,c_2184])).

cnf(c_25441,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_25440])).

cnf(c_25449,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2184,c_25441])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_725,plain,
    ( ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1295,plain,
    ( k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_2265,plain,
    ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_2184,c_1295])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1304,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_2218,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1316,c_1304])).

cnf(c_2222,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2218,c_1916])).

cnf(c_2267,plain,
    ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2265,c_2222])).

cnf(c_695,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1321,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_697,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1319,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_2185,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_1303])).

cnf(c_2766,plain,
    ( k5_relat_1(k2_funct_1(X0_48),k5_relat_1(X1_48,X2_48)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_48),X1_48),X2_48)
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X2_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1293])).

cnf(c_9252,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_48),X1_48) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_48,X1_48))
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_2766])).

cnf(c_10017,plain,
    ( v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_48),X1_48) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_48,X1_48)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9252,c_2185])).

cnf(c_10018,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_48),X1_48) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_48,X1_48))
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_10017])).

cnf(c_10023,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_48)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_2185,c_10018])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_707,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1313,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_3423,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_1313])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_704,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1379,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK1,X0_48) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1428,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_3518,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3423,c_36,c_35,c_34,c_28,c_704,c_701,c_1428])).

cnf(c_10028,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10023,c_3518])).

cnf(c_10052,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(X0_48))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_10028])).

cnf(c_13230,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_10052])).

cnf(c_3521,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_1314])).

cnf(c_1378,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK1,X0_48) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1440,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_3670,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3521,c_36,c_35,c_34,c_28,c_704,c_701,c_1440])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_726,plain,
    ( ~ v1_relat_1(X0_48)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1294,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_2191,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0_48))),k2_funct_1(X0_48)) = k2_funct_1(X0_48)
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1294])).

cnf(c_5858,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_2191])).

cnf(c_702,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1315,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_719,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1301,plain,
    ( k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48)
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_2757,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1301])).

cnf(c_2219,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1319,c_1304])).

cnf(c_2221,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2219,c_701])).

cnf(c_2759,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2757,c_2221])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3051,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2759,c_37,c_2185])).

cnf(c_5863,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5858,c_3051])).

cnf(c_6333,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5863,c_2185])).

cnf(c_10054,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2184,c_10028])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1308,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_3406,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1308])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3673,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3406,c_40])).

cnf(c_3674,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3673])).

cnf(c_3680,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_3674])).

cnf(c_3683,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3680,c_1787])).

cnf(c_4263,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3683,c_37])).

cnf(c_10060,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_10054,c_4263])).

cnf(c_13237,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13230,c_3670,c_6333,c_10060])).

cnf(c_13529,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13237,c_2185])).

cnf(c_3424,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1916,c_1313])).

cnf(c_1367,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK0,X0_48) != sK0
    | k1_xboole_0 = sK0
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1424,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) != sK0
    | k1_xboole_0 = sK0
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_18022,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_36,c_35,c_34,c_33,c_32,c_31,c_703,c_701,c_693,c_1392,c_1402,c_1424,c_1444,c_1672,c_1748,c_2363,c_2981])).

cnf(c_25456,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_25449,c_2267,c_13529,c_18022])).

cnf(c_25,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_705,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25456,c_705])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.53/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.53/2.00  
% 11.53/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.53/2.00  
% 11.53/2.00  ------  iProver source info
% 11.53/2.00  
% 11.53/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.53/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.53/2.00  git: non_committed_changes: false
% 11.53/2.00  git: last_make_outside_of_git: false
% 11.53/2.00  
% 11.53/2.00  ------ 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options
% 11.53/2.00  
% 11.53/2.00  --out_options                           all
% 11.53/2.00  --tptp_safe_out                         true
% 11.53/2.00  --problem_path                          ""
% 11.53/2.00  --include_path                          ""
% 11.53/2.00  --clausifier                            res/vclausify_rel
% 11.53/2.00  --clausifier_options                    ""
% 11.53/2.00  --stdin                                 false
% 11.53/2.00  --stats_out                             all
% 11.53/2.00  
% 11.53/2.00  ------ General Options
% 11.53/2.00  
% 11.53/2.00  --fof                                   false
% 11.53/2.00  --time_out_real                         305.
% 11.53/2.00  --time_out_virtual                      -1.
% 11.53/2.00  --symbol_type_check                     false
% 11.53/2.00  --clausify_out                          false
% 11.53/2.00  --sig_cnt_out                           false
% 11.53/2.00  --trig_cnt_out                          false
% 11.53/2.00  --trig_cnt_out_tolerance                1.
% 11.53/2.00  --trig_cnt_out_sk_spl                   false
% 11.53/2.00  --abstr_cl_out                          false
% 11.53/2.00  
% 11.53/2.00  ------ Global Options
% 11.53/2.00  
% 11.53/2.00  --schedule                              default
% 11.53/2.00  --add_important_lit                     false
% 11.53/2.00  --prop_solver_per_cl                    1000
% 11.53/2.00  --min_unsat_core                        false
% 11.53/2.00  --soft_assumptions                      false
% 11.53/2.00  --soft_lemma_size                       3
% 11.53/2.00  --prop_impl_unit_size                   0
% 11.53/2.00  --prop_impl_unit                        []
% 11.53/2.00  --share_sel_clauses                     true
% 11.53/2.00  --reset_solvers                         false
% 11.53/2.00  --bc_imp_inh                            [conj_cone]
% 11.53/2.00  --conj_cone_tolerance                   3.
% 11.53/2.00  --extra_neg_conj                        none
% 11.53/2.00  --large_theory_mode                     true
% 11.53/2.00  --prolific_symb_bound                   200
% 11.53/2.00  --lt_threshold                          2000
% 11.53/2.00  --clause_weak_htbl                      true
% 11.53/2.00  --gc_record_bc_elim                     false
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing Options
% 11.53/2.00  
% 11.53/2.00  --preprocessing_flag                    true
% 11.53/2.00  --time_out_prep_mult                    0.1
% 11.53/2.00  --splitting_mode                        input
% 11.53/2.00  --splitting_grd                         true
% 11.53/2.00  --splitting_cvd                         false
% 11.53/2.00  --splitting_cvd_svl                     false
% 11.53/2.00  --splitting_nvd                         32
% 11.53/2.00  --sub_typing                            true
% 11.53/2.00  --prep_gs_sim                           true
% 11.53/2.00  --prep_unflatten                        true
% 11.53/2.00  --prep_res_sim                          true
% 11.53/2.00  --prep_upred                            true
% 11.53/2.00  --prep_sem_filter                       exhaustive
% 11.53/2.00  --prep_sem_filter_out                   false
% 11.53/2.00  --pred_elim                             true
% 11.53/2.00  --res_sim_input                         true
% 11.53/2.00  --eq_ax_congr_red                       true
% 11.53/2.00  --pure_diseq_elim                       true
% 11.53/2.00  --brand_transform                       false
% 11.53/2.00  --non_eq_to_eq                          false
% 11.53/2.00  --prep_def_merge                        true
% 11.53/2.00  --prep_def_merge_prop_impl              false
% 11.53/2.00  --prep_def_merge_mbd                    true
% 11.53/2.00  --prep_def_merge_tr_red                 false
% 11.53/2.00  --prep_def_merge_tr_cl                  false
% 11.53/2.00  --smt_preprocessing                     true
% 11.53/2.00  --smt_ac_axioms                         fast
% 11.53/2.00  --preprocessed_out                      false
% 11.53/2.00  --preprocessed_stats                    false
% 11.53/2.00  
% 11.53/2.00  ------ Abstraction refinement Options
% 11.53/2.00  
% 11.53/2.00  --abstr_ref                             []
% 11.53/2.00  --abstr_ref_prep                        false
% 11.53/2.00  --abstr_ref_until_sat                   false
% 11.53/2.00  --abstr_ref_sig_restrict                funpre
% 11.53/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/2.00  --abstr_ref_under                       []
% 11.53/2.00  
% 11.53/2.00  ------ SAT Options
% 11.53/2.00  
% 11.53/2.00  --sat_mode                              false
% 11.53/2.00  --sat_fm_restart_options                ""
% 11.53/2.00  --sat_gr_def                            false
% 11.53/2.00  --sat_epr_types                         true
% 11.53/2.00  --sat_non_cyclic_types                  false
% 11.53/2.00  --sat_finite_models                     false
% 11.53/2.00  --sat_fm_lemmas                         false
% 11.53/2.00  --sat_fm_prep                           false
% 11.53/2.00  --sat_fm_uc_incr                        true
% 11.53/2.00  --sat_out_model                         small
% 11.53/2.00  --sat_out_clauses                       false
% 11.53/2.00  
% 11.53/2.00  ------ QBF Options
% 11.53/2.00  
% 11.53/2.00  --qbf_mode                              false
% 11.53/2.00  --qbf_elim_univ                         false
% 11.53/2.00  --qbf_dom_inst                          none
% 11.53/2.00  --qbf_dom_pre_inst                      false
% 11.53/2.00  --qbf_sk_in                             false
% 11.53/2.00  --qbf_pred_elim                         true
% 11.53/2.00  --qbf_split                             512
% 11.53/2.00  
% 11.53/2.00  ------ BMC1 Options
% 11.53/2.00  
% 11.53/2.00  --bmc1_incremental                      false
% 11.53/2.00  --bmc1_axioms                           reachable_all
% 11.53/2.00  --bmc1_min_bound                        0
% 11.53/2.00  --bmc1_max_bound                        -1
% 11.53/2.00  --bmc1_max_bound_default                -1
% 11.53/2.00  --bmc1_symbol_reachability              true
% 11.53/2.00  --bmc1_property_lemmas                  false
% 11.53/2.00  --bmc1_k_induction                      false
% 11.53/2.00  --bmc1_non_equiv_states                 false
% 11.53/2.00  --bmc1_deadlock                         false
% 11.53/2.00  --bmc1_ucm                              false
% 11.53/2.00  --bmc1_add_unsat_core                   none
% 11.53/2.00  --bmc1_unsat_core_children              false
% 11.53/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/2.00  --bmc1_out_stat                         full
% 11.53/2.00  --bmc1_ground_init                      false
% 11.53/2.00  --bmc1_pre_inst_next_state              false
% 11.53/2.00  --bmc1_pre_inst_state                   false
% 11.53/2.00  --bmc1_pre_inst_reach_state             false
% 11.53/2.00  --bmc1_out_unsat_core                   false
% 11.53/2.00  --bmc1_aig_witness_out                  false
% 11.53/2.00  --bmc1_verbose                          false
% 11.53/2.00  --bmc1_dump_clauses_tptp                false
% 11.53/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.53/2.00  --bmc1_dump_file                        -
% 11.53/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.53/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.53/2.00  --bmc1_ucm_extend_mode                  1
% 11.53/2.00  --bmc1_ucm_init_mode                    2
% 11.53/2.00  --bmc1_ucm_cone_mode                    none
% 11.53/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.53/2.00  --bmc1_ucm_relax_model                  4
% 11.53/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.53/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/2.00  --bmc1_ucm_layered_model                none
% 11.53/2.00  --bmc1_ucm_max_lemma_size               10
% 11.53/2.00  
% 11.53/2.00  ------ AIG Options
% 11.53/2.00  
% 11.53/2.00  --aig_mode                              false
% 11.53/2.00  
% 11.53/2.00  ------ Instantiation Options
% 11.53/2.00  
% 11.53/2.00  --instantiation_flag                    true
% 11.53/2.00  --inst_sos_flag                         true
% 11.53/2.00  --inst_sos_phase                        true
% 11.53/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel_side                     num_symb
% 11.53/2.00  --inst_solver_per_active                1400
% 11.53/2.00  --inst_solver_calls_frac                1.
% 11.53/2.00  --inst_passive_queue_type               priority_queues
% 11.53/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/2.00  --inst_passive_queues_freq              [25;2]
% 11.53/2.00  --inst_dismatching                      true
% 11.53/2.00  --inst_eager_unprocessed_to_passive     true
% 11.53/2.00  --inst_prop_sim_given                   true
% 11.53/2.00  --inst_prop_sim_new                     false
% 11.53/2.00  --inst_subs_new                         false
% 11.53/2.00  --inst_eq_res_simp                      false
% 11.53/2.00  --inst_subs_given                       false
% 11.53/2.00  --inst_orphan_elimination               true
% 11.53/2.00  --inst_learning_loop_flag               true
% 11.53/2.00  --inst_learning_start                   3000
% 11.53/2.00  --inst_learning_factor                  2
% 11.53/2.00  --inst_start_prop_sim_after_learn       3
% 11.53/2.00  --inst_sel_renew                        solver
% 11.53/2.00  --inst_lit_activity_flag                true
% 11.53/2.00  --inst_restr_to_given                   false
% 11.53/2.00  --inst_activity_threshold               500
% 11.53/2.00  --inst_out_proof                        true
% 11.53/2.00  
% 11.53/2.00  ------ Resolution Options
% 11.53/2.00  
% 11.53/2.00  --resolution_flag                       true
% 11.53/2.00  --res_lit_sel                           adaptive
% 11.53/2.00  --res_lit_sel_side                      none
% 11.53/2.00  --res_ordering                          kbo
% 11.53/2.00  --res_to_prop_solver                    active
% 11.53/2.00  --res_prop_simpl_new                    false
% 11.53/2.00  --res_prop_simpl_given                  true
% 11.53/2.00  --res_passive_queue_type                priority_queues
% 11.53/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/2.00  --res_passive_queues_freq               [15;5]
% 11.53/2.00  --res_forward_subs                      full
% 11.53/2.00  --res_backward_subs                     full
% 11.53/2.00  --res_forward_subs_resolution           true
% 11.53/2.00  --res_backward_subs_resolution          true
% 11.53/2.00  --res_orphan_elimination                true
% 11.53/2.00  --res_time_limit                        2.
% 11.53/2.00  --res_out_proof                         true
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Options
% 11.53/2.00  
% 11.53/2.00  --superposition_flag                    true
% 11.53/2.00  --sup_passive_queue_type                priority_queues
% 11.53/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.53/2.00  --demod_completeness_check              fast
% 11.53/2.00  --demod_use_ground                      true
% 11.53/2.00  --sup_to_prop_solver                    passive
% 11.53/2.00  --sup_prop_simpl_new                    true
% 11.53/2.00  --sup_prop_simpl_given                  true
% 11.53/2.00  --sup_fun_splitting                     true
% 11.53/2.00  --sup_smt_interval                      50000
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Simplification Setup
% 11.53/2.00  
% 11.53/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_immed_triv                        [TrivRules]
% 11.53/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_bw_main                     []
% 11.53/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_input_bw                          []
% 11.53/2.00  
% 11.53/2.00  ------ Combination Options
% 11.53/2.00  
% 11.53/2.00  --comb_res_mult                         3
% 11.53/2.00  --comb_sup_mult                         2
% 11.53/2.00  --comb_inst_mult                        10
% 11.53/2.00  
% 11.53/2.00  ------ Debug Options
% 11.53/2.00  
% 11.53/2.00  --dbg_backtrace                         false
% 11.53/2.00  --dbg_dump_prop_clauses                 false
% 11.53/2.00  --dbg_dump_prop_clauses_file            -
% 11.53/2.00  --dbg_out_stat                          false
% 11.53/2.00  ------ Parsing...
% 11.53/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.53/2.00  ------ Proving...
% 11.53/2.00  ------ Problem Properties 
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  clauses                                 36
% 11.53/2.00  conjectures                             11
% 11.53/2.00  EPR                                     7
% 11.53/2.00  Horn                                    32
% 11.53/2.00  unary                                   14
% 11.53/2.00  binary                                  5
% 11.53/2.00  lits                                    129
% 11.53/2.00  lits eq                                 29
% 11.53/2.00  fd_pure                                 0
% 11.53/2.00  fd_pseudo                               0
% 11.53/2.00  fd_cond                                 4
% 11.53/2.00  fd_pseudo_cond                          0
% 11.53/2.00  AC symbols                              0
% 11.53/2.00  
% 11.53/2.00  ------ Schedule dynamic 5 is on 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  ------ 
% 11.53/2.00  Current options:
% 11.53/2.00  ------ 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options
% 11.53/2.00  
% 11.53/2.00  --out_options                           all
% 11.53/2.00  --tptp_safe_out                         true
% 11.53/2.00  --problem_path                          ""
% 11.53/2.00  --include_path                          ""
% 11.53/2.00  --clausifier                            res/vclausify_rel
% 11.53/2.00  --clausifier_options                    ""
% 11.53/2.00  --stdin                                 false
% 11.53/2.00  --stats_out                             all
% 11.53/2.00  
% 11.53/2.00  ------ General Options
% 11.53/2.00  
% 11.53/2.00  --fof                                   false
% 11.53/2.00  --time_out_real                         305.
% 11.53/2.00  --time_out_virtual                      -1.
% 11.53/2.00  --symbol_type_check                     false
% 11.53/2.00  --clausify_out                          false
% 11.53/2.00  --sig_cnt_out                           false
% 11.53/2.00  --trig_cnt_out                          false
% 11.53/2.00  --trig_cnt_out_tolerance                1.
% 11.53/2.00  --trig_cnt_out_sk_spl                   false
% 11.53/2.00  --abstr_cl_out                          false
% 11.53/2.00  
% 11.53/2.00  ------ Global Options
% 11.53/2.00  
% 11.53/2.00  --schedule                              default
% 11.53/2.00  --add_important_lit                     false
% 11.53/2.00  --prop_solver_per_cl                    1000
% 11.53/2.00  --min_unsat_core                        false
% 11.53/2.00  --soft_assumptions                      false
% 11.53/2.00  --soft_lemma_size                       3
% 11.53/2.00  --prop_impl_unit_size                   0
% 11.53/2.00  --prop_impl_unit                        []
% 11.53/2.00  --share_sel_clauses                     true
% 11.53/2.00  --reset_solvers                         false
% 11.53/2.00  --bc_imp_inh                            [conj_cone]
% 11.53/2.00  --conj_cone_tolerance                   3.
% 11.53/2.00  --extra_neg_conj                        none
% 11.53/2.00  --large_theory_mode                     true
% 11.53/2.00  --prolific_symb_bound                   200
% 11.53/2.00  --lt_threshold                          2000
% 11.53/2.00  --clause_weak_htbl                      true
% 11.53/2.00  --gc_record_bc_elim                     false
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing Options
% 11.53/2.00  
% 11.53/2.00  --preprocessing_flag                    true
% 11.53/2.00  --time_out_prep_mult                    0.1
% 11.53/2.00  --splitting_mode                        input
% 11.53/2.00  --splitting_grd                         true
% 11.53/2.00  --splitting_cvd                         false
% 11.53/2.00  --splitting_cvd_svl                     false
% 11.53/2.00  --splitting_nvd                         32
% 11.53/2.00  --sub_typing                            true
% 11.53/2.00  --prep_gs_sim                           true
% 11.53/2.00  --prep_unflatten                        true
% 11.53/2.00  --prep_res_sim                          true
% 11.53/2.00  --prep_upred                            true
% 11.53/2.00  --prep_sem_filter                       exhaustive
% 11.53/2.00  --prep_sem_filter_out                   false
% 11.53/2.00  --pred_elim                             true
% 11.53/2.00  --res_sim_input                         true
% 11.53/2.00  --eq_ax_congr_red                       true
% 11.53/2.00  --pure_diseq_elim                       true
% 11.53/2.00  --brand_transform                       false
% 11.53/2.00  --non_eq_to_eq                          false
% 11.53/2.00  --prep_def_merge                        true
% 11.53/2.00  --prep_def_merge_prop_impl              false
% 11.53/2.00  --prep_def_merge_mbd                    true
% 11.53/2.00  --prep_def_merge_tr_red                 false
% 11.53/2.00  --prep_def_merge_tr_cl                  false
% 11.53/2.00  --smt_preprocessing                     true
% 11.53/2.00  --smt_ac_axioms                         fast
% 11.53/2.00  --preprocessed_out                      false
% 11.53/2.00  --preprocessed_stats                    false
% 11.53/2.00  
% 11.53/2.00  ------ Abstraction refinement Options
% 11.53/2.00  
% 11.53/2.00  --abstr_ref                             []
% 11.53/2.00  --abstr_ref_prep                        false
% 11.53/2.00  --abstr_ref_until_sat                   false
% 11.53/2.00  --abstr_ref_sig_restrict                funpre
% 11.53/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/2.00  --abstr_ref_under                       []
% 11.53/2.00  
% 11.53/2.00  ------ SAT Options
% 11.53/2.00  
% 11.53/2.00  --sat_mode                              false
% 11.53/2.00  --sat_fm_restart_options                ""
% 11.53/2.00  --sat_gr_def                            false
% 11.53/2.00  --sat_epr_types                         true
% 11.53/2.00  --sat_non_cyclic_types                  false
% 11.53/2.00  --sat_finite_models                     false
% 11.53/2.00  --sat_fm_lemmas                         false
% 11.53/2.00  --sat_fm_prep                           false
% 11.53/2.00  --sat_fm_uc_incr                        true
% 11.53/2.00  --sat_out_model                         small
% 11.53/2.00  --sat_out_clauses                       false
% 11.53/2.00  
% 11.53/2.00  ------ QBF Options
% 11.53/2.00  
% 11.53/2.00  --qbf_mode                              false
% 11.53/2.00  --qbf_elim_univ                         false
% 11.53/2.00  --qbf_dom_inst                          none
% 11.53/2.00  --qbf_dom_pre_inst                      false
% 11.53/2.00  --qbf_sk_in                             false
% 11.53/2.00  --qbf_pred_elim                         true
% 11.53/2.00  --qbf_split                             512
% 11.53/2.00  
% 11.53/2.00  ------ BMC1 Options
% 11.53/2.00  
% 11.53/2.00  --bmc1_incremental                      false
% 11.53/2.00  --bmc1_axioms                           reachable_all
% 11.53/2.00  --bmc1_min_bound                        0
% 11.53/2.00  --bmc1_max_bound                        -1
% 11.53/2.00  --bmc1_max_bound_default                -1
% 11.53/2.00  --bmc1_symbol_reachability              true
% 11.53/2.00  --bmc1_property_lemmas                  false
% 11.53/2.00  --bmc1_k_induction                      false
% 11.53/2.00  --bmc1_non_equiv_states                 false
% 11.53/2.00  --bmc1_deadlock                         false
% 11.53/2.00  --bmc1_ucm                              false
% 11.53/2.00  --bmc1_add_unsat_core                   none
% 11.53/2.00  --bmc1_unsat_core_children              false
% 11.53/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/2.00  --bmc1_out_stat                         full
% 11.53/2.00  --bmc1_ground_init                      false
% 11.53/2.00  --bmc1_pre_inst_next_state              false
% 11.53/2.00  --bmc1_pre_inst_state                   false
% 11.53/2.00  --bmc1_pre_inst_reach_state             false
% 11.53/2.00  --bmc1_out_unsat_core                   false
% 11.53/2.00  --bmc1_aig_witness_out                  false
% 11.53/2.00  --bmc1_verbose                          false
% 11.53/2.00  --bmc1_dump_clauses_tptp                false
% 11.53/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.53/2.00  --bmc1_dump_file                        -
% 11.53/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.53/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.53/2.00  --bmc1_ucm_extend_mode                  1
% 11.53/2.00  --bmc1_ucm_init_mode                    2
% 11.53/2.00  --bmc1_ucm_cone_mode                    none
% 11.53/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.53/2.00  --bmc1_ucm_relax_model                  4
% 11.53/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.53/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/2.00  --bmc1_ucm_layered_model                none
% 11.53/2.00  --bmc1_ucm_max_lemma_size               10
% 11.53/2.00  
% 11.53/2.00  ------ AIG Options
% 11.53/2.00  
% 11.53/2.00  --aig_mode                              false
% 11.53/2.00  
% 11.53/2.00  ------ Instantiation Options
% 11.53/2.00  
% 11.53/2.00  --instantiation_flag                    true
% 11.53/2.00  --inst_sos_flag                         true
% 11.53/2.00  --inst_sos_phase                        true
% 11.53/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel_side                     none
% 11.53/2.00  --inst_solver_per_active                1400
% 11.53/2.00  --inst_solver_calls_frac                1.
% 11.53/2.00  --inst_passive_queue_type               priority_queues
% 11.53/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/2.00  --inst_passive_queues_freq              [25;2]
% 11.53/2.00  --inst_dismatching                      true
% 11.53/2.00  --inst_eager_unprocessed_to_passive     true
% 11.53/2.00  --inst_prop_sim_given                   true
% 11.53/2.00  --inst_prop_sim_new                     false
% 11.53/2.00  --inst_subs_new                         false
% 11.53/2.00  --inst_eq_res_simp                      false
% 11.53/2.00  --inst_subs_given                       false
% 11.53/2.00  --inst_orphan_elimination               true
% 11.53/2.00  --inst_learning_loop_flag               true
% 11.53/2.00  --inst_learning_start                   3000
% 11.53/2.00  --inst_learning_factor                  2
% 11.53/2.00  --inst_start_prop_sim_after_learn       3
% 11.53/2.00  --inst_sel_renew                        solver
% 11.53/2.00  --inst_lit_activity_flag                true
% 11.53/2.00  --inst_restr_to_given                   false
% 11.53/2.00  --inst_activity_threshold               500
% 11.53/2.00  --inst_out_proof                        true
% 11.53/2.00  
% 11.53/2.00  ------ Resolution Options
% 11.53/2.00  
% 11.53/2.00  --resolution_flag                       false
% 11.53/2.00  --res_lit_sel                           adaptive
% 11.53/2.00  --res_lit_sel_side                      none
% 11.53/2.00  --res_ordering                          kbo
% 11.53/2.00  --res_to_prop_solver                    active
% 11.53/2.00  --res_prop_simpl_new                    false
% 11.53/2.00  --res_prop_simpl_given                  true
% 11.53/2.00  --res_passive_queue_type                priority_queues
% 11.53/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/2.00  --res_passive_queues_freq               [15;5]
% 11.53/2.00  --res_forward_subs                      full
% 11.53/2.00  --res_backward_subs                     full
% 11.53/2.00  --res_forward_subs_resolution           true
% 11.53/2.00  --res_backward_subs_resolution          true
% 11.53/2.00  --res_orphan_elimination                true
% 11.53/2.00  --res_time_limit                        2.
% 11.53/2.00  --res_out_proof                         true
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Options
% 11.53/2.00  
% 11.53/2.00  --superposition_flag                    true
% 11.53/2.00  --sup_passive_queue_type                priority_queues
% 11.53/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.53/2.00  --demod_completeness_check              fast
% 11.53/2.00  --demod_use_ground                      true
% 11.53/2.00  --sup_to_prop_solver                    passive
% 11.53/2.00  --sup_prop_simpl_new                    true
% 11.53/2.00  --sup_prop_simpl_given                  true
% 11.53/2.00  --sup_fun_splitting                     true
% 11.53/2.00  --sup_smt_interval                      50000
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Simplification Setup
% 11.53/2.00  
% 11.53/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_immed_triv                        [TrivRules]
% 11.53/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_bw_main                     []
% 11.53/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_input_bw                          []
% 11.53/2.00  
% 11.53/2.00  ------ Combination Options
% 11.53/2.00  
% 11.53/2.00  --comb_res_mult                         3
% 11.53/2.00  --comb_sup_mult                         2
% 11.53/2.00  --comb_inst_mult                        10
% 11.53/2.00  
% 11.53/2.00  ------ Debug Options
% 11.53/2.00  
% 11.53/2.00  --dbg_backtrace                         false
% 11.53/2.00  --dbg_dump_prop_clauses                 false
% 11.53/2.00  --dbg_dump_prop_clauses_file            -
% 11.53/2.00  --dbg_out_stat                          false
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  ------ Proving...
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  % SZS status Theorem for theBenchmark.p
% 11.53/2.00  
% 11.53/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.53/2.00  
% 11.53/2.00  fof(f18,conjecture,(
% 11.53/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f19,negated_conjecture,(
% 11.53/2.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.53/2.00    inference(negated_conjecture,[],[f18])).
% 11.53/2.00  
% 11.53/2.00  fof(f43,plain,(
% 11.53/2.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.53/2.00    inference(ennf_transformation,[],[f19])).
% 11.53/2.00  
% 11.53/2.00  fof(f44,plain,(
% 11.53/2.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.53/2.00    inference(flattening,[],[f43])).
% 11.53/2.00  
% 11.53/2.00  fof(f47,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f46,plain,(
% 11.53/2.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f48,plain,(
% 11.53/2.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.53/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f47,f46])).
% 11.53/2.00  
% 11.53/2.00  fof(f80,plain,(
% 11.53/2.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f8,axiom,(
% 11.53/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f29,plain,(
% 11.53/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/2.00    inference(ennf_transformation,[],[f8])).
% 11.53/2.00  
% 11.53/2.00  fof(f59,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.53/2.00    inference(cnf_transformation,[],[f29])).
% 11.53/2.00  
% 11.53/2.00  fof(f78,plain,(
% 11.53/2.00    v1_funct_1(sK3)),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f4,axiom,(
% 11.53/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f23,plain,(
% 11.53/2.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/2.00    inference(ennf_transformation,[],[f4])).
% 11.53/2.00  
% 11.53/2.00  fof(f24,plain,(
% 11.53/2.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/2.00    inference(flattening,[],[f23])).
% 11.53/2.00  
% 11.53/2.00  fof(f52,plain,(
% 11.53/2.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f24])).
% 11.53/2.00  
% 11.53/2.00  fof(f1,axiom,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f20,plain,(
% 11.53/2.00    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f1])).
% 11.53/2.00  
% 11.53/2.00  fof(f49,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f20])).
% 11.53/2.00  
% 11.53/2.00  fof(f10,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f31,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.53/2.00    inference(ennf_transformation,[],[f10])).
% 11.53/2.00  
% 11.53/2.00  fof(f32,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/2.00    inference(flattening,[],[f31])).
% 11.53/2.00  
% 11.53/2.00  fof(f45,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/2.00    inference(nnf_transformation,[],[f32])).
% 11.53/2.00  
% 11.53/2.00  fof(f61,plain,(
% 11.53/2.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.53/2.00    inference(cnf_transformation,[],[f45])).
% 11.53/2.00  
% 11.53/2.00  fof(f82,plain,(
% 11.53/2.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f11,axiom,(
% 11.53/2.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f63,plain,(
% 11.53/2.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.53/2.00    inference(cnf_transformation,[],[f11])).
% 11.53/2.00  
% 11.53/2.00  fof(f14,axiom,(
% 11.53/2.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f67,plain,(
% 11.53/2.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f14])).
% 11.53/2.00  
% 11.53/2.00  fof(f91,plain,(
% 11.53/2.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.53/2.00    inference(definition_unfolding,[],[f63,f67])).
% 11.53/2.00  
% 11.53/2.00  fof(f75,plain,(
% 11.53/2.00    v1_funct_1(sK2)),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f77,plain,(
% 11.53/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f12,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f33,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.53/2.00    inference(ennf_transformation,[],[f12])).
% 11.53/2.00  
% 11.53/2.00  fof(f34,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.53/2.00    inference(flattening,[],[f33])).
% 11.53/2.00  
% 11.53/2.00  fof(f65,plain,(
% 11.53/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f34])).
% 11.53/2.00  
% 11.53/2.00  fof(f15,axiom,(
% 11.53/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f37,plain,(
% 11.53/2.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.53/2.00    inference(ennf_transformation,[],[f15])).
% 11.53/2.00  
% 11.53/2.00  fof(f38,plain,(
% 11.53/2.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.53/2.00    inference(flattening,[],[f37])).
% 11.53/2.00  
% 11.53/2.00  fof(f68,plain,(
% 11.53/2.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f38])).
% 11.53/2.00  
% 11.53/2.00  fof(f76,plain,(
% 11.53/2.00    v1_funct_2(sK2,sK0,sK1)),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f79,plain,(
% 11.53/2.00    v1_funct_2(sK3,sK1,sK0)),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f17,axiom,(
% 11.53/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f41,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.53/2.00    inference(ennf_transformation,[],[f17])).
% 11.53/2.00  
% 11.53/2.00  fof(f42,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.53/2.00    inference(flattening,[],[f41])).
% 11.53/2.00  
% 11.53/2.00  fof(f73,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f42])).
% 11.53/2.00  
% 11.53/2.00  fof(f84,plain,(
% 11.53/2.00    k1_xboole_0 != sK0),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f81,plain,(
% 11.53/2.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f16,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f39,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.53/2.00    inference(ennf_transformation,[],[f16])).
% 11.53/2.00  
% 11.53/2.00  fof(f40,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.53/2.00    inference(flattening,[],[f39])).
% 11.53/2.00  
% 11.53/2.00  fof(f71,plain,(
% 11.53/2.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f40])).
% 11.53/2.00  
% 11.53/2.00  fof(f5,axiom,(
% 11.53/2.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f55,plain,(
% 11.53/2.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.53/2.00    inference(cnf_transformation,[],[f5])).
% 11.53/2.00  
% 11.53/2.00  fof(f89,plain,(
% 11.53/2.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.53/2.00    inference(definition_unfolding,[],[f55,f67])).
% 11.53/2.00  
% 11.53/2.00  fof(f3,axiom,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f22,plain,(
% 11.53/2.00    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f3])).
% 11.53/2.00  
% 11.53/2.00  fof(f51,plain,(
% 11.53/2.00    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f22])).
% 11.53/2.00  
% 11.53/2.00  fof(f88,plain,(
% 11.53/2.00    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f51,f67])).
% 11.53/2.00  
% 11.53/2.00  fof(f9,axiom,(
% 11.53/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f30,plain,(
% 11.53/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/2.00    inference(ennf_transformation,[],[f9])).
% 11.53/2.00  
% 11.53/2.00  fof(f60,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.53/2.00    inference(cnf_transformation,[],[f30])).
% 11.53/2.00  
% 11.53/2.00  fof(f74,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f42])).
% 11.53/2.00  
% 11.53/2.00  fof(f83,plain,(
% 11.53/2.00    v2_funct_1(sK2)),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f85,plain,(
% 11.53/2.00    k1_xboole_0 != sK1),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  fof(f2,axiom,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f21,plain,(
% 11.53/2.00    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f2])).
% 11.53/2.00  
% 11.53/2.00  fof(f50,plain,(
% 11.53/2.00    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f21])).
% 11.53/2.00  
% 11.53/2.00  fof(f87,plain,(
% 11.53/2.00    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f50,f67])).
% 11.53/2.00  
% 11.53/2.00  fof(f6,axiom,(
% 11.53/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f25,plain,(
% 11.53/2.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/2.00    inference(ennf_transformation,[],[f6])).
% 11.53/2.00  
% 11.53/2.00  fof(f26,plain,(
% 11.53/2.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/2.00    inference(flattening,[],[f25])).
% 11.53/2.00  
% 11.53/2.00  fof(f56,plain,(
% 11.53/2.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f26])).
% 11.53/2.00  
% 11.53/2.00  fof(f13,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.53/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f35,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.53/2.00    inference(ennf_transformation,[],[f13])).
% 11.53/2.00  
% 11.53/2.00  fof(f36,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.53/2.00    inference(flattening,[],[f35])).
% 11.53/2.00  
% 11.53/2.00  fof(f66,plain,(
% 11.53/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f36])).
% 11.53/2.00  
% 11.53/2.00  fof(f86,plain,(
% 11.53/2.00    k2_funct_1(sK2) != sK3),
% 11.53/2.00    inference(cnf_transformation,[],[f48])).
% 11.53/2.00  
% 11.53/2.00  cnf(c_31,negated_conjecture,
% 11.53/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.53/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_700,negated_conjecture,
% 11.53/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.53/2.00      inference(subtyping,[status(esa)],[c_31]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1316,plain,
% 11.53/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_10,plain,
% 11.53/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.00      | v1_relat_1(X0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_717,plain,
% 11.53/2.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.00      | v1_relat_1(X0_48) ),
% 11.53/2.00      inference(subtyping,[status(esa)],[c_10]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1303,plain,
% 11.53/2.01      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2184,plain,
% 11.53/2.01      ( v1_relat_1(sK3) = iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1316,c_1303]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_33,negated_conjecture,
% 11.53/2.01      ( v1_funct_1(sK3) ),
% 11.53/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_698,negated_conjecture,
% 11.53/2.01      ( v1_funct_1(sK3) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_33]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1318,plain,
% 11.53/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_4,plain,
% 11.53/2.01      ( ~ v1_funct_1(X0)
% 11.53/2.01      | ~ v1_relat_1(X0)
% 11.53/2.01      | v1_relat_1(k2_funct_1(X0)) ),
% 11.53/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_723,plain,
% 11.53/2.01      ( ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_relat_1(X0_48)
% 11.53/2.01      | v1_relat_1(k2_funct_1(X0_48)) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_4]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1297,plain,
% 11.53/2.01      ( v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_0,plain,
% 11.53/2.01      ( ~ v1_relat_1(X0)
% 11.53/2.01      | ~ v1_relat_1(X1)
% 11.53/2.01      | ~ v1_relat_1(X2)
% 11.53/2.01      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 11.53/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_727,plain,
% 11.53/2.01      ( ~ v1_relat_1(X0_48)
% 11.53/2.01      | ~ v1_relat_1(X1_48)
% 11.53/2.01      | ~ v1_relat_1(X2_48)
% 11.53/2.01      | k5_relat_1(k5_relat_1(X2_48,X1_48),X0_48) = k5_relat_1(X2_48,k5_relat_1(X1_48,X0_48)) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_0]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1293,plain,
% 11.53/2.01      ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
% 11.53/2.01      | v1_relat_1(X2_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X1_48) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2768,plain,
% 11.53/2.01      ( k5_relat_1(sK3,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK3,X0_48),X1_48)
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X1_48) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_2184,c_1293]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_5012,plain,
% 11.53/2.01      ( k5_relat_1(k5_relat_1(sK3,k2_funct_1(X0_48)),X1_48) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(X0_48),X1_48))
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X1_48) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1297,c_2768]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_19923,plain,
% 11.53/2.01      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_48)
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1318,c_5012]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_13,plain,
% 11.53/2.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.53/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.53/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.53/2.01      | X3 = X2 ),
% 11.53/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_29,negated_conjecture,
% 11.53/2.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.53/2.01      inference(cnf_transformation,[],[f82]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_407,plain,
% 11.53/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | X3 = X0
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.53/2.01      | k6_partfun1(sK0) != X3
% 11.53/2.01      | sK0 != X2
% 11.53/2.01      | sK0 != X1 ),
% 11.53/2.01      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_408,plain,
% 11.53/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.53/2.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.53/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(unflattening,[status(thm)],[c_407]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_14,plain,
% 11.53/2.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.53/2.01      inference(cnf_transformation,[],[f91]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_416,plain,
% 11.53/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.53/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(forward_subsumption_resolution,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_408,c_14]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_693,plain,
% 11.53/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.53/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_416]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1323,plain,
% 11.53/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.53/2.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_36,negated_conjecture,
% 11.53/2.01      ( v1_funct_1(sK2) ),
% 11.53/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_34,negated_conjecture,
% 11.53/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.53/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_15,plain,
% 11.53/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.53/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X3) ),
% 11.53/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_714,plain,
% 11.53/2.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.01      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 11.53/2.01      | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X1_48) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_15]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1392,plain,
% 11.53/2.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.53/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.53/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.53/2.01      | ~ v1_funct_1(sK3)
% 11.53/2.01      | ~ v1_funct_1(sK2) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_714]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1787,plain,
% 11.53/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_1323,c_36,c_34,c_33,c_31,c_693,c_1392]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_18,plain,
% 11.53/2.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.53/2.01      | ~ v1_funct_2(X2,X0,X1)
% 11.53/2.01      | ~ v1_funct_2(X3,X1,X0)
% 11.53/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.53/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.53/2.01      | ~ v1_funct_1(X2)
% 11.53/2.01      | ~ v1_funct_1(X3)
% 11.53/2.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.53/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_420,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.53/2.01      | ~ v1_funct_2(X3,X2,X1)
% 11.53/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.53/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X3)
% 11.53/2.01      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.53/2.01      | k2_relset_1(X1,X2,X0) = X2
% 11.53/2.01      | k6_partfun1(X2) != k6_partfun1(sK0)
% 11.53/2.01      | sK0 != X2 ),
% 11.53/2.01      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_421,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0,X1,sK0)
% 11.53/2.01      | ~ v1_funct_2(X2,sK0,X1)
% 11.53/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.53/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X2)
% 11.53/2.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.53/2.01      | k2_relset_1(X1,sK0,X0) = sK0
% 11.53/2.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 11.53/2.01      inference(unflattening,[status(thm)],[c_420]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_507,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0,X1,sK0)
% 11.53/2.01      | ~ v1_funct_2(X2,sK0,X1)
% 11.53/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.53/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X2)
% 11.53/2.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.53/2.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 11.53/2.01      inference(equality_resolution_simp,[status(thm)],[c_421]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_692,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,sK0)
% 11.53/2.01      | ~ v1_funct_2(X1_48,sK0,X0_49)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 11.53/2.01      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X1_48)
% 11.53/2.01      | k2_relset_1(X0_49,sK0,X0_48) = sK0
% 11.53/2.01      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_507]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1324,plain,
% 11.53/2.01      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 11.53/2.01      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.53/2.01      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 11.53/2.01      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 11.53/2.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 11.53/2.01      | v1_funct_1(X1_48) != iProver_top
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1790,plain,
% 11.53/2.01      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 11.53/2.01      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k6_partfun1(sK0)
% 11.53/2.01      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 11.53/2.01      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 11.53/2.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 11.53/2.01      | v1_funct_1(X1_48) != iProver_top
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_1324,c_1787]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1794,plain,
% 11.53/2.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 11.53/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.53/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.53/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.53/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.53/2.01      | v1_funct_1(sK3) != iProver_top
% 11.53/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1787,c_1790]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_35,negated_conjecture,
% 11.53/2.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.53/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_32,negated_conjecture,
% 11.53/2.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 11.53/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1400,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,sK0,sK1)
% 11.53/2.01      | ~ v1_funct_2(sK3,sK1,sK0)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.53/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(sK3)
% 11.53/2.01      | k2_relset_1(sK1,sK0,sK3) = sK0
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_692]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1402,plain,
% 11.53/2.01      ( ~ v1_funct_2(sK3,sK1,sK0)
% 11.53/2.01      | ~ v1_funct_2(sK2,sK0,sK1)
% 11.53/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.53/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.53/2.01      | ~ v1_funct_1(sK3)
% 11.53/2.01      | ~ v1_funct_1(sK2)
% 11.53/2.01      | k2_relset_1(sK1,sK0,sK3) = sK0
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1400]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_729,plain,( X0_48 = X0_48 ),theory(equality) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1444,plain,
% 11.53/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_729]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1916,plain,
% 11.53/2.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_1794,c_36,c_35,c_34,c_33,c_32,c_31,c_1402,c_1444]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_24,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.53/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | ~ v2_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | k2_relset_1(X1,X2,X0) != X2
% 11.53/2.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.53/2.01      | k1_xboole_0 = X2 ),
% 11.53/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_706,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.01      | ~ v2_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 11.53/2.01      | k1_xboole_0 = X1_49
% 11.53/2.01      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_24]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1314,plain,
% 11.53/2.01      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 11.53/2.01      | k1_xboole_0 = X1_49
% 11.53/2.01      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
% 11.53/2.01      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 11.53/2.01      | v2_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3522,plain,
% 11.53/2.01      ( sK0 = k1_xboole_0
% 11.53/2.01      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.53/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.53/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.53/2.01      | v2_funct_1(sK3) != iProver_top
% 11.53/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1916,c_1314]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_27,negated_conjecture,
% 11.53/2.01      ( k1_xboole_0 != sK0 ),
% 11.53/2.01      inference(cnf_transformation,[],[f84]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_703,negated_conjecture,
% 11.53/2.01      ( k1_xboole_0 != sK0 ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_27]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_30,negated_conjecture,
% 11.53/2.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.53/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_701,negated_conjecture,
% 11.53/2.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_30]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1366,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,sK0)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 11.53/2.01      | ~ v2_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | k2_relset_1(X0_49,sK0,X0_48) != sK0
% 11.53/2.01      | k1_xboole_0 = sK0
% 11.53/2.01      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_706]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1436,plain,
% 11.53/2.01      ( ~ v1_funct_2(sK3,sK1,sK0)
% 11.53/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.53/2.01      | ~ v2_funct_1(sK3)
% 11.53/2.01      | ~ v1_funct_1(sK3)
% 11.53/2.01      | k2_relset_1(sK1,sK0,sK3) != sK0
% 11.53/2.01      | k1_xboole_0 = sK0
% 11.53/2.01      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1366]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_733,plain,
% 11.53/2.01      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 11.53/2.01      theory(equality) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1458,plain,
% 11.53/2.01      ( X0_48 != X1_48
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_48
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48 ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_733]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1513,plain,
% 11.53/2.01      ( X0_48 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1458]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1672,plain,
% 11.53/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 11.53/2.01      | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1513]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_20,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.53/2.01      | ~ v1_funct_2(X3,X4,X1)
% 11.53/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.53/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | v2_funct_1(X0)
% 11.53/2.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X3)
% 11.53/2.01      | k2_relset_1(X4,X1,X3) != X1
% 11.53/2.01      | k1_xboole_0 = X2 ),
% 11.53/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_710,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 11.53/2.01      | ~ v1_funct_2(X1_48,X2_49,X0_49)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.01      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49)))
% 11.53/2.01      | v2_funct_1(X0_48)
% 11.53/2.01      | ~ v2_funct_1(k1_partfun1(X2_49,X0_49,X0_49,X1_49,X1_48,X0_48))
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X1_48)
% 11.53/2.01      | k2_relset_1(X2_49,X0_49,X1_48) != X0_49
% 11.53/2.01      | k1_xboole_0 = X1_49 ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_20]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1466,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 11.53/2.01      | ~ v1_funct_2(sK3,X1_49,X2_49)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 11.53/2.01      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,sK3))
% 11.53/2.01      | v2_funct_1(sK3)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(sK3)
% 11.53/2.01      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 11.53/2.01      | k1_xboole_0 = X2_49 ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_710]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1634,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 11.53/2.01      | ~ v1_funct_2(sK3,X1_49,sK0)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,sK0)))
% 11.53/2.01      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,sK0,X0_48,sK3))
% 11.53/2.01      | v2_funct_1(sK3)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(sK3)
% 11.53/2.01      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 11.53/2.01      | k1_xboole_0 = sK0 ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1466]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1748,plain,
% 11.53/2.01      ( ~ v1_funct_2(sK3,sK1,sK0)
% 11.53/2.01      | ~ v1_funct_2(sK2,sK0,sK1)
% 11.53/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.53/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.53/2.01      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 11.53/2.01      | v2_funct_1(sK3)
% 11.53/2.01      | ~ v1_funct_1(sK3)
% 11.53/2.01      | ~ v1_funct_1(sK2)
% 11.53/2.01      | k2_relset_1(sK0,sK1,sK2) != sK1
% 11.53/2.01      | k1_xboole_0 = sK0 ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1634]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_742,plain,
% 11.53/2.01      ( ~ v2_funct_1(X0_48) | v2_funct_1(X1_48) | X1_48 != X0_48 ),
% 11.53/2.01      theory(equality) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1858,plain,
% 11.53/2.01      ( ~ v2_funct_1(X0_48)
% 11.53/2.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_48 ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_742]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2363,plain,
% 11.53/2.01      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 11.53/2.01      | ~ v2_funct_1(k6_partfun1(sK0))
% 11.53/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1858]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_5,plain,
% 11.53/2.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.53/2.01      inference(cnf_transformation,[],[f89]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_722,plain,
% 11.53/2.01      ( v2_funct_1(k6_partfun1(X0_49)) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_5]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2981,plain,
% 11.53/2.01      ( v2_funct_1(k6_partfun1(sK0)) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_722]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_18666,plain,
% 11.53/2.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_3522,c_36,c_35,c_34,c_33,c_32,c_31,c_703,c_701,c_693,
% 11.53/2.01                 c_1392,c_1402,c_1436,c_1444,c_1672,c_1748,c_2363,c_2981]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_19932,plain,
% 11.53/2.01      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_19923,c_18666]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_25440,plain,
% 11.53/2.01      ( v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_19932,c_2184]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_25441,plain,
% 11.53/2.01      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(renaming,[status(thm)],[c_25440]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_25449,plain,
% 11.53/2.01      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_2184,c_25441]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2,plain,
% 11.53/2.01      ( ~ v1_relat_1(X0)
% 11.53/2.01      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 11.53/2.01      inference(cnf_transformation,[],[f88]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_725,plain,
% 11.53/2.01      ( ~ v1_relat_1(X0_48)
% 11.53/2.01      | k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48 ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_2]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1295,plain,
% 11.53/2.01      ( k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2265,plain,
% 11.53/2.01      ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_2184,c_1295]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_11,plain,
% 11.53/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.53/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_716,plain,
% 11.53/2.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.01      | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_11]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1304,plain,
% 11.53/2.01      ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2218,plain,
% 11.53/2.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1316,c_1304]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2222,plain,
% 11.53/2.01      ( k2_relat_1(sK3) = sK0 ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_2218,c_1916]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2267,plain,
% 11.53/2.01      ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_2265,c_2222]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_695,negated_conjecture,
% 11.53/2.01      ( v1_funct_1(sK2) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_36]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1321,plain,
% 11.53/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_697,negated_conjecture,
% 11.53/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_34]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1319,plain,
% 11.53/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2185,plain,
% 11.53/2.01      ( v1_relat_1(sK2) = iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1319,c_1303]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2766,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(X0_48),k5_relat_1(X1_48,X2_48)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_48),X1_48),X2_48)
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X2_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X1_48) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1297,c_1293]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_9252,plain,
% 11.53/2.01      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_48),X1_48) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_48,X1_48))
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X1_48) != iProver_top
% 11.53/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1321,c_2766]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_10017,plain,
% 11.53/2.01      ( v1_relat_1(X1_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_48),X1_48) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_48,X1_48)) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_9252,c_2185]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_10018,plain,
% 11.53/2.01      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_48),X1_48) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_48,X1_48))
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X1_48) != iProver_top ),
% 11.53/2.01      inference(renaming,[status(thm)],[c_10017]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_10023,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_48)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_48)
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_2185,c_10018]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_23,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.53/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | ~ v2_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | k2_relset_1(X1,X2,X0) != X2
% 11.53/2.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 11.53/2.01      | k1_xboole_0 = X2 ),
% 11.53/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_707,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.01      | ~ v2_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 11.53/2.01      | k1_xboole_0 = X1_49
% 11.53/2.01      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_23]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1313,plain,
% 11.53/2.01      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 11.53/2.01      | k1_xboole_0 = X1_49
% 11.53/2.01      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49)
% 11.53/2.01      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 11.53/2.01      | v2_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3423,plain,
% 11.53/2.01      ( sK1 = k1_xboole_0
% 11.53/2.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 11.53/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.53/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.53/2.01      | v2_funct_1(sK2) != iProver_top
% 11.53/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_701,c_1313]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_28,negated_conjecture,
% 11.53/2.01      ( v2_funct_1(sK2) ),
% 11.53/2.01      inference(cnf_transformation,[],[f83]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_26,negated_conjecture,
% 11.53/2.01      ( k1_xboole_0 != sK1 ),
% 11.53/2.01      inference(cnf_transformation,[],[f85]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_704,negated_conjecture,
% 11.53/2.01      ( k1_xboole_0 != sK1 ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_26]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1379,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,sK1)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
% 11.53/2.01      | ~ v2_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | k2_relset_1(X0_49,sK1,X0_48) != sK1
% 11.53/2.01      | k1_xboole_0 = sK1
% 11.53/2.01      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(sK1) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_707]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1428,plain,
% 11.53/2.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 11.53/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.53/2.01      | ~ v2_funct_1(sK2)
% 11.53/2.01      | ~ v1_funct_1(sK2)
% 11.53/2.01      | k2_relset_1(sK0,sK1,sK2) != sK1
% 11.53/2.01      | k1_xboole_0 = sK1
% 11.53/2.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1379]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3518,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_3423,c_36,c_35,c_34,c_28,c_704,c_701,c_1428]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_10028,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_10023,c_3518]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_10052,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(X0_48))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(X0_48))
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1297,c_10028]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_13230,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
% 11.53/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1321,c_10052]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3521,plain,
% 11.53/2.01      ( sK1 = k1_xboole_0
% 11.53/2.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 11.53/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.53/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.53/2.01      | v2_funct_1(sK2) != iProver_top
% 11.53/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_701,c_1314]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1378,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,sK1)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
% 11.53/2.01      | ~ v2_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | k2_relset_1(X0_49,sK1,X0_48) != sK1
% 11.53/2.01      | k1_xboole_0 = sK1
% 11.53/2.01      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_706]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1440,plain,
% 11.53/2.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 11.53/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.53/2.01      | ~ v2_funct_1(sK2)
% 11.53/2.01      | ~ v1_funct_1(sK2)
% 11.53/2.01      | k2_relset_1(sK0,sK1,sK2) != sK1
% 11.53/2.01      | k1_xboole_0 = sK1
% 11.53/2.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1378]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3670,plain,
% 11.53/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_3521,c_36,c_35,c_34,c_28,c_704,c_701,c_1440]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1,plain,
% 11.53/2.01      ( ~ v1_relat_1(X0)
% 11.53/2.01      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 11.53/2.01      inference(cnf_transformation,[],[f87]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_726,plain,
% 11.53/2.01      ( ~ v1_relat_1(X0_48)
% 11.53/2.01      | k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48 ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_1]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1294,plain,
% 11.53/2.01      ( k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2191,plain,
% 11.53/2.01      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0_48))),k2_funct_1(X0_48)) = k2_funct_1(X0_48)
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1297,c_1294]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_5858,plain,
% 11.53/2.01      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2)
% 11.53/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1321,c_2191]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_702,negated_conjecture,
% 11.53/2.01      ( v2_funct_1(sK2) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_28]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1315,plain,
% 11.53/2.01      ( v2_funct_1(sK2) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_8,plain,
% 11.53/2.01      ( ~ v2_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | ~ v1_relat_1(X0)
% 11.53/2.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.53/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_719,plain,
% 11.53/2.01      ( ~ v2_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_relat_1(X0_48)
% 11.53/2.01      | k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_8]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1301,plain,
% 11.53/2.01      ( k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48)
% 11.53/2.01      | v2_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_relat_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2757,plain,
% 11.53/2.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.53/2.01      | v1_funct_1(sK2) != iProver_top
% 11.53/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1315,c_1301]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2219,plain,
% 11.53/2.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1319,c_1304]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2221,plain,
% 11.53/2.01      ( k2_relat_1(sK2) = sK1 ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_2219,c_701]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2759,plain,
% 11.53/2.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 11.53/2.01      | v1_funct_1(sK2) != iProver_top
% 11.53/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_2757,c_2221]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_37,plain,
% 11.53/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3051,plain,
% 11.53/2.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_2759,c_37,c_2185]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_5863,plain,
% 11.53/2.01      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2)
% 11.53/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_5858,c_3051]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_6333,plain,
% 11.53/2.01      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_5863,c_2185]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_10054,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_2184,c_10028]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_17,plain,
% 11.53/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.53/2.01      | ~ v1_funct_1(X0)
% 11.53/2.01      | ~ v1_funct_1(X3)
% 11.53/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.53/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_712,plain,
% 11.53/2.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 11.53/2.01      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X1_48)
% 11.53/2.01      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_17]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1308,plain,
% 11.53/2.01      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 11.53/2.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_funct_1(X1_48) != iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3406,plain,
% 11.53/2.01      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1316,c_1308]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_40,plain,
% 11.53/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3673,plain,
% 11.53/2.01      ( v1_funct_1(X0_48) != iProver_top
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 11.53/2.01      | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_3406,c_40]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3674,plain,
% 11.53/2.01      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 11.53/2.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 11.53/2.01      | v1_funct_1(X0_48) != iProver_top ),
% 11.53/2.01      inference(renaming,[status(thm)],[c_3673]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3680,plain,
% 11.53/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.53/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1319,c_3674]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3683,plain,
% 11.53/2.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.53/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_3680,c_1787]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_4263,plain,
% 11.53/2.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_3683,c_37]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_10060,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.53/2.01      inference(light_normalisation,[status(thm)],[c_10054,c_4263]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_13237,plain,
% 11.53/2.01      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2)
% 11.53/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.53/2.01      inference(light_normalisation,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_13230,c_3670,c_6333,c_10060]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_13529,plain,
% 11.53/2.01      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_13237,c_2185]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3424,plain,
% 11.53/2.01      ( sK0 = k1_xboole_0
% 11.53/2.01      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
% 11.53/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.53/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.53/2.01      | v2_funct_1(sK3) != iProver_top
% 11.53/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_1916,c_1313]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1367,plain,
% 11.53/2.01      ( ~ v1_funct_2(X0_48,X0_49,sK0)
% 11.53/2.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 11.53/2.01      | ~ v2_funct_1(X0_48)
% 11.53/2.01      | ~ v1_funct_1(X0_48)
% 11.53/2.01      | k2_relset_1(X0_49,sK0,X0_48) != sK0
% 11.53/2.01      | k1_xboole_0 = sK0
% 11.53/2.01      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(sK0) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_707]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_1424,plain,
% 11.53/2.01      ( ~ v1_funct_2(sK3,sK1,sK0)
% 11.53/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.53/2.01      | ~ v2_funct_1(sK3)
% 11.53/2.01      | ~ v1_funct_1(sK3)
% 11.53/2.01      | k2_relset_1(sK1,sK0,sK3) != sK0
% 11.53/2.01      | k1_xboole_0 = sK0
% 11.53/2.01      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
% 11.53/2.01      inference(instantiation,[status(thm)],[c_1367]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_18022,plain,
% 11.53/2.01      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_3424,c_36,c_35,c_34,c_33,c_32,c_31,c_703,c_701,c_693,
% 11.53/2.01                 c_1392,c_1402,c_1424,c_1444,c_1672,c_1748,c_2363,c_2981]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_25456,plain,
% 11.53/2.01      ( k2_funct_1(sK2) = sK3 ),
% 11.53/2.01      inference(light_normalisation,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_25449,c_2267,c_13529,c_18022]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_25,negated_conjecture,
% 11.53/2.01      ( k2_funct_1(sK2) != sK3 ),
% 11.53/2.01      inference(cnf_transformation,[],[f86]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_705,negated_conjecture,
% 11.53/2.01      ( k2_funct_1(sK2) != sK3 ),
% 11.53/2.01      inference(subtyping,[status(esa)],[c_25]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(contradiction,plain,
% 11.53/2.01      ( $false ),
% 11.53/2.01      inference(minisat,[status(thm)],[c_25456,c_705]) ).
% 11.53/2.01  
% 11.53/2.01  
% 11.53/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.53/2.01  
% 11.53/2.01  ------                               Statistics
% 11.53/2.01  
% 11.53/2.01  ------ General
% 11.53/2.01  
% 11.53/2.01  abstr_ref_over_cycles:                  0
% 11.53/2.01  abstr_ref_under_cycles:                 0
% 11.53/2.01  gc_basic_clause_elim:                   0
% 11.53/2.01  forced_gc_time:                         0
% 11.53/2.01  parsing_time:                           0.017
% 11.53/2.01  unif_index_cands_time:                  0.
% 11.53/2.01  unif_index_add_time:                    0.
% 11.53/2.01  orderings_time:                         0.
% 11.53/2.01  out_proof_time:                         0.02
% 11.53/2.01  total_time:                             1.051
% 11.53/2.01  num_of_symbols:                         55
% 11.53/2.01  num_of_terms:                           35555
% 11.53/2.01  
% 11.53/2.01  ------ Preprocessing
% 11.53/2.01  
% 11.53/2.01  num_of_splits:                          0
% 11.53/2.01  num_of_split_atoms:                     0
% 11.53/2.01  num_of_reused_defs:                     0
% 11.53/2.01  num_eq_ax_congr_red:                    0
% 11.53/2.01  num_of_sem_filtered_clauses:            1
% 11.53/2.01  num_of_subtypes:                        4
% 11.53/2.01  monotx_restored_types:                  1
% 11.53/2.01  sat_num_of_epr_types:                   0
% 11.53/2.01  sat_num_of_non_cyclic_types:            0
% 11.53/2.01  sat_guarded_non_collapsed_types:        2
% 11.53/2.01  num_pure_diseq_elim:                    0
% 11.53/2.01  simp_replaced_by:                       0
% 11.53/2.01  res_preprocessed:                       186
% 11.53/2.01  prep_upred:                             0
% 11.53/2.01  prep_unflattend:                        12
% 11.53/2.01  smt_new_axioms:                         0
% 11.53/2.01  pred_elim_cands:                        5
% 11.53/2.01  pred_elim:                              1
% 11.53/2.01  pred_elim_cl:                           1
% 11.53/2.01  pred_elim_cycles:                       3
% 11.53/2.01  merged_defs:                            0
% 11.53/2.01  merged_defs_ncl:                        0
% 11.53/2.01  bin_hyper_res:                          0
% 11.53/2.01  prep_cycles:                            4
% 11.53/2.01  pred_elim_time:                         0.005
% 11.53/2.01  splitting_time:                         0.
% 11.53/2.01  sem_filter_time:                        0.
% 11.53/2.01  monotx_time:                            0.001
% 11.53/2.01  subtype_inf_time:                       0.002
% 11.53/2.01  
% 11.53/2.01  ------ Problem properties
% 11.53/2.01  
% 11.53/2.01  clauses:                                36
% 11.53/2.01  conjectures:                            11
% 11.53/2.01  epr:                                    7
% 11.53/2.01  horn:                                   32
% 11.53/2.01  ground:                                 12
% 11.53/2.01  unary:                                  14
% 11.53/2.01  binary:                                 5
% 11.53/2.01  lits:                                   129
% 11.53/2.01  lits_eq:                                29
% 11.53/2.01  fd_pure:                                0
% 11.53/2.01  fd_pseudo:                              0
% 11.53/2.01  fd_cond:                                4
% 11.53/2.01  fd_pseudo_cond:                         0
% 11.53/2.01  ac_symbols:                             0
% 11.53/2.01  
% 11.53/2.01  ------ Propositional Solver
% 11.53/2.01  
% 11.53/2.01  prop_solver_calls:                      33
% 11.53/2.01  prop_fast_solver_calls:                 2231
% 11.53/2.01  smt_solver_calls:                       0
% 11.53/2.01  smt_fast_solver_calls:                  0
% 11.53/2.01  prop_num_of_clauses:                    12737
% 11.53/2.01  prop_preprocess_simplified:             23551
% 11.53/2.01  prop_fo_subsumed:                       165
% 11.53/2.01  prop_solver_time:                       0.
% 11.53/2.01  smt_solver_time:                        0.
% 11.53/2.01  smt_fast_solver_time:                   0.
% 11.53/2.01  prop_fast_solver_time:                  0.
% 11.53/2.01  prop_unsat_core_time:                   0.002
% 11.53/2.01  
% 11.53/2.01  ------ QBF
% 11.53/2.01  
% 11.53/2.01  qbf_q_res:                              0
% 11.53/2.01  qbf_num_tautologies:                    0
% 11.53/2.01  qbf_prep_cycles:                        0
% 11.53/2.01  
% 11.53/2.01  ------ BMC1
% 11.53/2.01  
% 11.53/2.01  bmc1_current_bound:                     -1
% 11.53/2.01  bmc1_last_solved_bound:                 -1
% 11.53/2.01  bmc1_unsat_core_size:                   -1
% 11.53/2.01  bmc1_unsat_core_parents_size:           -1
% 11.53/2.01  bmc1_merge_next_fun:                    0
% 11.53/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.53/2.01  
% 11.53/2.01  ------ Instantiation
% 11.53/2.01  
% 11.53/2.01  inst_num_of_clauses:                    3943
% 11.53/2.01  inst_num_in_passive:                    486
% 11.53/2.01  inst_num_in_active:                     1636
% 11.53/2.01  inst_num_in_unprocessed:                1821
% 11.53/2.01  inst_num_of_loops:                      1720
% 11.53/2.01  inst_num_of_learning_restarts:          0
% 11.53/2.01  inst_num_moves_active_passive:          77
% 11.53/2.01  inst_lit_activity:                      0
% 11.53/2.01  inst_lit_activity_moves:                0
% 11.53/2.01  inst_num_tautologies:                   0
% 11.53/2.01  inst_num_prop_implied:                  0
% 11.53/2.01  inst_num_existing_simplified:           0
% 11.53/2.01  inst_num_eq_res_simplified:             0
% 11.53/2.01  inst_num_child_elim:                    0
% 11.53/2.01  inst_num_of_dismatching_blockings:      914
% 11.53/2.01  inst_num_of_non_proper_insts:           3517
% 11.53/2.01  inst_num_of_duplicates:                 0
% 11.53/2.01  inst_inst_num_from_inst_to_res:         0
% 11.53/2.01  inst_dismatching_checking_time:         0.
% 11.53/2.01  
% 11.53/2.01  ------ Resolution
% 11.53/2.01  
% 11.53/2.01  res_num_of_clauses:                     0
% 11.53/2.01  res_num_in_passive:                     0
% 11.53/2.01  res_num_in_active:                      0
% 11.53/2.01  res_num_of_loops:                       190
% 11.53/2.01  res_forward_subset_subsumed:            578
% 11.53/2.01  res_backward_subset_subsumed:           2
% 11.53/2.01  res_forward_subsumed:                   0
% 11.53/2.01  res_backward_subsumed:                  0
% 11.53/2.01  res_forward_subsumption_resolution:     2
% 11.53/2.01  res_backward_subsumption_resolution:    0
% 11.53/2.01  res_clause_to_clause_subsumption:       1707
% 11.53/2.01  res_orphan_elimination:                 0
% 11.53/2.01  res_tautology_del:                      196
% 11.53/2.01  res_num_eq_res_simplified:              1
% 11.53/2.01  res_num_sel_changes:                    0
% 11.53/2.01  res_moves_from_active_to_pass:          0
% 11.53/2.01  
% 11.53/2.01  ------ Superposition
% 11.53/2.01  
% 11.53/2.01  sup_time_total:                         0.
% 11.53/2.01  sup_time_generating:                    0.
% 11.53/2.01  sup_time_sim_full:                      0.
% 11.53/2.01  sup_time_sim_immed:                     0.
% 11.53/2.01  
% 11.53/2.01  sup_num_of_clauses:                     749
% 11.53/2.01  sup_num_in_active:                      319
% 11.53/2.01  sup_num_in_passive:                     430
% 11.53/2.01  sup_num_of_loops:                       343
% 11.53/2.01  sup_fw_superposition:                   659
% 11.53/2.01  sup_bw_superposition:                   160
% 11.53/2.01  sup_immediate_simplified:               243
% 11.53/2.01  sup_given_eliminated:                   0
% 11.53/2.01  comparisons_done:                       0
% 11.53/2.01  comparisons_avoided:                    0
% 11.53/2.01  
% 11.53/2.01  ------ Simplifications
% 11.53/2.01  
% 11.53/2.01  
% 11.53/2.01  sim_fw_subset_subsumed:                 15
% 11.53/2.01  sim_bw_subset_subsumed:                 12
% 11.53/2.01  sim_fw_subsumed:                        12
% 11.53/2.01  sim_bw_subsumed:                        3
% 11.53/2.01  sim_fw_subsumption_res:                 0
% 11.53/2.01  sim_bw_subsumption_res:                 0
% 11.53/2.01  sim_tautology_del:                      2
% 11.53/2.01  sim_eq_tautology_del:                   44
% 11.53/2.01  sim_eq_res_simp:                        0
% 11.53/2.01  sim_fw_demodulated:                     26
% 11.53/2.01  sim_bw_demodulated:                     23
% 11.53/2.01  sim_light_normalised:                   225
% 11.53/2.01  sim_joinable_taut:                      0
% 11.53/2.01  sim_joinable_simp:                      0
% 11.53/2.01  sim_ac_normalised:                      0
% 11.53/2.01  sim_smt_subsumption:                    0
% 11.53/2.01  
%------------------------------------------------------------------------------
