%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:08 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 534 expanded)
%              Number of clauses        :   94 ( 165 expanded)
%              Number of leaves         :   14 ( 131 expanded)
%              Depth                    :   20
%              Number of atoms          :  542 (4565 expanded)
%              Number of equality atoms :  265 (1687 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f34,f33])).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_311,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_8,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_319,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_311,c_8])).

cnf(c_564,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_319])).

cnf(c_923,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_567,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_920,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_569,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_918,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_917,plain,
    ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_2221,plain,
    ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_917])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3214,plain,
    ( v1_funct_1(X2_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2221,c_31])).

cnf(c_3215,plain,
    ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3214])).

cnf(c_3224,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_3215])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1165,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3_50,X4_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1_50,X2_50,X3_50,X4_50,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_1303,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2_50,X3_50,X0_50,X1_50,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_1799,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0_50,X1_50,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_2807,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_4681,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3224,c_27,c_25,c_24,c_22,c_2807])).

cnf(c_4829,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_923,c_4681])).

cnf(c_4830,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4829,c_4681])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_915,plain,
    ( k4_relset_1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_2179,plain,
    ( k4_relset_1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_915])).

cnf(c_2378,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_920,c_2179])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_912,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50))) != iProver_top
    | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_2568,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_912])).

cnf(c_4834,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4830,c_30,c_33,c_2568])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_271,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_relat_1(X0) != k1_relat_1(X1)
    | k2_funct_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_272,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_276,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(X0)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_27])).

cnf(c_277,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_565,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0_50)
    | k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0_50)
    | k2_funct_1(sK2) = X0_50 ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_922,plain,
    ( k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0_50)
    | k2_funct_1(sK2) = X0_50
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_635,plain,
    ( k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0_50)
    | k2_funct_1(sK2) = X0_50
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1068,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_1069,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_3454,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | k2_funct_1(sK2) = X0_50
    | k2_relat_1(sK2) != k1_relat_1(X0_50)
    | k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_922,c_30,c_635,c_1069])).

cnf(c_3455,plain,
    ( k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0_50)
    | k2_funct_1(sK2) = X0_50
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3454])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k1_relset_1(X1_50,X2_50,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_913,plain,
    ( k1_relset_1(X0_50,X1_50,X2_50) = k1_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_1338,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_920,c_913])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_413,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_25,c_17])).

cnf(c_558,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_413])).

cnf(c_1343,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1338,c_558])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_914,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_1962,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_920,c_914])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_570,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1974,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1962,c_570])).

cnf(c_3460,plain,
    ( k5_relat_1(sK2,X0_50) != k6_partfun1(sK0)
    | k1_relat_1(X0_50) != sK1
    | k2_funct_1(sK2) = X0_50
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3455,c_1343,c_1974])).

cnf(c_4842,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK2) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4834,c_3460])).

cnf(c_1337,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_918,c_913])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_403,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_405,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_22,c_18])).

cnf(c_559,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_1346,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1337,c_559])).

cnf(c_4843,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 != sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4842,c_1346])).

cnf(c_4844,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4843])).

cnf(c_1065,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_1066,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(c_16,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_573,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4844,c_1066,c_573,c_33,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:20:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.86/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.00  
% 2.86/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.86/1.00  
% 2.86/1.00  ------  iProver source info
% 2.86/1.00  
% 2.86/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.86/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.86/1.00  git: non_committed_changes: false
% 2.86/1.00  git: last_make_outside_of_git: false
% 2.86/1.00  
% 2.86/1.00  ------ 
% 2.86/1.00  
% 2.86/1.00  ------ Input Options
% 2.86/1.00  
% 2.86/1.00  --out_options                           all
% 2.86/1.00  --tptp_safe_out                         true
% 2.86/1.00  --problem_path                          ""
% 2.86/1.00  --include_path                          ""
% 2.86/1.00  --clausifier                            res/vclausify_rel
% 2.86/1.00  --clausifier_options                    --mode clausify
% 2.86/1.00  --stdin                                 false
% 2.86/1.00  --stats_out                             all
% 2.86/1.00  
% 2.86/1.00  ------ General Options
% 2.86/1.00  
% 2.86/1.00  --fof                                   false
% 2.86/1.00  --time_out_real                         305.
% 2.86/1.00  --time_out_virtual                      -1.
% 2.86/1.00  --symbol_type_check                     false
% 2.86/1.00  --clausify_out                          false
% 2.86/1.00  --sig_cnt_out                           false
% 2.86/1.00  --trig_cnt_out                          false
% 2.86/1.00  --trig_cnt_out_tolerance                1.
% 2.86/1.00  --trig_cnt_out_sk_spl                   false
% 2.86/1.00  --abstr_cl_out                          false
% 2.86/1.00  
% 2.86/1.00  ------ Global Options
% 2.86/1.00  
% 2.86/1.00  --schedule                              default
% 2.86/1.00  --add_important_lit                     false
% 2.86/1.00  --prop_solver_per_cl                    1000
% 2.86/1.00  --min_unsat_core                        false
% 2.86/1.00  --soft_assumptions                      false
% 2.86/1.00  --soft_lemma_size                       3
% 2.86/1.00  --prop_impl_unit_size                   0
% 2.86/1.00  --prop_impl_unit                        []
% 2.86/1.00  --share_sel_clauses                     true
% 2.86/1.00  --reset_solvers                         false
% 2.86/1.00  --bc_imp_inh                            [conj_cone]
% 2.86/1.00  --conj_cone_tolerance                   3.
% 2.86/1.00  --extra_neg_conj                        none
% 2.86/1.00  --large_theory_mode                     true
% 2.86/1.00  --prolific_symb_bound                   200
% 2.86/1.00  --lt_threshold                          2000
% 2.86/1.00  --clause_weak_htbl                      true
% 2.86/1.00  --gc_record_bc_elim                     false
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing Options
% 2.86/1.00  
% 2.86/1.00  --preprocessing_flag                    true
% 2.86/1.00  --time_out_prep_mult                    0.1
% 2.86/1.00  --splitting_mode                        input
% 2.86/1.00  --splitting_grd                         true
% 2.86/1.00  --splitting_cvd                         false
% 2.86/1.00  --splitting_cvd_svl                     false
% 2.86/1.00  --splitting_nvd                         32
% 2.86/1.00  --sub_typing                            true
% 2.86/1.00  --prep_gs_sim                           true
% 2.86/1.00  --prep_unflatten                        true
% 2.86/1.00  --prep_res_sim                          true
% 2.86/1.00  --prep_upred                            true
% 2.86/1.00  --prep_sem_filter                       exhaustive
% 2.86/1.00  --prep_sem_filter_out                   false
% 2.86/1.00  --pred_elim                             true
% 2.86/1.00  --res_sim_input                         true
% 2.86/1.00  --eq_ax_congr_red                       true
% 2.86/1.00  --pure_diseq_elim                       true
% 2.86/1.00  --brand_transform                       false
% 2.86/1.00  --non_eq_to_eq                          false
% 2.86/1.00  --prep_def_merge                        true
% 2.86/1.00  --prep_def_merge_prop_impl              false
% 2.86/1.00  --prep_def_merge_mbd                    true
% 2.86/1.00  --prep_def_merge_tr_red                 false
% 2.86/1.00  --prep_def_merge_tr_cl                  false
% 2.86/1.00  --smt_preprocessing                     true
% 2.86/1.00  --smt_ac_axioms                         fast
% 2.86/1.00  --preprocessed_out                      false
% 2.86/1.00  --preprocessed_stats                    false
% 2.86/1.00  
% 2.86/1.00  ------ Abstraction refinement Options
% 2.86/1.00  
% 2.86/1.00  --abstr_ref                             []
% 2.86/1.00  --abstr_ref_prep                        false
% 2.86/1.00  --abstr_ref_until_sat                   false
% 2.86/1.00  --abstr_ref_sig_restrict                funpre
% 2.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/1.00  --abstr_ref_under                       []
% 2.86/1.00  
% 2.86/1.00  ------ SAT Options
% 2.86/1.00  
% 2.86/1.00  --sat_mode                              false
% 2.86/1.00  --sat_fm_restart_options                ""
% 2.86/1.00  --sat_gr_def                            false
% 2.86/1.00  --sat_epr_types                         true
% 2.86/1.00  --sat_non_cyclic_types                  false
% 2.86/1.00  --sat_finite_models                     false
% 2.86/1.00  --sat_fm_lemmas                         false
% 2.86/1.00  --sat_fm_prep                           false
% 2.86/1.00  --sat_fm_uc_incr                        true
% 2.86/1.00  --sat_out_model                         small
% 2.86/1.00  --sat_out_clauses                       false
% 2.86/1.00  
% 2.86/1.00  ------ QBF Options
% 2.86/1.00  
% 2.86/1.00  --qbf_mode                              false
% 2.86/1.00  --qbf_elim_univ                         false
% 2.86/1.00  --qbf_dom_inst                          none
% 2.86/1.00  --qbf_dom_pre_inst                      false
% 2.86/1.00  --qbf_sk_in                             false
% 2.86/1.00  --qbf_pred_elim                         true
% 2.86/1.00  --qbf_split                             512
% 2.86/1.00  
% 2.86/1.00  ------ BMC1 Options
% 2.86/1.00  
% 2.86/1.00  --bmc1_incremental                      false
% 2.86/1.00  --bmc1_axioms                           reachable_all
% 2.86/1.00  --bmc1_min_bound                        0
% 2.86/1.00  --bmc1_max_bound                        -1
% 2.86/1.00  --bmc1_max_bound_default                -1
% 2.86/1.00  --bmc1_symbol_reachability              true
% 2.86/1.00  --bmc1_property_lemmas                  false
% 2.86/1.00  --bmc1_k_induction                      false
% 2.86/1.00  --bmc1_non_equiv_states                 false
% 2.86/1.00  --bmc1_deadlock                         false
% 2.86/1.00  --bmc1_ucm                              false
% 2.86/1.00  --bmc1_add_unsat_core                   none
% 2.86/1.00  --bmc1_unsat_core_children              false
% 2.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/1.00  --bmc1_out_stat                         full
% 2.86/1.00  --bmc1_ground_init                      false
% 2.86/1.00  --bmc1_pre_inst_next_state              false
% 2.86/1.00  --bmc1_pre_inst_state                   false
% 2.86/1.00  --bmc1_pre_inst_reach_state             false
% 2.86/1.00  --bmc1_out_unsat_core                   false
% 2.86/1.00  --bmc1_aig_witness_out                  false
% 2.86/1.00  --bmc1_verbose                          false
% 2.86/1.00  --bmc1_dump_clauses_tptp                false
% 2.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.86/1.00  --bmc1_dump_file                        -
% 2.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.86/1.00  --bmc1_ucm_extend_mode                  1
% 2.86/1.00  --bmc1_ucm_init_mode                    2
% 2.86/1.00  --bmc1_ucm_cone_mode                    none
% 2.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.86/1.00  --bmc1_ucm_relax_model                  4
% 2.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/1.00  --bmc1_ucm_layered_model                none
% 2.86/1.00  --bmc1_ucm_max_lemma_size               10
% 2.86/1.00  
% 2.86/1.00  ------ AIG Options
% 2.86/1.00  
% 2.86/1.00  --aig_mode                              false
% 2.86/1.00  
% 2.86/1.00  ------ Instantiation Options
% 2.86/1.00  
% 2.86/1.00  --instantiation_flag                    true
% 2.86/1.00  --inst_sos_flag                         false
% 2.86/1.00  --inst_sos_phase                        true
% 2.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/1.00  --inst_lit_sel_side                     num_symb
% 2.86/1.00  --inst_solver_per_active                1400
% 2.86/1.00  --inst_solver_calls_frac                1.
% 2.86/1.00  --inst_passive_queue_type               priority_queues
% 2.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/1.00  --inst_passive_queues_freq              [25;2]
% 2.86/1.00  --inst_dismatching                      true
% 2.86/1.00  --inst_eager_unprocessed_to_passive     true
% 2.86/1.00  --inst_prop_sim_given                   true
% 2.86/1.00  --inst_prop_sim_new                     false
% 2.86/1.00  --inst_subs_new                         false
% 2.86/1.00  --inst_eq_res_simp                      false
% 2.86/1.00  --inst_subs_given                       false
% 2.86/1.00  --inst_orphan_elimination               true
% 2.86/1.00  --inst_learning_loop_flag               true
% 2.86/1.00  --inst_learning_start                   3000
% 2.86/1.00  --inst_learning_factor                  2
% 2.86/1.00  --inst_start_prop_sim_after_learn       3
% 2.86/1.00  --inst_sel_renew                        solver
% 2.86/1.00  --inst_lit_activity_flag                true
% 2.86/1.00  --inst_restr_to_given                   false
% 2.86/1.00  --inst_activity_threshold               500
% 2.86/1.00  --inst_out_proof                        true
% 2.86/1.00  
% 2.86/1.00  ------ Resolution Options
% 2.86/1.00  
% 2.86/1.00  --resolution_flag                       true
% 2.86/1.00  --res_lit_sel                           adaptive
% 2.86/1.00  --res_lit_sel_side                      none
% 2.86/1.00  --res_ordering                          kbo
% 2.86/1.00  --res_to_prop_solver                    active
% 2.86/1.00  --res_prop_simpl_new                    false
% 2.86/1.00  --res_prop_simpl_given                  true
% 2.86/1.00  --res_passive_queue_type                priority_queues
% 2.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/1.00  --res_passive_queues_freq               [15;5]
% 2.86/1.00  --res_forward_subs                      full
% 2.86/1.00  --res_backward_subs                     full
% 2.86/1.00  --res_forward_subs_resolution           true
% 2.86/1.00  --res_backward_subs_resolution          true
% 2.86/1.00  --res_orphan_elimination                true
% 2.86/1.00  --res_time_limit                        2.
% 2.86/1.00  --res_out_proof                         true
% 2.86/1.00  
% 2.86/1.00  ------ Superposition Options
% 2.86/1.00  
% 2.86/1.00  --superposition_flag                    true
% 2.86/1.00  --sup_passive_queue_type                priority_queues
% 2.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.86/1.00  --demod_completeness_check              fast
% 2.86/1.00  --demod_use_ground                      true
% 2.86/1.00  --sup_to_prop_solver                    passive
% 2.86/1.00  --sup_prop_simpl_new                    true
% 2.86/1.00  --sup_prop_simpl_given                  true
% 2.86/1.00  --sup_fun_splitting                     false
% 2.86/1.00  --sup_smt_interval                      50000
% 2.86/1.00  
% 2.86/1.00  ------ Superposition Simplification Setup
% 2.86/1.00  
% 2.86/1.00  --sup_indices_passive                   []
% 2.86/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_full_bw                           [BwDemod]
% 2.86/1.00  --sup_immed_triv                        [TrivRules]
% 2.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_immed_bw_main                     []
% 2.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.00  
% 2.86/1.00  ------ Combination Options
% 2.86/1.00  
% 2.86/1.00  --comb_res_mult                         3
% 2.86/1.00  --comb_sup_mult                         2
% 2.86/1.00  --comb_inst_mult                        10
% 2.86/1.00  
% 2.86/1.00  ------ Debug Options
% 2.86/1.00  
% 2.86/1.00  --dbg_backtrace                         false
% 2.86/1.00  --dbg_dump_prop_clauses                 false
% 2.86/1.00  --dbg_dump_prop_clauses_file            -
% 2.86/1.00  --dbg_out_stat                          false
% 2.86/1.00  ------ Parsing...
% 2.86/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.86/1.00  ------ Proving...
% 2.86/1.00  ------ Problem Properties 
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  clauses                                 23
% 2.86/1.00  conjectures                             8
% 2.86/1.00  EPR                                     4
% 2.86/1.00  Horn                                    23
% 2.86/1.00  unary                                   11
% 2.86/1.00  binary                                  4
% 2.86/1.00  lits                                    48
% 2.86/1.00  lits eq                                 22
% 2.86/1.00  fd_pure                                 0
% 2.86/1.00  fd_pseudo                               0
% 2.86/1.00  fd_cond                                 1
% 2.86/1.00  fd_pseudo_cond                          0
% 2.86/1.00  AC symbols                              0
% 2.86/1.00  
% 2.86/1.00  ------ Schedule dynamic 5 is on 
% 2.86/1.00  
% 2.86/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  ------ 
% 2.86/1.00  Current options:
% 2.86/1.00  ------ 
% 2.86/1.00  
% 2.86/1.00  ------ Input Options
% 2.86/1.00  
% 2.86/1.00  --out_options                           all
% 2.86/1.00  --tptp_safe_out                         true
% 2.86/1.00  --problem_path                          ""
% 2.86/1.00  --include_path                          ""
% 2.86/1.00  --clausifier                            res/vclausify_rel
% 2.86/1.00  --clausifier_options                    --mode clausify
% 2.86/1.00  --stdin                                 false
% 2.86/1.00  --stats_out                             all
% 2.86/1.00  
% 2.86/1.00  ------ General Options
% 2.86/1.00  
% 2.86/1.00  --fof                                   false
% 2.86/1.00  --time_out_real                         305.
% 2.86/1.00  --time_out_virtual                      -1.
% 2.86/1.00  --symbol_type_check                     false
% 2.86/1.00  --clausify_out                          false
% 2.86/1.00  --sig_cnt_out                           false
% 2.86/1.00  --trig_cnt_out                          false
% 2.86/1.00  --trig_cnt_out_tolerance                1.
% 2.86/1.00  --trig_cnt_out_sk_spl                   false
% 2.86/1.00  --abstr_cl_out                          false
% 2.86/1.00  
% 2.86/1.00  ------ Global Options
% 2.86/1.00  
% 2.86/1.00  --schedule                              default
% 2.86/1.00  --add_important_lit                     false
% 2.86/1.00  --prop_solver_per_cl                    1000
% 2.86/1.00  --min_unsat_core                        false
% 2.86/1.00  --soft_assumptions                      false
% 2.86/1.00  --soft_lemma_size                       3
% 2.86/1.00  --prop_impl_unit_size                   0
% 2.86/1.00  --prop_impl_unit                        []
% 2.86/1.00  --share_sel_clauses                     true
% 2.86/1.00  --reset_solvers                         false
% 2.86/1.00  --bc_imp_inh                            [conj_cone]
% 2.86/1.00  --conj_cone_tolerance                   3.
% 2.86/1.00  --extra_neg_conj                        none
% 2.86/1.00  --large_theory_mode                     true
% 2.86/1.00  --prolific_symb_bound                   200
% 2.86/1.00  --lt_threshold                          2000
% 2.86/1.00  --clause_weak_htbl                      true
% 2.86/1.00  --gc_record_bc_elim                     false
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing Options
% 2.86/1.00  
% 2.86/1.00  --preprocessing_flag                    true
% 2.86/1.00  --time_out_prep_mult                    0.1
% 2.86/1.00  --splitting_mode                        input
% 2.86/1.00  --splitting_grd                         true
% 2.86/1.00  --splitting_cvd                         false
% 2.86/1.00  --splitting_cvd_svl                     false
% 2.86/1.00  --splitting_nvd                         32
% 2.86/1.00  --sub_typing                            true
% 2.86/1.00  --prep_gs_sim                           true
% 2.86/1.00  --prep_unflatten                        true
% 2.86/1.00  --prep_res_sim                          true
% 2.86/1.00  --prep_upred                            true
% 2.86/1.00  --prep_sem_filter                       exhaustive
% 2.86/1.00  --prep_sem_filter_out                   false
% 2.86/1.00  --pred_elim                             true
% 2.86/1.00  --res_sim_input                         true
% 2.86/1.00  --eq_ax_congr_red                       true
% 2.86/1.00  --pure_diseq_elim                       true
% 2.86/1.00  --brand_transform                       false
% 2.86/1.00  --non_eq_to_eq                          false
% 2.86/1.00  --prep_def_merge                        true
% 2.86/1.00  --prep_def_merge_prop_impl              false
% 2.86/1.00  --prep_def_merge_mbd                    true
% 2.86/1.00  --prep_def_merge_tr_red                 false
% 2.86/1.00  --prep_def_merge_tr_cl                  false
% 2.86/1.00  --smt_preprocessing                     true
% 2.86/1.00  --smt_ac_axioms                         fast
% 2.86/1.00  --preprocessed_out                      false
% 2.86/1.00  --preprocessed_stats                    false
% 2.86/1.00  
% 2.86/1.00  ------ Abstraction refinement Options
% 2.86/1.00  
% 2.86/1.00  --abstr_ref                             []
% 2.86/1.00  --abstr_ref_prep                        false
% 2.86/1.00  --abstr_ref_until_sat                   false
% 2.86/1.00  --abstr_ref_sig_restrict                funpre
% 2.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/1.00  --abstr_ref_under                       []
% 2.86/1.00  
% 2.86/1.00  ------ SAT Options
% 2.86/1.00  
% 2.86/1.00  --sat_mode                              false
% 2.86/1.00  --sat_fm_restart_options                ""
% 2.86/1.00  --sat_gr_def                            false
% 2.86/1.00  --sat_epr_types                         true
% 2.86/1.00  --sat_non_cyclic_types                  false
% 2.86/1.00  --sat_finite_models                     false
% 2.86/1.00  --sat_fm_lemmas                         false
% 2.86/1.00  --sat_fm_prep                           false
% 2.86/1.00  --sat_fm_uc_incr                        true
% 2.86/1.00  --sat_out_model                         small
% 2.86/1.00  --sat_out_clauses                       false
% 2.86/1.00  
% 2.86/1.00  ------ QBF Options
% 2.86/1.00  
% 2.86/1.00  --qbf_mode                              false
% 2.86/1.00  --qbf_elim_univ                         false
% 2.86/1.00  --qbf_dom_inst                          none
% 2.86/1.00  --qbf_dom_pre_inst                      false
% 2.86/1.00  --qbf_sk_in                             false
% 2.86/1.00  --qbf_pred_elim                         true
% 2.86/1.00  --qbf_split                             512
% 2.86/1.00  
% 2.86/1.00  ------ BMC1 Options
% 2.86/1.00  
% 2.86/1.00  --bmc1_incremental                      false
% 2.86/1.00  --bmc1_axioms                           reachable_all
% 2.86/1.00  --bmc1_min_bound                        0
% 2.86/1.00  --bmc1_max_bound                        -1
% 2.86/1.00  --bmc1_max_bound_default                -1
% 2.86/1.00  --bmc1_symbol_reachability              true
% 2.86/1.00  --bmc1_property_lemmas                  false
% 2.86/1.00  --bmc1_k_induction                      false
% 2.86/1.00  --bmc1_non_equiv_states                 false
% 2.86/1.00  --bmc1_deadlock                         false
% 2.86/1.00  --bmc1_ucm                              false
% 2.86/1.00  --bmc1_add_unsat_core                   none
% 2.86/1.00  --bmc1_unsat_core_children              false
% 2.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/1.00  --bmc1_out_stat                         full
% 2.86/1.00  --bmc1_ground_init                      false
% 2.86/1.00  --bmc1_pre_inst_next_state              false
% 2.86/1.00  --bmc1_pre_inst_state                   false
% 2.86/1.00  --bmc1_pre_inst_reach_state             false
% 2.86/1.00  --bmc1_out_unsat_core                   false
% 2.86/1.00  --bmc1_aig_witness_out                  false
% 2.86/1.00  --bmc1_verbose                          false
% 2.86/1.00  --bmc1_dump_clauses_tptp                false
% 2.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.86/1.00  --bmc1_dump_file                        -
% 2.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.86/1.00  --bmc1_ucm_extend_mode                  1
% 2.86/1.00  --bmc1_ucm_init_mode                    2
% 2.86/1.00  --bmc1_ucm_cone_mode                    none
% 2.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.86/1.00  --bmc1_ucm_relax_model                  4
% 2.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/1.00  --bmc1_ucm_layered_model                none
% 2.86/1.00  --bmc1_ucm_max_lemma_size               10
% 2.86/1.00  
% 2.86/1.00  ------ AIG Options
% 2.86/1.00  
% 2.86/1.00  --aig_mode                              false
% 2.86/1.00  
% 2.86/1.00  ------ Instantiation Options
% 2.86/1.00  
% 2.86/1.00  --instantiation_flag                    true
% 2.86/1.00  --inst_sos_flag                         false
% 2.86/1.00  --inst_sos_phase                        true
% 2.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/1.00  --inst_lit_sel_side                     none
% 2.86/1.00  --inst_solver_per_active                1400
% 2.86/1.00  --inst_solver_calls_frac                1.
% 2.86/1.00  --inst_passive_queue_type               priority_queues
% 2.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/1.00  --inst_passive_queues_freq              [25;2]
% 2.86/1.00  --inst_dismatching                      true
% 2.86/1.00  --inst_eager_unprocessed_to_passive     true
% 2.86/1.00  --inst_prop_sim_given                   true
% 2.86/1.00  --inst_prop_sim_new                     false
% 2.86/1.00  --inst_subs_new                         false
% 2.86/1.00  --inst_eq_res_simp                      false
% 2.86/1.00  --inst_subs_given                       false
% 2.86/1.00  --inst_orphan_elimination               true
% 2.86/1.00  --inst_learning_loop_flag               true
% 2.86/1.00  --inst_learning_start                   3000
% 2.86/1.00  --inst_learning_factor                  2
% 2.86/1.00  --inst_start_prop_sim_after_learn       3
% 2.86/1.00  --inst_sel_renew                        solver
% 2.86/1.00  --inst_lit_activity_flag                true
% 2.86/1.00  --inst_restr_to_given                   false
% 2.86/1.00  --inst_activity_threshold               500
% 2.86/1.00  --inst_out_proof                        true
% 2.86/1.00  
% 2.86/1.00  ------ Resolution Options
% 2.86/1.00  
% 2.86/1.00  --resolution_flag                       false
% 2.86/1.00  --res_lit_sel                           adaptive
% 2.86/1.00  --res_lit_sel_side                      none
% 2.86/1.00  --res_ordering                          kbo
% 2.86/1.00  --res_to_prop_solver                    active
% 2.86/1.00  --res_prop_simpl_new                    false
% 2.86/1.00  --res_prop_simpl_given                  true
% 2.86/1.00  --res_passive_queue_type                priority_queues
% 2.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/1.00  --res_passive_queues_freq               [15;5]
% 2.86/1.00  --res_forward_subs                      full
% 2.86/1.00  --res_backward_subs                     full
% 2.86/1.00  --res_forward_subs_resolution           true
% 2.86/1.00  --res_backward_subs_resolution          true
% 2.86/1.00  --res_orphan_elimination                true
% 2.86/1.00  --res_time_limit                        2.
% 2.86/1.00  --res_out_proof                         true
% 2.86/1.00  
% 2.86/1.00  ------ Superposition Options
% 2.86/1.00  
% 2.86/1.00  --superposition_flag                    true
% 2.86/1.00  --sup_passive_queue_type                priority_queues
% 2.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.86/1.00  --demod_completeness_check              fast
% 2.86/1.00  --demod_use_ground                      true
% 2.86/1.00  --sup_to_prop_solver                    passive
% 2.86/1.00  --sup_prop_simpl_new                    true
% 2.86/1.00  --sup_prop_simpl_given                  true
% 2.86/1.00  --sup_fun_splitting                     false
% 2.86/1.00  --sup_smt_interval                      50000
% 2.86/1.00  
% 2.86/1.00  ------ Superposition Simplification Setup
% 2.86/1.00  
% 2.86/1.00  --sup_indices_passive                   []
% 2.86/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_full_bw                           [BwDemod]
% 2.86/1.00  --sup_immed_triv                        [TrivRules]
% 2.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_immed_bw_main                     []
% 2.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.00  
% 2.86/1.00  ------ Combination Options
% 2.86/1.00  
% 2.86/1.00  --comb_res_mult                         3
% 2.86/1.00  --comb_sup_mult                         2
% 2.86/1.00  --comb_inst_mult                        10
% 2.86/1.00  
% 2.86/1.00  ------ Debug Options
% 2.86/1.00  
% 2.86/1.00  --dbg_backtrace                         false
% 2.86/1.00  --dbg_dump_prop_clauses                 false
% 2.86/1.00  --dbg_dump_prop_clauses_file            -
% 2.86/1.00  --dbg_out_stat                          false
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  ------ Proving...
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  % SZS status Theorem for theBenchmark.p
% 2.86/1.00  
% 2.86/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.86/1.00  
% 2.86/1.00  fof(f7,axiom,(
% 2.86/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f23,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.86/1.00    inference(ennf_transformation,[],[f7])).
% 2.86/1.00  
% 2.86/1.00  fof(f24,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(flattening,[],[f23])).
% 2.86/1.00  
% 2.86/1.00  fof(f31,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(nnf_transformation,[],[f24])).
% 2.86/1.00  
% 2.86/1.00  fof(f42,plain,(
% 2.86/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.00    inference(cnf_transformation,[],[f31])).
% 2.86/1.00  
% 2.86/1.00  fof(f12,conjecture,(
% 2.86/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f13,negated_conjecture,(
% 2.86/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.86/1.00    inference(negated_conjecture,[],[f12])).
% 2.86/1.00  
% 2.86/1.00  fof(f29,plain,(
% 2.86/1.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.86/1.00    inference(ennf_transformation,[],[f13])).
% 2.86/1.00  
% 2.86/1.00  fof(f30,plain,(
% 2.86/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.86/1.00    inference(flattening,[],[f29])).
% 2.86/1.00  
% 2.86/1.00  fof(f34,plain,(
% 2.86/1.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.86/1.00    introduced(choice_axiom,[])).
% 2.86/1.00  
% 2.86/1.00  fof(f33,plain,(
% 2.86/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.86/1.00    introduced(choice_axiom,[])).
% 2.86/1.00  
% 2.86/1.00  fof(f35,plain,(
% 2.86/1.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f34,f33])).
% 2.86/1.00  
% 2.86/1.00  fof(f60,plain,(
% 2.86/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f8,axiom,(
% 2.86/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f44,plain,(
% 2.86/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.86/1.00    inference(cnf_transformation,[],[f8])).
% 2.86/1.00  
% 2.86/1.00  fof(f11,axiom,(
% 2.86/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f52,plain,(
% 2.86/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.86/1.00    inference(cnf_transformation,[],[f11])).
% 2.86/1.00  
% 2.86/1.00  fof(f66,plain,(
% 2.86/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.86/1.00    inference(definition_unfolding,[],[f44,f52])).
% 2.86/1.00  
% 2.86/1.00  fof(f55,plain,(
% 2.86/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f58,plain,(
% 2.86/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f10,axiom,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f27,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.86/1.00    inference(ennf_transformation,[],[f10])).
% 2.86/1.00  
% 2.86/1.00  fof(f28,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.86/1.00    inference(flattening,[],[f27])).
% 2.86/1.00  
% 2.86/1.00  fof(f51,plain,(
% 2.86/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.86/1.00    inference(cnf_transformation,[],[f28])).
% 2.86/1.00  
% 2.86/1.00  fof(f56,plain,(
% 2.86/1.00    v1_funct_1(sK3)),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f53,plain,(
% 2.86/1.00    v1_funct_1(sK2)),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f6,axiom,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f21,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.86/1.00    inference(ennf_transformation,[],[f6])).
% 2.86/1.00  
% 2.86/1.00  fof(f22,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(flattening,[],[f21])).
% 2.86/1.00  
% 2.86/1.00  fof(f41,plain,(
% 2.86/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.00    inference(cnf_transformation,[],[f22])).
% 2.86/1.00  
% 2.86/1.00  fof(f3,axiom,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f17,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.86/1.00    inference(ennf_transformation,[],[f3])).
% 2.86/1.00  
% 2.86/1.00  fof(f18,plain,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(flattening,[],[f17])).
% 2.86/1.00  
% 2.86/1.00  fof(f38,plain,(
% 2.86/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.00    inference(cnf_transformation,[],[f18])).
% 2.86/1.00  
% 2.86/1.00  fof(f1,axiom,(
% 2.86/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f14,plain,(
% 2.86/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.86/1.00    inference(ennf_transformation,[],[f1])).
% 2.86/1.00  
% 2.86/1.00  fof(f15,plain,(
% 2.86/1.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/1.00    inference(flattening,[],[f14])).
% 2.86/1.00  
% 2.86/1.00  fof(f36,plain,(
% 2.86/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/1.00    inference(cnf_transformation,[],[f15])).
% 2.86/1.00  
% 2.86/1.00  fof(f65,plain,(
% 2.86/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/1.00    inference(definition_unfolding,[],[f36,f52])).
% 2.86/1.00  
% 2.86/1.00  fof(f61,plain,(
% 2.86/1.00    v2_funct_1(sK2)),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f2,axiom,(
% 2.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f16,plain,(
% 2.86/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(ennf_transformation,[],[f2])).
% 2.86/1.00  
% 2.86/1.00  fof(f37,plain,(
% 2.86/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.00    inference(cnf_transformation,[],[f16])).
% 2.86/1.00  
% 2.86/1.00  fof(f4,axiom,(
% 2.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f19,plain,(
% 2.86/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(ennf_transformation,[],[f4])).
% 2.86/1.00  
% 2.86/1.00  fof(f39,plain,(
% 2.86/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.00    inference(cnf_transformation,[],[f19])).
% 2.86/1.00  
% 2.86/1.00  fof(f9,axiom,(
% 2.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f25,plain,(
% 2.86/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(ennf_transformation,[],[f9])).
% 2.86/1.00  
% 2.86/1.00  fof(f26,plain,(
% 2.86/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(flattening,[],[f25])).
% 2.86/1.00  
% 2.86/1.00  fof(f32,plain,(
% 2.86/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(nnf_transformation,[],[f26])).
% 2.86/1.00  
% 2.86/1.00  fof(f45,plain,(
% 2.86/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.00    inference(cnf_transformation,[],[f32])).
% 2.86/1.00  
% 2.86/1.00  fof(f54,plain,(
% 2.86/1.00    v1_funct_2(sK2,sK0,sK1)),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f63,plain,(
% 2.86/1.00    k1_xboole_0 != sK1),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f5,axiom,(
% 2.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f20,plain,(
% 2.86/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.00    inference(ennf_transformation,[],[f5])).
% 2.86/1.00  
% 2.86/1.00  fof(f40,plain,(
% 2.86/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.00    inference(cnf_transformation,[],[f20])).
% 2.86/1.00  
% 2.86/1.00  fof(f59,plain,(
% 2.86/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f57,plain,(
% 2.86/1.00    v1_funct_2(sK3,sK1,sK0)),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f62,plain,(
% 2.86/1.00    k1_xboole_0 != sK0),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  fof(f64,plain,(
% 2.86/1.00    k2_funct_1(sK2) != sK3),
% 2.86/1.00    inference(cnf_transformation,[],[f35])).
% 2.86/1.00  
% 2.86/1.00  cnf(c_7,plain,
% 2.86/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.86/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.86/1.00      | X3 = X2 ),
% 2.86/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_20,negated_conjecture,
% 2.86/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.86/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_310,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | X3 = X0
% 2.86/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.86/1.00      | k6_partfun1(sK0) != X3
% 2.86/1.00      | sK0 != X2
% 2.86/1.00      | sK0 != X1 ),
% 2.86/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_311,plain,
% 2.86/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.86/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.86/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.86/1.00      inference(unflattening,[status(thm)],[c_310]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_8,plain,
% 2.86/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.86/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_319,plain,
% 2.86/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.86/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.86/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_311,c_8]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_564,plain,
% 2.86/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.86/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_319]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_923,plain,
% 2.86/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.86/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_25,negated_conjecture,
% 2.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.86/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_567,negated_conjecture,
% 2.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_920,plain,
% 2.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_22,negated_conjecture,
% 2.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.86/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_569,negated_conjecture,
% 2.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_918,plain,
% 2.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_15,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.86/1.00      | ~ v1_funct_1(X0)
% 2.86/1.00      | ~ v1_funct_1(X3)
% 2.86/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.86/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_574,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.86/1.00      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 2.86/1.00      | ~ v1_funct_1(X0_50)
% 2.86/1.00      | ~ v1_funct_1(X3_50)
% 2.86/1.00      | k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_917,plain,
% 2.86/1.00      ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
% 2.86/1.00      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 2.86/1.00      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.86/1.00      | v1_funct_1(X5_50) != iProver_top
% 2.86/1.00      | v1_funct_1(X4_50) != iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_2221,plain,
% 2.86/1.00      ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
% 2.86/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.86/1.00      | v1_funct_1(X2_50) != iProver_top
% 2.86/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_918,c_917]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_24,negated_conjecture,
% 2.86/1.00      ( v1_funct_1(sK3) ),
% 2.86/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_31,plain,
% 2.86/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_3214,plain,
% 2.86/1.00      ( v1_funct_1(X2_50) != iProver_top
% 2.86/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.86/1.00      | k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3) ),
% 2.86/1.00      inference(global_propositional_subsumption,
% 2.86/1.00                [status(thm)],
% 2.86/1.00                [c_2221,c_31]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_3215,plain,
% 2.86/1.00      ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
% 2.86/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.86/1.00      | v1_funct_1(X2_50) != iProver_top ),
% 2.86/1.00      inference(renaming,[status(thm)],[c_3214]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_3224,plain,
% 2.86/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 2.86/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_920,c_3215]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_27,negated_conjecture,
% 2.86/1.00      ( v1_funct_1(sK2) ),
% 2.86/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1165,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3_50,X4_50)))
% 2.86/1.00      | ~ v1_funct_1(X0_50)
% 2.86/1.00      | ~ v1_funct_1(sK3)
% 2.86/1.00      | k1_partfun1(X1_50,X2_50,X3_50,X4_50,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
% 2.86/1.00      inference(instantiation,[status(thm)],[c_574]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1303,plain,
% 2.86/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 2.86/1.00      | ~ v1_funct_1(sK3)
% 2.86/1.00      | ~ v1_funct_1(sK2)
% 2.86/1.00      | k1_partfun1(X2_50,X3_50,X0_50,X1_50,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.86/1.00      inference(instantiation,[status(thm)],[c_1165]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1799,plain,
% 2.86/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.86/1.00      | ~ v1_funct_1(sK3)
% 2.86/1.00      | ~ v1_funct_1(sK2)
% 2.86/1.00      | k1_partfun1(X0_50,X1_50,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.86/1.00      inference(instantiation,[status(thm)],[c_1303]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_2807,plain,
% 2.86/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.86/1.00      | ~ v1_funct_1(sK3)
% 2.86/1.00      | ~ v1_funct_1(sK2)
% 2.86/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.86/1.00      inference(instantiation,[status(thm)],[c_1799]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_4681,plain,
% 2.86/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.86/1.00      inference(global_propositional_subsumption,
% 2.86/1.00                [status(thm)],
% 2.86/1.00                [c_3224,c_27,c_25,c_24,c_22,c_2807]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_4829,plain,
% 2.86/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.86/1.00      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.86/1.00      inference(light_normalisation,[status(thm)],[c_923,c_4681]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_4830,plain,
% 2.86/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 2.86/1.00      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.86/1.00      inference(demodulation,[status(thm)],[c_4829,c_4681]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_30,plain,
% 2.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_33,plain,
% 2.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_5,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.86/1.00      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.86/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_576,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.86/1.00      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 2.86/1.00      | k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_915,plain,
% 2.86/1.00      ( k4_relset_1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
% 2.86/1.00      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 2.86/1.00      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_2179,plain,
% 2.86/1.00      ( k4_relset_1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
% 2.86/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_918,c_915]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_2378,plain,
% 2.86/1.00      ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_920,c_2179]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_2,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.86/1.00      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 2.86/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_579,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.86/1.00      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 2.86/1.00      | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_912,plain,
% 2.86/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 2.86/1.00      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50))) != iProver_top
% 2.86/1.00      | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) = iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_2568,plain,
% 2.86/1.00      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_2378,c_912]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_4834,plain,
% 2.86/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 2.86/1.00      inference(global_propositional_subsumption,
% 2.86/1.00                [status(thm)],
% 2.86/1.00                [c_4830,c_30,c_33,c_2568]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_0,plain,
% 2.86/1.00      ( ~ v1_relat_1(X0)
% 2.86/1.00      | ~ v1_relat_1(X1)
% 2.86/1.00      | ~ v1_funct_1(X0)
% 2.86/1.00      | ~ v1_funct_1(X1)
% 2.86/1.00      | ~ v2_funct_1(X1)
% 2.86/1.00      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 2.86/1.00      | k2_relat_1(X1) != k1_relat_1(X0)
% 2.86/1.00      | k2_funct_1(X1) = X0 ),
% 2.86/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_19,negated_conjecture,
% 2.86/1.00      ( v2_funct_1(sK2) ),
% 2.86/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_271,plain,
% 2.86/1.00      ( ~ v1_relat_1(X0)
% 2.86/1.00      | ~ v1_relat_1(X1)
% 2.86/1.00      | ~ v1_funct_1(X0)
% 2.86/1.00      | ~ v1_funct_1(X1)
% 2.86/1.00      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 2.86/1.00      | k2_relat_1(X0) != k1_relat_1(X1)
% 2.86/1.00      | k2_funct_1(X0) = X1
% 2.86/1.00      | sK2 != X0 ),
% 2.86/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_272,plain,
% 2.86/1.00      ( ~ v1_relat_1(X0)
% 2.86/1.00      | ~ v1_relat_1(sK2)
% 2.86/1.00      | ~ v1_funct_1(X0)
% 2.86/1.00      | ~ v1_funct_1(sK2)
% 2.86/1.00      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.00      | k2_relat_1(sK2) != k1_relat_1(X0)
% 2.86/1.00      | k2_funct_1(sK2) = X0 ),
% 2.86/1.00      inference(unflattening,[status(thm)],[c_271]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_276,plain,
% 2.86/1.00      ( ~ v1_funct_1(X0)
% 2.86/1.00      | ~ v1_relat_1(sK2)
% 2.86/1.00      | ~ v1_relat_1(X0)
% 2.86/1.00      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.00      | k2_relat_1(sK2) != k1_relat_1(X0)
% 2.86/1.00      | k2_funct_1(sK2) = X0 ),
% 2.86/1.00      inference(global_propositional_subsumption,
% 2.86/1.00                [status(thm)],
% 2.86/1.00                [c_272,c_27]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_277,plain,
% 2.86/1.00      ( ~ v1_relat_1(X0)
% 2.86/1.00      | ~ v1_relat_1(sK2)
% 2.86/1.00      | ~ v1_funct_1(X0)
% 2.86/1.00      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.00      | k2_relat_1(sK2) != k1_relat_1(X0)
% 2.86/1.00      | k2_funct_1(sK2) = X0 ),
% 2.86/1.00      inference(renaming,[status(thm)],[c_276]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_565,plain,
% 2.86/1.00      ( ~ v1_relat_1(X0_50)
% 2.86/1.00      | ~ v1_relat_1(sK2)
% 2.86/1.00      | ~ v1_funct_1(X0_50)
% 2.86/1.00      | k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.00      | k2_relat_1(sK2) != k1_relat_1(X0_50)
% 2.86/1.00      | k2_funct_1(sK2) = X0_50 ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_277]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_922,plain,
% 2.86/1.00      ( k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.00      | k2_relat_1(sK2) != k1_relat_1(X0_50)
% 2.86/1.00      | k2_funct_1(sK2) = X0_50
% 2.86/1.00      | v1_relat_1(X0_50) != iProver_top
% 2.86/1.00      | v1_relat_1(sK2) != iProver_top
% 2.86/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_635,plain,
% 2.86/1.00      ( k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.00      | k2_relat_1(sK2) != k1_relat_1(X0_50)
% 2.86/1.00      | k2_funct_1(sK2) = X0_50
% 2.86/1.00      | v1_relat_1(X0_50) != iProver_top
% 2.86/1.00      | v1_relat_1(sK2) != iProver_top
% 2.86/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | v1_relat_1(X0) ),
% 2.86/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_580,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.86/1.00      | v1_relat_1(X0_50) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1068,plain,
% 2.86/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.86/1.00      | v1_relat_1(sK2) ),
% 2.86/1.00      inference(instantiation,[status(thm)],[c_580]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1069,plain,
% 2.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.86/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_3454,plain,
% 2.86/1.00      ( v1_relat_1(X0_50) != iProver_top
% 2.86/1.00      | k2_funct_1(sK2) = X0_50
% 2.86/1.00      | k2_relat_1(sK2) != k1_relat_1(X0_50)
% 2.86/1.00      | k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.86/1.00      inference(global_propositional_subsumption,
% 2.86/1.00                [status(thm)],
% 2.86/1.00                [c_922,c_30,c_635,c_1069]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_3455,plain,
% 2.86/1.00      ( k5_relat_1(sK2,X0_50) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.00      | k2_relat_1(sK2) != k1_relat_1(X0_50)
% 2.86/1.00      | k2_funct_1(sK2) = X0_50
% 2.86/1.00      | v1_relat_1(X0_50) != iProver_top
% 2.86/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.86/1.00      inference(renaming,[status(thm)],[c_3454]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_3,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.86/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_578,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.86/1.00      | k1_relset_1(X1_50,X2_50,X0_50) = k1_relat_1(X0_50) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_913,plain,
% 2.86/1.00      ( k1_relset_1(X0_50,X1_50,X2_50) = k1_relat_1(X2_50)
% 2.86/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1338,plain,
% 2.86/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_920,c_913]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_14,plain,
% 2.86/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.86/1.00      | k1_xboole_0 = X2 ),
% 2.86/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_26,negated_conjecture,
% 2.86/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.86/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_410,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.86/1.00      | sK0 != X1
% 2.86/1.00      | sK1 != X2
% 2.86/1.00      | sK2 != X0
% 2.86/1.00      | k1_xboole_0 = X2 ),
% 2.86/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_411,plain,
% 2.86/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.86/1.00      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.86/1.00      | k1_xboole_0 = sK1 ),
% 2.86/1.00      inference(unflattening,[status(thm)],[c_410]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_17,negated_conjecture,
% 2.86/1.00      ( k1_xboole_0 != sK1 ),
% 2.86/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_413,plain,
% 2.86/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 2.86/1.00      inference(global_propositional_subsumption,
% 2.86/1.00                [status(thm)],
% 2.86/1.00                [c_411,c_25,c_17]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_558,plain,
% 2.86/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_413]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1343,plain,
% 2.86/1.00      ( k1_relat_1(sK2) = sK0 ),
% 2.86/1.00      inference(light_normalisation,[status(thm)],[c_1338,c_558]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_4,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.86/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_577,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.86/1.00      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_914,plain,
% 2.86/1.00      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 2.86/1.00      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1962,plain,
% 2.86/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_920,c_914]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_21,negated_conjecture,
% 2.86/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.86/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_570,negated_conjecture,
% 2.86/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1974,plain,
% 2.86/1.00      ( k2_relat_1(sK2) = sK1 ),
% 2.86/1.00      inference(light_normalisation,[status(thm)],[c_1962,c_570]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_3460,plain,
% 2.86/1.00      ( k5_relat_1(sK2,X0_50) != k6_partfun1(sK0)
% 2.86/1.00      | k1_relat_1(X0_50) != sK1
% 2.86/1.00      | k2_funct_1(sK2) = X0_50
% 2.86/1.00      | v1_relat_1(X0_50) != iProver_top
% 2.86/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.86/1.00      inference(light_normalisation,[status(thm)],[c_3455,c_1343,c_1974]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_4842,plain,
% 2.86/1.00      ( k1_relat_1(sK3) != sK1
% 2.86/1.00      | k2_funct_1(sK2) = sK3
% 2.86/1.00      | v1_relat_1(sK3) != iProver_top
% 2.86/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_4834,c_3460]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1337,plain,
% 2.86/1.00      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 2.86/1.00      inference(superposition,[status(thm)],[c_918,c_913]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_23,negated_conjecture,
% 2.86/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.86/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_402,plain,
% 2.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.86/1.00      | sK0 != X2
% 2.86/1.00      | sK1 != X1
% 2.86/1.00      | sK3 != X0
% 2.86/1.00      | k1_xboole_0 = X2 ),
% 2.86/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_403,plain,
% 2.86/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.86/1.00      | k1_relset_1(sK1,sK0,sK3) = sK1
% 2.86/1.00      | k1_xboole_0 = sK0 ),
% 2.86/1.00      inference(unflattening,[status(thm)],[c_402]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_18,negated_conjecture,
% 2.86/1.00      ( k1_xboole_0 != sK0 ),
% 2.86/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_405,plain,
% 2.86/1.00      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 2.86/1.00      inference(global_propositional_subsumption,
% 2.86/1.00                [status(thm)],
% 2.86/1.00                [c_403,c_22,c_18]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_559,plain,
% 2.86/1.00      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_405]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1346,plain,
% 2.86/1.00      ( k1_relat_1(sK3) = sK1 ),
% 2.86/1.00      inference(light_normalisation,[status(thm)],[c_1337,c_559]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_4843,plain,
% 2.86/1.00      ( k2_funct_1(sK2) = sK3
% 2.86/1.00      | sK1 != sK1
% 2.86/1.00      | v1_relat_1(sK3) != iProver_top
% 2.86/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.86/1.00      inference(light_normalisation,[status(thm)],[c_4842,c_1346]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_4844,plain,
% 2.86/1.00      ( k2_funct_1(sK2) = sK3
% 2.86/1.00      | v1_relat_1(sK3) != iProver_top
% 2.86/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.86/1.00      inference(equality_resolution_simp,[status(thm)],[c_4843]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1065,plain,
% 2.86/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.86/1.00      | v1_relat_1(sK3) ),
% 2.86/1.00      inference(instantiation,[status(thm)],[c_580]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_1066,plain,
% 2.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.86/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1065]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_16,negated_conjecture,
% 2.86/1.00      ( k2_funct_1(sK2) != sK3 ),
% 2.86/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(c_573,negated_conjecture,
% 2.86/1.00      ( k2_funct_1(sK2) != sK3 ),
% 2.86/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.86/1.00  
% 2.86/1.00  cnf(contradiction,plain,
% 2.86/1.00      ( $false ),
% 2.86/1.00      inference(minisat,[status(thm)],[c_4844,c_1066,c_573,c_33,c_31]) ).
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.86/1.00  
% 2.86/1.00  ------                               Statistics
% 2.86/1.00  
% 2.86/1.00  ------ General
% 2.86/1.00  
% 2.86/1.00  abstr_ref_over_cycles:                  0
% 2.86/1.00  abstr_ref_under_cycles:                 0
% 2.86/1.00  gc_basic_clause_elim:                   0
% 2.86/1.00  forced_gc_time:                         0
% 2.86/1.00  parsing_time:                           0.011
% 2.86/1.00  unif_index_cands_time:                  0.
% 2.86/1.00  unif_index_add_time:                    0.
% 2.86/1.00  orderings_time:                         0.
% 2.86/1.00  out_proof_time:                         0.011
% 2.86/1.00  total_time:                             0.183
% 2.86/1.00  num_of_symbols:                         56
% 2.86/1.00  num_of_terms:                           5737
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing
% 2.86/1.00  
% 2.86/1.00  num_of_splits:                          0
% 2.86/1.00  num_of_split_atoms:                     0
% 2.86/1.00  num_of_reused_defs:                     0
% 2.86/1.00  num_eq_ax_congr_red:                    27
% 2.86/1.00  num_of_sem_filtered_clauses:            1
% 2.86/1.00  num_of_subtypes:                        3
% 2.86/1.00  monotx_restored_types:                  0
% 2.86/1.00  sat_num_of_epr_types:                   0
% 2.86/1.00  sat_num_of_non_cyclic_types:            0
% 2.86/1.00  sat_guarded_non_collapsed_types:        1
% 2.86/1.00  num_pure_diseq_elim:                    0
% 2.86/1.00  simp_replaced_by:                       0
% 2.86/1.00  res_preprocessed:                       132
% 2.86/1.00  prep_upred:                             0
% 2.86/1.00  prep_unflattend:                        43
% 2.86/1.00  smt_new_axioms:                         0
% 2.86/1.00  pred_elim_cands:                        3
% 2.86/1.00  pred_elim:                              3
% 2.86/1.00  pred_elim_cl:                           5
% 2.86/1.00  pred_elim_cycles:                       5
% 2.86/1.00  merged_defs:                            0
% 2.86/1.00  merged_defs_ncl:                        0
% 2.86/1.00  bin_hyper_res:                          0
% 2.86/1.00  prep_cycles:                            4
% 2.86/1.00  pred_elim_time:                         0.005
% 2.86/1.00  splitting_time:                         0.
% 2.86/1.00  sem_filter_time:                        0.
% 2.86/1.00  monotx_time:                            0.
% 2.86/1.00  subtype_inf_time:                       0.001
% 2.86/1.00  
% 2.86/1.00  ------ Problem properties
% 2.86/1.00  
% 2.86/1.00  clauses:                                23
% 2.86/1.00  conjectures:                            8
% 2.86/1.00  epr:                                    4
% 2.86/1.00  horn:                                   23
% 2.86/1.00  ground:                                 15
% 2.86/1.00  unary:                                  11
% 2.86/1.00  binary:                                 4
% 2.86/1.00  lits:                                   48
% 2.86/1.00  lits_eq:                                22
% 2.86/1.00  fd_pure:                                0
% 2.86/1.00  fd_pseudo:                              0
% 2.86/1.00  fd_cond:                                1
% 2.86/1.00  fd_pseudo_cond:                         0
% 2.86/1.00  ac_symbols:                             0
% 2.86/1.00  
% 2.86/1.00  ------ Propositional Solver
% 2.86/1.00  
% 2.86/1.00  prop_solver_calls:                      28
% 2.86/1.00  prop_fast_solver_calls:                 762
% 2.86/1.00  smt_solver_calls:                       0
% 2.86/1.00  smt_fast_solver_calls:                  0
% 2.86/1.00  prop_num_of_clauses:                    2341
% 2.86/1.00  prop_preprocess_simplified:             6400
% 2.86/1.00  prop_fo_subsumed:                       24
% 2.86/1.00  prop_solver_time:                       0.
% 2.86/1.00  smt_solver_time:                        0.
% 2.86/1.00  smt_fast_solver_time:                   0.
% 2.86/1.00  prop_fast_solver_time:                  0.
% 2.86/1.00  prop_unsat_core_time:                   0.
% 2.86/1.00  
% 2.86/1.00  ------ QBF
% 2.86/1.00  
% 2.86/1.00  qbf_q_res:                              0
% 2.86/1.00  qbf_num_tautologies:                    0
% 2.86/1.00  qbf_prep_cycles:                        0
% 2.86/1.00  
% 2.86/1.00  ------ BMC1
% 2.86/1.00  
% 2.86/1.00  bmc1_current_bound:                     -1
% 2.86/1.00  bmc1_last_solved_bound:                 -1
% 2.86/1.00  bmc1_unsat_core_size:                   -1
% 2.86/1.00  bmc1_unsat_core_parents_size:           -1
% 2.86/1.00  bmc1_merge_next_fun:                    0
% 2.86/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.86/1.00  
% 2.86/1.00  ------ Instantiation
% 2.86/1.00  
% 2.86/1.00  inst_num_of_clauses:                    727
% 2.86/1.00  inst_num_in_passive:                    511
% 2.86/1.00  inst_num_in_active:                     210
% 2.86/1.00  inst_num_in_unprocessed:                6
% 2.86/1.00  inst_num_of_loops:                      230
% 2.86/1.00  inst_num_of_learning_restarts:          0
% 2.86/1.00  inst_num_moves_active_passive:          18
% 2.86/1.00  inst_lit_activity:                      0
% 2.86/1.00  inst_lit_activity_moves:                1
% 2.86/1.00  inst_num_tautologies:                   0
% 2.86/1.00  inst_num_prop_implied:                  0
% 2.86/1.00  inst_num_existing_simplified:           0
% 2.86/1.00  inst_num_eq_res_simplified:             0
% 2.86/1.00  inst_num_child_elim:                    0
% 2.86/1.00  inst_num_of_dismatching_blockings:      12
% 2.86/1.00  inst_num_of_non_proper_insts:           334
% 2.86/1.00  inst_num_of_duplicates:                 0
% 2.86/1.00  inst_inst_num_from_inst_to_res:         0
% 2.86/1.00  inst_dismatching_checking_time:         0.
% 2.86/1.00  
% 2.86/1.00  ------ Resolution
% 2.86/1.00  
% 2.86/1.00  res_num_of_clauses:                     0
% 2.86/1.00  res_num_in_passive:                     0
% 2.86/1.00  res_num_in_active:                      0
% 2.86/1.00  res_num_of_loops:                       136
% 2.86/1.00  res_forward_subset_subsumed:            17
% 2.86/1.00  res_backward_subset_subsumed:           0
% 2.86/1.00  res_forward_subsumed:                   0
% 2.86/1.00  res_backward_subsumed:                  0
% 2.86/1.00  res_forward_subsumption_resolution:     1
% 2.86/1.00  res_backward_subsumption_resolution:    0
% 2.86/1.00  res_clause_to_clause_subsumption:       138
% 2.86/1.00  res_orphan_elimination:                 0
% 2.86/1.00  res_tautology_del:                      20
% 2.86/1.00  res_num_eq_res_simplified:              0
% 2.86/1.00  res_num_sel_changes:                    0
% 2.86/1.00  res_moves_from_active_to_pass:          0
% 2.86/1.00  
% 2.86/1.00  ------ Superposition
% 2.86/1.00  
% 2.86/1.00  sup_time_total:                         0.
% 2.86/1.00  sup_time_generating:                    0.
% 2.86/1.00  sup_time_sim_full:                      0.
% 2.86/1.00  sup_time_sim_immed:                     0.
% 2.86/1.00  
% 2.86/1.00  sup_num_of_clauses:                     74
% 2.86/1.00  sup_num_in_active:                      44
% 2.86/1.00  sup_num_in_passive:                     30
% 2.86/1.00  sup_num_of_loops:                       45
% 2.86/1.00  sup_fw_superposition:                   31
% 2.86/1.00  sup_bw_superposition:                   22
% 2.86/1.00  sup_immediate_simplified:               4
% 2.86/1.00  sup_given_eliminated:                   0
% 2.86/1.00  comparisons_done:                       0
% 2.86/1.00  comparisons_avoided:                    0
% 2.86/1.00  
% 2.86/1.00  ------ Simplifications
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  sim_fw_subset_subsumed:                 0
% 2.86/1.00  sim_bw_subset_subsumed:                 0
% 2.86/1.00  sim_fw_subsumed:                        0
% 2.86/1.00  sim_bw_subsumed:                        0
% 2.86/1.00  sim_fw_subsumption_res:                 0
% 2.86/1.00  sim_bw_subsumption_res:                 0
% 2.86/1.00  sim_tautology_del:                      0
% 2.86/1.00  sim_eq_tautology_del:                   0
% 2.86/1.00  sim_eq_res_simp:                        1
% 2.86/1.00  sim_fw_demodulated:                     1
% 2.86/1.00  sim_bw_demodulated:                     2
% 2.86/1.00  sim_light_normalised:                   6
% 2.86/1.00  sim_joinable_taut:                      0
% 2.86/1.00  sim_joinable_simp:                      0
% 2.86/1.00  sim_ac_normalised:                      0
% 2.86/1.00  sim_smt_subsumption:                    0
% 2.86/1.00  
%------------------------------------------------------------------------------
