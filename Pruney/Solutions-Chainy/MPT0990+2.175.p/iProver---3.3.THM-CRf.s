%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:34 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 666 expanded)
%              Number of clauses        :  107 ( 191 expanded)
%              Number of leaves         :   19 ( 174 expanded)
%              Depth                    :   19
%              Number of atoms          :  671 (5733 expanded)
%              Number of equality atoms :  313 (2111 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f31])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_787,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_790,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_796,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6864,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_796])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8114,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6864,c_37])).

cnf(c_8115,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8114])).

cnf(c_8126,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_8115])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X3,X4,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_2431,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_3515,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2431])).

cnf(c_8315,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8126,c_33,c_31,c_30,c_28,c_3515])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_791,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8318,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8315,c_791])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_806,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5010,plain,
    ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_806])).

cnf(c_6580,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_787,c_5010])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_808,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6750,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6580,c_808])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11344,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6750,c_36,c_39])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_804,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11363,plain,
    ( k5_relat_1(sK2,sK3) = X0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11344,c_804])).

cnf(c_14879,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8318,c_11363])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1476,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1479,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1476])).

cnf(c_23264,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14879,c_1479])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_257,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_2])).

cnf(c_258,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_784,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_relat_1(X0) != k1_relat_1(X1)
    | k2_funct_1(X0) = X1
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_23313,plain,
    ( k2_relat_1(sK2) != k1_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_23264,c_784])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_797,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3779,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_797])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_807,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1742,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_787,c_807])).

cnf(c_3783,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3779,c_1742])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_284,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_317,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_285,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1144,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_1145,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_4811,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3783,c_35,c_23,c_317,c_1145])).

cnf(c_3778,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_797])).

cnf(c_1741,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_790,c_807])).

cnf(c_3790,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3778,c_1741])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1146,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_1147,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_8517,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3790,c_38,c_24,c_317,c_1147])).

cnf(c_23321,plain,
    ( k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = sK3
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23313,c_4811,c_8517])).

cnf(c_23322,plain,
    ( k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_23321])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_795,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4833,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_795])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1282,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1611,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1612,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1611])).

cnf(c_5876,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4833,c_34,c_35,c_36,c_27,c_41,c_1612])).

cnf(c_5883,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5876,c_797])).

cnf(c_5884,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5876,c_807])).

cnf(c_785,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_809,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3064,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_809])).

cnf(c_1151,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1370,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_0,c_31])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1444,plain,
    ( v1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1370,c_1])).

cnf(c_4152,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3064,c_33,c_25,c_1151,c_1444])).

cnf(c_5896,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5884,c_4152])).

cnf(c_5898,plain,
    ( k2_relat_1(sK2) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5883,c_5896])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1287,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1614,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_1615,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1614])).

cnf(c_1445,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_1368,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_0,c_28])).

cnf(c_1386,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1368,c_1])).

cnf(c_1387,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1386])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23322,c_5898,c_1615,c_1445,c_1387,c_1147,c_317,c_22,c_24,c_41,c_27,c_37,c_36,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:36:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.53/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.53/1.49  
% 7.53/1.49  ------  iProver source info
% 7.53/1.49  
% 7.53/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.53/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.53/1.49  git: non_committed_changes: false
% 7.53/1.49  git: last_make_outside_of_git: false
% 7.53/1.49  
% 7.53/1.49  ------ 
% 7.53/1.49  ------ Parsing...
% 7.53/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.53/1.49  ------ Proving...
% 7.53/1.49  ------ Problem Properties 
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  clauses                                 34
% 7.53/1.49  conjectures                             12
% 7.53/1.49  EPR                                     7
% 7.53/1.49  Horn                                    30
% 7.53/1.49  unary                                   14
% 7.53/1.49  binary                                  2
% 7.53/1.49  lits                                    96
% 7.53/1.49  lits eq                                 26
% 7.53/1.49  fd_pure                                 0
% 7.53/1.49  fd_pseudo                               0
% 7.53/1.49  fd_cond                                 3
% 7.53/1.49  fd_pseudo_cond                          2
% 7.53/1.49  AC symbols                              0
% 7.53/1.49  
% 7.53/1.49  ------ Input Options Time Limit: Unbounded
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  ------ 
% 7.53/1.49  Current options:
% 7.53/1.49  ------ 
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  ------ Proving...
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  % SZS status Theorem for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  fof(f15,conjecture,(
% 7.53/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f16,negated_conjecture,(
% 7.53/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.53/1.49    inference(negated_conjecture,[],[f15])).
% 7.53/1.49  
% 7.53/1.49  fof(f37,plain,(
% 7.53/1.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.53/1.49    inference(ennf_transformation,[],[f16])).
% 7.53/1.49  
% 7.53/1.49  fof(f38,plain,(
% 7.53/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.53/1.49    inference(flattening,[],[f37])).
% 7.53/1.49  
% 7.53/1.49  fof(f42,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.53/1.49    introduced(choice_axiom,[])).
% 7.53/1.49  
% 7.53/1.49  fof(f41,plain,(
% 7.53/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.53/1.49    introduced(choice_axiom,[])).
% 7.53/1.49  
% 7.53/1.49  fof(f43,plain,(
% 7.53/1.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.53/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 7.53/1.49  
% 7.53/1.49  fof(f69,plain,(
% 7.53/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f72,plain,(
% 7.53/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f12,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f33,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.53/1.49    inference(ennf_transformation,[],[f12])).
% 7.53/1.49  
% 7.53/1.49  fof(f34,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.53/1.49    inference(flattening,[],[f33])).
% 7.53/1.49  
% 7.53/1.49  fof(f62,plain,(
% 7.53/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f34])).
% 7.53/1.49  
% 7.53/1.49  fof(f70,plain,(
% 7.53/1.49    v1_funct_1(sK3)),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f67,plain,(
% 7.53/1.49    v1_funct_1(sK2)),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f74,plain,(
% 7.53/1.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f8,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f27,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.53/1.49    inference(ennf_transformation,[],[f8])).
% 7.53/1.49  
% 7.53/1.49  fof(f28,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(flattening,[],[f27])).
% 7.53/1.49  
% 7.53/1.49  fof(f52,plain,(
% 7.53/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f28])).
% 7.53/1.49  
% 7.53/1.49  fof(f6,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f24,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.53/1.49    inference(ennf_transformation,[],[f6])).
% 7.53/1.49  
% 7.53/1.49  fof(f25,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(flattening,[],[f24])).
% 7.53/1.49  
% 7.53/1.49  fof(f50,plain,(
% 7.53/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f25])).
% 7.53/1.49  
% 7.53/1.49  fof(f9,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f29,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.53/1.49    inference(ennf_transformation,[],[f9])).
% 7.53/1.49  
% 7.53/1.49  fof(f30,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(flattening,[],[f29])).
% 7.53/1.49  
% 7.53/1.49  fof(f39,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(nnf_transformation,[],[f30])).
% 7.53/1.49  
% 7.53/1.49  fof(f53,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f39])).
% 7.53/1.49  
% 7.53/1.49  fof(f10,axiom,(
% 7.53/1.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f55,plain,(
% 7.53/1.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f10])).
% 7.53/1.49  
% 7.53/1.49  fof(f13,axiom,(
% 7.53/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f63,plain,(
% 7.53/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f13])).
% 7.53/1.49  
% 7.53/1.49  fof(f81,plain,(
% 7.53/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.53/1.49    inference(definition_unfolding,[],[f55,f63])).
% 7.53/1.49  
% 7.53/1.49  fof(f5,axiom,(
% 7.53/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f22,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f5])).
% 7.53/1.49  
% 7.53/1.49  fof(f23,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.53/1.49    inference(flattening,[],[f22])).
% 7.53/1.49  
% 7.53/1.49  fof(f49,plain,(
% 7.53/1.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f23])).
% 7.53/1.49  
% 7.53/1.49  fof(f80,plain,(
% 7.53/1.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.53/1.49    inference(definition_unfolding,[],[f49,f63])).
% 7.53/1.49  
% 7.53/1.49  fof(f3,axiom,(
% 7.53/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f18,plain,(
% 7.53/1.49    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f3])).
% 7.53/1.49  
% 7.53/1.49  fof(f19,plain,(
% 7.53/1.49    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.53/1.49    inference(flattening,[],[f18])).
% 7.53/1.49  
% 7.53/1.49  fof(f46,plain,(
% 7.53/1.49    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f19])).
% 7.53/1.49  
% 7.53/1.49  fof(f79,plain,(
% 7.53/1.49    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.53/1.49    inference(definition_unfolding,[],[f46,f63])).
% 7.53/1.49  
% 7.53/1.49  fof(f11,axiom,(
% 7.53/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f31,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(ennf_transformation,[],[f11])).
% 7.53/1.49  
% 7.53/1.49  fof(f32,plain,(
% 7.53/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(flattening,[],[f31])).
% 7.53/1.49  
% 7.53/1.49  fof(f40,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(nnf_transformation,[],[f32])).
% 7.53/1.49  
% 7.53/1.49  fof(f56,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f40])).
% 7.53/1.49  
% 7.53/1.49  fof(f7,axiom,(
% 7.53/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f26,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(ennf_transformation,[],[f7])).
% 7.53/1.49  
% 7.53/1.49  fof(f51,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f26])).
% 7.53/1.49  
% 7.53/1.49  fof(f68,plain,(
% 7.53/1.49    v1_funct_2(sK2,sK0,sK1)),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f77,plain,(
% 7.53/1.49    k1_xboole_0 != sK1),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f71,plain,(
% 7.53/1.49    v1_funct_2(sK3,sK1,sK0)),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f76,plain,(
% 7.53/1.49    k1_xboole_0 != sK0),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f73,plain,(
% 7.53/1.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f14,axiom,(
% 7.53/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f35,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.53/1.49    inference(ennf_transformation,[],[f14])).
% 7.53/1.49  
% 7.53/1.49  fof(f36,plain,(
% 7.53/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.53/1.49    inference(flattening,[],[f35])).
% 7.53/1.49  
% 7.53/1.49  fof(f66,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f36])).
% 7.53/1.49  
% 7.53/1.49  fof(f75,plain,(
% 7.53/1.49    v2_funct_1(sK2)),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f4,axiom,(
% 7.53/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f20,plain,(
% 7.53/1.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f4])).
% 7.53/1.49  
% 7.53/1.49  fof(f21,plain,(
% 7.53/1.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.53/1.49    inference(flattening,[],[f20])).
% 7.53/1.49  
% 7.53/1.49  fof(f47,plain,(
% 7.53/1.49    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f21])).
% 7.53/1.49  
% 7.53/1.49  fof(f1,axiom,(
% 7.53/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f17,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.53/1.49    inference(ennf_transformation,[],[f1])).
% 7.53/1.49  
% 7.53/1.49  fof(f44,plain,(
% 7.53/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f17])).
% 7.53/1.49  
% 7.53/1.49  fof(f2,axiom,(
% 7.53/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f45,plain,(
% 7.53/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f2])).
% 7.53/1.49  
% 7.53/1.49  fof(f65,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f36])).
% 7.53/1.49  
% 7.53/1.49  fof(f78,plain,(
% 7.53/1.49    k2_funct_1(sK2) != sK3),
% 7.53/1.49    inference(cnf_transformation,[],[f43])).
% 7.53/1.49  
% 7.53/1.49  cnf(c_31,negated_conjecture,
% 7.53/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.53/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_787,plain,
% 7.53/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_28,negated_conjecture,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.53/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_790,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_18,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v1_funct_1(X3)
% 7.53/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_796,plain,
% 7.53/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.53/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.53/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.53/1.49      | v1_funct_1(X5) != iProver_top
% 7.53/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6864,plain,
% 7.53/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.53/1.49      | v1_funct_1(X2) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_790,c_796]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_30,negated_conjecture,
% 7.53/1.49      ( v1_funct_1(sK3) ),
% 7.53/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_37,plain,
% 7.53/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8114,plain,
% 7.53/1.49      ( v1_funct_1(X2) != iProver_top
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.53/1.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_6864,c_37]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8115,plain,
% 7.53/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.53/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_8114]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8126,plain,
% 7.53/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.53/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_787,c_8115]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_33,negated_conjecture,
% 7.53/1.49      ( v1_funct_1(sK2) ),
% 7.53/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1297,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v1_funct_1(sK2)
% 7.53/1.49      | k1_partfun1(X3,X4,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1627,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.53/1.49      | ~ v1_funct_1(sK3)
% 7.53/1.49      | ~ v1_funct_1(sK2)
% 7.53/1.49      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1297]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2431,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ v1_funct_1(sK3)
% 7.53/1.49      | ~ v1_funct_1(sK2)
% 7.53/1.49      | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1627]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3515,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.53/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ v1_funct_1(sK3)
% 7.53/1.49      | ~ v1_funct_1(sK2)
% 7.53/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_2431]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8315,plain,
% 7.53/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_8126,c_33,c_31,c_30,c_28,c_3515]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_26,negated_conjecture,
% 7.53/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_791,plain,
% 7.53/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8318,plain,
% 7.53/1.49      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_8315,c_791]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.53/1.49      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_806,plain,
% 7.53/1.49      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.53/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.53/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5010,plain,
% 7.53/1.49      ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_790,c_806]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6580,plain,
% 7.53/1.49      ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_787,c_5010]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.53/1.49      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 7.53/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_808,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.53/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6750,plain,
% 7.53/1.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_6580,c_808]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_36,plain,
% 7.53/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_39,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11344,plain,
% 7.53/1.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_6750,c_36,c_39]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10,plain,
% 7.53/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.53/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | X3 = X2 ),
% 7.53/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_804,plain,
% 7.53/1.49      ( X0 = X1
% 7.53/1.49      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 7.53/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11363,plain,
% 7.53/1.49      ( k5_relat_1(sK2,sK3) = X0
% 7.53/1.49      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
% 7.53/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_11344,c_804]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14879,plain,
% 7.53/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.53/1.49      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_8318,c_11363]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11,plain,
% 7.53/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.53/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1476,plain,
% 7.53/1.49      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1479,plain,
% 7.53/1.49      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1476]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_23264,plain,
% 7.53/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_14879,c_1479]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5,plain,
% 7.53/1.49      ( ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v1_funct_1(X1)
% 7.53/1.49      | ~ v2_funct_1(X1)
% 7.53/1.49      | ~ v1_relat_1(X1)
% 7.53/1.49      | ~ v1_relat_1(X0)
% 7.53/1.49      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 7.53/1.49      | k2_relat_1(X1) != k1_relat_1(X0)
% 7.53/1.49      | k2_funct_1(X1) = X0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2,plain,
% 7.53/1.49      ( ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v1_funct_1(X1)
% 7.53/1.49      | v2_funct_1(X1)
% 7.53/1.49      | ~ v1_relat_1(X1)
% 7.53/1.49      | ~ v1_relat_1(X0)
% 7.53/1.49      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_257,plain,
% 7.53/1.49      ( ~ v1_funct_1(X1)
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v1_relat_1(X1)
% 7.53/1.49      | ~ v1_relat_1(X0)
% 7.53/1.49      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 7.53/1.49      | k2_relat_1(X1) != k1_relat_1(X0)
% 7.53/1.49      | k2_funct_1(X1) = X0 ),
% 7.53/1.49      inference(global_propositional_subsumption,[status(thm)],[c_5,c_2]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_258,plain,
% 7.53/1.49      ( ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v1_funct_1(X1)
% 7.53/1.49      | ~ v1_relat_1(X1)
% 7.53/1.49      | ~ v1_relat_1(X0)
% 7.53/1.49      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 7.53/1.49      | k2_relat_1(X1) != k1_relat_1(X0)
% 7.53/1.49      | k2_funct_1(X1) = X0 ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_257]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_784,plain,
% 7.53/1.49      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 7.53/1.49      | k2_relat_1(X0) != k1_relat_1(X1)
% 7.53/1.49      | k2_funct_1(X0) = X1
% 7.53/1.49      | v1_funct_1(X1) != iProver_top
% 7.53/1.49      | v1_funct_1(X0) != iProver_top
% 7.53/1.49      | v1_relat_1(X0) != iProver_top
% 7.53/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_23313,plain,
% 7.53/1.49      ( k2_relat_1(sK2) != k1_relat_1(sK3)
% 7.53/1.49      | k2_funct_1(sK2) = sK3
% 7.53/1.49      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top
% 7.53/1.49      | v1_funct_1(sK2) != iProver_top
% 7.53/1.49      | v1_relat_1(sK3) != iProver_top
% 7.53/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_23264,c_784]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_17,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.53/1.49      | k1_xboole_0 = X2 ),
% 7.53/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_797,plain,
% 7.53/1.49      ( k1_relset_1(X0,X1,X2) = X0
% 7.53/1.49      | k1_xboole_0 = X1
% 7.53/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3779,plain,
% 7.53/1.49      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 7.53/1.49      | sK1 = k1_xboole_0
% 7.53/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_787,c_797]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_807,plain,
% 7.53/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1742,plain,
% 7.53/1.49      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_787,c_807]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3783,plain,
% 7.53/1.49      ( k1_relat_1(sK2) = sK0
% 7.53/1.49      | sK1 = k1_xboole_0
% 7.53/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_3779,c_1742]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_32,negated_conjecture,
% 7.53/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35,plain,
% 7.53/1.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_23,negated_conjecture,
% 7.53/1.49      ( k1_xboole_0 != sK1 ),
% 7.53/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_284,plain,( X0 = X0 ),theory(equality) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_317,plain,
% 7.53/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_284]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_285,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1144,plain,
% 7.53/1.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_285]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1145,plain,
% 7.53/1.49      ( sK1 != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 = sK1
% 7.53/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1144]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4811,plain,
% 7.53/1.49      ( k1_relat_1(sK2) = sK0 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_3783,c_35,c_23,c_317,c_1145]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3778,plain,
% 7.53/1.49      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 7.53/1.49      | sK0 = k1_xboole_0
% 7.53/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_790,c_797]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1741,plain,
% 7.53/1.49      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_790,c_807]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3790,plain,
% 7.53/1.49      ( k1_relat_1(sK3) = sK1
% 7.53/1.49      | sK0 = k1_xboole_0
% 7.53/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_3778,c_1741]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_29,negated_conjecture,
% 7.53/1.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_38,plain,
% 7.53/1.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_24,negated_conjecture,
% 7.53/1.49      ( k1_xboole_0 != sK0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1146,plain,
% 7.53/1.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_285]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1147,plain,
% 7.53/1.49      ( sK0 != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 = sK0
% 7.53/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1146]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8517,plain,
% 7.53/1.49      ( k1_relat_1(sK3) = sK1 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_3790,c_38,c_24,c_317,c_1147]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_23321,plain,
% 7.53/1.49      ( k2_relat_1(sK2) != sK1
% 7.53/1.49      | k2_funct_1(sK2) = sK3
% 7.53/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top
% 7.53/1.49      | v1_funct_1(sK2) != iProver_top
% 7.53/1.49      | v1_relat_1(sK3) != iProver_top
% 7.53/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.53/1.49      inference(light_normalisation,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_23313,c_4811,c_8517]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_23322,plain,
% 7.53/1.49      ( k2_relat_1(sK2) != sK1
% 7.53/1.49      | k2_funct_1(sK2) = sK3
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top
% 7.53/1.49      | v1_funct_1(sK2) != iProver_top
% 7.53/1.49      | v1_relat_1(sK3) != iProver_top
% 7.53/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.53/1.49      inference(equality_resolution_simp,[status(thm)],[c_23321]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_27,negated_conjecture,
% 7.53/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.53/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_19,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v2_funct_1(X0)
% 7.53/1.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.53/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_795,plain,
% 7.53/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 7.53/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 7.53/1.49      | v1_funct_1(X2) != iProver_top
% 7.53/1.49      | v2_funct_1(X2) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4833,plain,
% 7.53/1.49      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 7.53/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(sK2) != iProver_top
% 7.53/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_27,c_795]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_34,plain,
% 7.53/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_25,negated_conjecture,
% 7.53/1.49      ( v2_funct_1(sK2) ),
% 7.53/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_41,plain,
% 7.53/1.49      ( v2_funct_1(sK2) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1282,plain,
% 7.53/1.49      ( ~ v1_funct_2(sK2,X0,X1)
% 7.53/1.49      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.53/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | ~ v1_funct_1(sK2)
% 7.53/1.49      | ~ v2_funct_1(sK2)
% 7.53/1.49      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1611,plain,
% 7.53/1.49      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.53/1.49      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.53/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ v1_funct_1(sK2)
% 7.53/1.49      | ~ v2_funct_1(sK2)
% 7.53/1.49      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1282]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1612,plain,
% 7.53/1.49      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 7.53/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 7.53/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(sK2) != iProver_top
% 7.53/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1611]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5876,plain,
% 7.53/1.49      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_4833,c_34,c_35,c_36,c_27,c_41,c_1612]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5883,plain,
% 7.53/1.49      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
% 7.53/1.49      | sK0 = k1_xboole_0
% 7.53/1.49      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_5876,c_797]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5884,plain,
% 7.53/1.49      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_5876,c_807]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_785,plain,
% 7.53/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4,plain,
% 7.53/1.49      ( ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v2_funct_1(X0)
% 7.53/1.49      | ~ v1_relat_1(X0)
% 7.53/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_809,plain,
% 7.53/1.49      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.53/1.49      | v1_funct_1(X0) != iProver_top
% 7.53/1.49      | v2_funct_1(X0) != iProver_top
% 7.53/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3064,plain,
% 7.53/1.49      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.53/1.49      | v2_funct_1(sK2) != iProver_top
% 7.53/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_785,c_809]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1151,plain,
% 7.53/1.49      ( ~ v1_funct_1(sK2)
% 7.53/1.49      | ~ v2_funct_1(sK2)
% 7.53/1.49      | ~ v1_relat_1(sK2)
% 7.53/1.49      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_0,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.53/1.49      | ~ v1_relat_1(X1)
% 7.53/1.49      | v1_relat_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1370,plain,
% 7.53/1.49      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 7.53/1.49      inference(resolution,[status(thm)],[c_0,c_31]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1,plain,
% 7.53/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1444,plain,
% 7.53/1.49      ( v1_relat_1(sK2) ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_1370,c_1]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4152,plain,
% 7.53/1.49      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_3064,c_33,c_25,c_1151,c_1444]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5896,plain,
% 7.53/1.49      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.53/1.49      inference(light_normalisation,[status(thm)],[c_5884,c_4152]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5898,plain,
% 7.53/1.49      ( k2_relat_1(sK2) = sK1
% 7.53/1.49      | sK0 = k1_xboole_0
% 7.53/1.49      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_5883,c_5896]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_20,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.53/1.49      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | ~ v2_funct_1(X0)
% 7.53/1.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.53/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1287,plain,
% 7.53/1.49      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 7.53/1.49      | ~ v1_funct_2(sK2,X1,X0)
% 7.53/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.53/1.49      | ~ v1_funct_1(sK2)
% 7.53/1.49      | ~ v2_funct_1(sK2)
% 7.53/1.49      | k2_relset_1(X1,X0,sK2) != X0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1614,plain,
% 7.53/1.49      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 7.53/1.49      | ~ v1_funct_2(sK2,sK0,sK1)
% 7.53/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ v1_funct_1(sK2)
% 7.53/1.49      | ~ v2_funct_1(sK2)
% 7.53/1.49      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1287]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1615,plain,
% 7.53/1.49      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 7.53/1.49      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
% 7.53/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(sK2) != iProver_top
% 7.53/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1614]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1445,plain,
% 7.53/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1368,plain,
% 7.53/1.49      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) ),
% 7.53/1.49      inference(resolution,[status(thm)],[c_0,c_28]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1386,plain,
% 7.53/1.49      ( v1_relat_1(sK3) ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_1368,c_1]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1387,plain,
% 7.53/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1386]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_22,negated_conjecture,
% 7.53/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.53/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(contradiction,plain,
% 7.53/1.49      ( $false ),
% 7.53/1.49      inference(minisat,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_23322,c_5898,c_1615,c_1445,c_1387,c_1147,c_317,c_22,
% 7.53/1.49                 c_24,c_41,c_27,c_37,c_36,c_35,c_34]) ).
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  ------                               Statistics
% 7.53/1.49  
% 7.53/1.49  ------ Selected
% 7.53/1.49  
% 7.53/1.49  total_time:                             0.838
% 7.53/1.49  
%------------------------------------------------------------------------------
