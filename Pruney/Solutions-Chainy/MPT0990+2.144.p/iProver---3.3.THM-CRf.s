%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:27 EST 2020

% Result     : Theorem 15.58s
% Output     : CNFRefutation 15.58s
% Verified   : 
% Statistics : Number of formulae       :  184 (1147 expanded)
%              Number of clauses        :  109 ( 354 expanded)
%              Number of leaves         :   21 ( 289 expanded)
%              Depth                    :   22
%              Number of atoms          :  680 (9247 expanded)
%              Number of equality atoms :  333 (3412 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f70])).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f45,f44])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f43,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
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
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f70])).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f38])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1208,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1187,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1202,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2165,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1187,c_1202])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2166,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2165,c_29])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1190,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1196,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3523,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1196])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1203,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2207,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1190,c_1203])).

cnf(c_3526,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3523,c_2207])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_672,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_701,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_673,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1292,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_1293,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_5680,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3526,c_40,c_26,c_701,c_1293])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1206,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5683,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5680,c_1206])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2212,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1212])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2331,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2332,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2331])).

cnf(c_38410,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5683,c_39,c_2212,c_2332])).

cnf(c_38411,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_38410])).

cnf(c_38416,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_38411])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1192,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2652,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1192])).

cnf(c_3209,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2652,c_39])).

cnf(c_3210,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3209])).

cnf(c_3217,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_3210])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_395,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_403,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_395,c_21])).

cnf(c_1183,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1294,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1943,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1183,c_35,c_33,c_32,c_30,c_403,c_1294])).

cnf(c_3218,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3217,c_1943])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3774,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3218,c_36])).

cnf(c_38418,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38416,c_3774])).

cnf(c_1211,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2213,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_1212])).

cnf(c_2468,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_2213])).

cnf(c_38461,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38418,c_36,c_2468])).

cnf(c_38462,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_38461])).

cnf(c_38465,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_38462])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1204,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4351,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3774,c_1204])).

cnf(c_2164,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1190,c_1202])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_407,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_408,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_493,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_408])).

cnf(c_1182,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_1682,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1182])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2009,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1682,c_36,c_37,c_38,c_39,c_40,c_41])).

cnf(c_2167,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2164,c_2009])).

cnf(c_4352,plain,
    ( k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4351,c_2166,c_2167])).

cnf(c_4353,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4352])).

cnf(c_4934,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4353,c_36,c_39,c_40,c_26,c_701,c_1293,c_2212,c_2332,c_2468,c_3526])).

cnf(c_39383,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_38465,c_4934])).

cnf(c_1188,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1209,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2706,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1209])).

cnf(c_2893,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2706,c_2212,c_2332])).

cnf(c_2894,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2893])).

cnf(c_39384,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_38465,c_2894])).

cnf(c_39385,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_39383,c_39384])).

cnf(c_2462,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2212,c_2332])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1210,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2466,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2462,c_1210])).

cnf(c_43653,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_39385,c_2466])).

cnf(c_1185,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2707,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_1209])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3050,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2707,c_43,c_2468])).

cnf(c_24,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3052,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_3050,c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43653,c_3052])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:52:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.58/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.58/2.49  
% 15.58/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.58/2.49  
% 15.58/2.49  ------  iProver source info
% 15.58/2.49  
% 15.58/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.58/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.58/2.49  git: non_committed_changes: false
% 15.58/2.49  git: last_make_outside_of_git: false
% 15.58/2.49  
% 15.58/2.49  ------ 
% 15.58/2.49  
% 15.58/2.49  ------ Input Options
% 15.58/2.49  
% 15.58/2.49  --out_options                           all
% 15.58/2.49  --tptp_safe_out                         true
% 15.58/2.49  --problem_path                          ""
% 15.58/2.49  --include_path                          ""
% 15.58/2.49  --clausifier                            res/vclausify_rel
% 15.58/2.49  --clausifier_options                    ""
% 15.58/2.49  --stdin                                 false
% 15.58/2.49  --stats_out                             all
% 15.58/2.49  
% 15.58/2.49  ------ General Options
% 15.58/2.49  
% 15.58/2.49  --fof                                   false
% 15.58/2.49  --time_out_real                         305.
% 15.58/2.49  --time_out_virtual                      -1.
% 15.58/2.49  --symbol_type_check                     false
% 15.58/2.49  --clausify_out                          false
% 15.58/2.49  --sig_cnt_out                           false
% 15.58/2.49  --trig_cnt_out                          false
% 15.58/2.49  --trig_cnt_out_tolerance                1.
% 15.58/2.49  --trig_cnt_out_sk_spl                   false
% 15.58/2.49  --abstr_cl_out                          false
% 15.58/2.49  
% 15.58/2.49  ------ Global Options
% 15.58/2.49  
% 15.58/2.49  --schedule                              default
% 15.58/2.49  --add_important_lit                     false
% 15.58/2.49  --prop_solver_per_cl                    1000
% 15.58/2.49  --min_unsat_core                        false
% 15.58/2.49  --soft_assumptions                      false
% 15.58/2.49  --soft_lemma_size                       3
% 15.58/2.49  --prop_impl_unit_size                   0
% 15.58/2.49  --prop_impl_unit                        []
% 15.58/2.49  --share_sel_clauses                     true
% 15.58/2.49  --reset_solvers                         false
% 15.58/2.49  --bc_imp_inh                            [conj_cone]
% 15.58/2.49  --conj_cone_tolerance                   3.
% 15.58/2.49  --extra_neg_conj                        none
% 15.58/2.49  --large_theory_mode                     true
% 15.58/2.49  --prolific_symb_bound                   200
% 15.58/2.49  --lt_threshold                          2000
% 15.58/2.49  --clause_weak_htbl                      true
% 15.58/2.49  --gc_record_bc_elim                     false
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing Options
% 15.58/2.49  
% 15.58/2.49  --preprocessing_flag                    true
% 15.58/2.49  --time_out_prep_mult                    0.1
% 15.58/2.49  --splitting_mode                        input
% 15.58/2.49  --splitting_grd                         true
% 15.58/2.49  --splitting_cvd                         false
% 15.58/2.49  --splitting_cvd_svl                     false
% 15.58/2.49  --splitting_nvd                         32
% 15.58/2.49  --sub_typing                            true
% 15.58/2.49  --prep_gs_sim                           true
% 15.58/2.49  --prep_unflatten                        true
% 15.58/2.49  --prep_res_sim                          true
% 15.58/2.49  --prep_upred                            true
% 15.58/2.49  --prep_sem_filter                       exhaustive
% 15.58/2.49  --prep_sem_filter_out                   false
% 15.58/2.49  --pred_elim                             true
% 15.58/2.49  --res_sim_input                         true
% 15.58/2.49  --eq_ax_congr_red                       true
% 15.58/2.49  --pure_diseq_elim                       true
% 15.58/2.49  --brand_transform                       false
% 15.58/2.49  --non_eq_to_eq                          false
% 15.58/2.49  --prep_def_merge                        true
% 15.58/2.49  --prep_def_merge_prop_impl              false
% 15.58/2.49  --prep_def_merge_mbd                    true
% 15.58/2.49  --prep_def_merge_tr_red                 false
% 15.58/2.49  --prep_def_merge_tr_cl                  false
% 15.58/2.49  --smt_preprocessing                     true
% 15.58/2.49  --smt_ac_axioms                         fast
% 15.58/2.49  --preprocessed_out                      false
% 15.58/2.49  --preprocessed_stats                    false
% 15.58/2.49  
% 15.58/2.49  ------ Abstraction refinement Options
% 15.58/2.49  
% 15.58/2.49  --abstr_ref                             []
% 15.58/2.49  --abstr_ref_prep                        false
% 15.58/2.49  --abstr_ref_until_sat                   false
% 15.58/2.49  --abstr_ref_sig_restrict                funpre
% 15.58/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.58/2.49  --abstr_ref_under                       []
% 15.58/2.49  
% 15.58/2.49  ------ SAT Options
% 15.58/2.49  
% 15.58/2.49  --sat_mode                              false
% 15.58/2.49  --sat_fm_restart_options                ""
% 15.58/2.49  --sat_gr_def                            false
% 15.58/2.49  --sat_epr_types                         true
% 15.58/2.49  --sat_non_cyclic_types                  false
% 15.58/2.49  --sat_finite_models                     false
% 15.58/2.49  --sat_fm_lemmas                         false
% 15.58/2.49  --sat_fm_prep                           false
% 15.58/2.49  --sat_fm_uc_incr                        true
% 15.58/2.49  --sat_out_model                         small
% 15.58/2.49  --sat_out_clauses                       false
% 15.58/2.49  
% 15.58/2.49  ------ QBF Options
% 15.58/2.49  
% 15.58/2.49  --qbf_mode                              false
% 15.58/2.49  --qbf_elim_univ                         false
% 15.58/2.49  --qbf_dom_inst                          none
% 15.58/2.49  --qbf_dom_pre_inst                      false
% 15.58/2.49  --qbf_sk_in                             false
% 15.58/2.49  --qbf_pred_elim                         true
% 15.58/2.49  --qbf_split                             512
% 15.58/2.49  
% 15.58/2.49  ------ BMC1 Options
% 15.58/2.49  
% 15.58/2.49  --bmc1_incremental                      false
% 15.58/2.49  --bmc1_axioms                           reachable_all
% 15.58/2.49  --bmc1_min_bound                        0
% 15.58/2.49  --bmc1_max_bound                        -1
% 15.58/2.49  --bmc1_max_bound_default                -1
% 15.58/2.49  --bmc1_symbol_reachability              true
% 15.58/2.49  --bmc1_property_lemmas                  false
% 15.58/2.49  --bmc1_k_induction                      false
% 15.58/2.49  --bmc1_non_equiv_states                 false
% 15.58/2.49  --bmc1_deadlock                         false
% 15.58/2.49  --bmc1_ucm                              false
% 15.58/2.49  --bmc1_add_unsat_core                   none
% 15.58/2.49  --bmc1_unsat_core_children              false
% 15.58/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.58/2.49  --bmc1_out_stat                         full
% 15.58/2.49  --bmc1_ground_init                      false
% 15.58/2.49  --bmc1_pre_inst_next_state              false
% 15.58/2.49  --bmc1_pre_inst_state                   false
% 15.58/2.49  --bmc1_pre_inst_reach_state             false
% 15.58/2.49  --bmc1_out_unsat_core                   false
% 15.58/2.49  --bmc1_aig_witness_out                  false
% 15.58/2.49  --bmc1_verbose                          false
% 15.58/2.49  --bmc1_dump_clauses_tptp                false
% 15.58/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.58/2.49  --bmc1_dump_file                        -
% 15.58/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.58/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.58/2.49  --bmc1_ucm_extend_mode                  1
% 15.58/2.49  --bmc1_ucm_init_mode                    2
% 15.58/2.49  --bmc1_ucm_cone_mode                    none
% 15.58/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.58/2.49  --bmc1_ucm_relax_model                  4
% 15.58/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.58/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.58/2.49  --bmc1_ucm_layered_model                none
% 15.58/2.49  --bmc1_ucm_max_lemma_size               10
% 15.58/2.49  
% 15.58/2.49  ------ AIG Options
% 15.58/2.49  
% 15.58/2.49  --aig_mode                              false
% 15.58/2.49  
% 15.58/2.49  ------ Instantiation Options
% 15.58/2.49  
% 15.58/2.49  --instantiation_flag                    true
% 15.58/2.49  --inst_sos_flag                         true
% 15.58/2.49  --inst_sos_phase                        true
% 15.58/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.58/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.58/2.49  --inst_lit_sel_side                     num_symb
% 15.58/2.49  --inst_solver_per_active                1400
% 15.58/2.49  --inst_solver_calls_frac                1.
% 15.58/2.49  --inst_passive_queue_type               priority_queues
% 15.58/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.58/2.49  --inst_passive_queues_freq              [25;2]
% 15.58/2.49  --inst_dismatching                      true
% 15.58/2.49  --inst_eager_unprocessed_to_passive     true
% 15.58/2.49  --inst_prop_sim_given                   true
% 15.58/2.49  --inst_prop_sim_new                     false
% 15.58/2.49  --inst_subs_new                         false
% 15.58/2.49  --inst_eq_res_simp                      false
% 15.58/2.49  --inst_subs_given                       false
% 15.58/2.49  --inst_orphan_elimination               true
% 15.58/2.49  --inst_learning_loop_flag               true
% 15.58/2.49  --inst_learning_start                   3000
% 15.58/2.49  --inst_learning_factor                  2
% 15.58/2.49  --inst_start_prop_sim_after_learn       3
% 15.58/2.49  --inst_sel_renew                        solver
% 15.58/2.49  --inst_lit_activity_flag                true
% 15.58/2.49  --inst_restr_to_given                   false
% 15.58/2.49  --inst_activity_threshold               500
% 15.58/2.49  --inst_out_proof                        true
% 15.58/2.49  
% 15.58/2.49  ------ Resolution Options
% 15.58/2.49  
% 15.58/2.49  --resolution_flag                       true
% 15.58/2.49  --res_lit_sel                           adaptive
% 15.58/2.49  --res_lit_sel_side                      none
% 15.58/2.49  --res_ordering                          kbo
% 15.58/2.49  --res_to_prop_solver                    active
% 15.58/2.49  --res_prop_simpl_new                    false
% 15.58/2.49  --res_prop_simpl_given                  true
% 15.58/2.49  --res_passive_queue_type                priority_queues
% 15.58/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.58/2.49  --res_passive_queues_freq               [15;5]
% 15.58/2.49  --res_forward_subs                      full
% 15.58/2.49  --res_backward_subs                     full
% 15.58/2.49  --res_forward_subs_resolution           true
% 15.58/2.49  --res_backward_subs_resolution          true
% 15.58/2.49  --res_orphan_elimination                true
% 15.58/2.49  --res_time_limit                        2.
% 15.58/2.49  --res_out_proof                         true
% 15.58/2.49  
% 15.58/2.49  ------ Superposition Options
% 15.58/2.49  
% 15.58/2.49  --superposition_flag                    true
% 15.58/2.49  --sup_passive_queue_type                priority_queues
% 15.58/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.58/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.58/2.49  --demod_completeness_check              fast
% 15.58/2.49  --demod_use_ground                      true
% 15.58/2.49  --sup_to_prop_solver                    passive
% 15.58/2.49  --sup_prop_simpl_new                    true
% 15.58/2.49  --sup_prop_simpl_given                  true
% 15.58/2.49  --sup_fun_splitting                     true
% 15.58/2.49  --sup_smt_interval                      50000
% 15.58/2.49  
% 15.58/2.49  ------ Superposition Simplification Setup
% 15.58/2.49  
% 15.58/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.58/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.58/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.58/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.58/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.58/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.58/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.58/2.49  --sup_immed_triv                        [TrivRules]
% 15.58/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.49  --sup_immed_bw_main                     []
% 15.58/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.58/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.58/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.49  --sup_input_bw                          []
% 15.58/2.49  
% 15.58/2.49  ------ Combination Options
% 15.58/2.49  
% 15.58/2.49  --comb_res_mult                         3
% 15.58/2.49  --comb_sup_mult                         2
% 15.58/2.49  --comb_inst_mult                        10
% 15.58/2.49  
% 15.58/2.49  ------ Debug Options
% 15.58/2.49  
% 15.58/2.49  --dbg_backtrace                         false
% 15.58/2.49  --dbg_dump_prop_clauses                 false
% 15.58/2.49  --dbg_dump_prop_clauses_file            -
% 15.58/2.49  --dbg_out_stat                          false
% 15.58/2.49  ------ Parsing...
% 15.58/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.58/2.49  ------ Proving...
% 15.58/2.49  ------ Problem Properties 
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  clauses                                 35
% 15.58/2.49  conjectures                             11
% 15.58/2.49  EPR                                     7
% 15.58/2.49  Horn                                    31
% 15.58/2.49  unary                                   15
% 15.58/2.49  binary                                  4
% 15.58/2.49  lits                                    104
% 15.58/2.49  lits eq                                 28
% 15.58/2.49  fd_pure                                 0
% 15.58/2.49  fd_pseudo                               0
% 15.58/2.49  fd_cond                                 3
% 15.58/2.49  fd_pseudo_cond                          1
% 15.58/2.49  AC symbols                              0
% 15.58/2.49  
% 15.58/2.49  ------ Schedule dynamic 5 is on 
% 15.58/2.49  
% 15.58/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  ------ 
% 15.58/2.49  Current options:
% 15.58/2.49  ------ 
% 15.58/2.49  
% 15.58/2.49  ------ Input Options
% 15.58/2.49  
% 15.58/2.49  --out_options                           all
% 15.58/2.49  --tptp_safe_out                         true
% 15.58/2.49  --problem_path                          ""
% 15.58/2.49  --include_path                          ""
% 15.58/2.49  --clausifier                            res/vclausify_rel
% 15.58/2.49  --clausifier_options                    ""
% 15.58/2.49  --stdin                                 false
% 15.58/2.49  --stats_out                             all
% 15.58/2.49  
% 15.58/2.49  ------ General Options
% 15.58/2.49  
% 15.58/2.49  --fof                                   false
% 15.58/2.49  --time_out_real                         305.
% 15.58/2.49  --time_out_virtual                      -1.
% 15.58/2.49  --symbol_type_check                     false
% 15.58/2.49  --clausify_out                          false
% 15.58/2.49  --sig_cnt_out                           false
% 15.58/2.49  --trig_cnt_out                          false
% 15.58/2.49  --trig_cnt_out_tolerance                1.
% 15.58/2.49  --trig_cnt_out_sk_spl                   false
% 15.58/2.49  --abstr_cl_out                          false
% 15.58/2.49  
% 15.58/2.49  ------ Global Options
% 15.58/2.49  
% 15.58/2.49  --schedule                              default
% 15.58/2.49  --add_important_lit                     false
% 15.58/2.49  --prop_solver_per_cl                    1000
% 15.58/2.49  --min_unsat_core                        false
% 15.58/2.49  --soft_assumptions                      false
% 15.58/2.49  --soft_lemma_size                       3
% 15.58/2.49  --prop_impl_unit_size                   0
% 15.58/2.49  --prop_impl_unit                        []
% 15.58/2.49  --share_sel_clauses                     true
% 15.58/2.49  --reset_solvers                         false
% 15.58/2.49  --bc_imp_inh                            [conj_cone]
% 15.58/2.49  --conj_cone_tolerance                   3.
% 15.58/2.49  --extra_neg_conj                        none
% 15.58/2.49  --large_theory_mode                     true
% 15.58/2.49  --prolific_symb_bound                   200
% 15.58/2.49  --lt_threshold                          2000
% 15.58/2.49  --clause_weak_htbl                      true
% 15.58/2.49  --gc_record_bc_elim                     false
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing Options
% 15.58/2.49  
% 15.58/2.49  --preprocessing_flag                    true
% 15.58/2.49  --time_out_prep_mult                    0.1
% 15.58/2.49  --splitting_mode                        input
% 15.58/2.49  --splitting_grd                         true
% 15.58/2.49  --splitting_cvd                         false
% 15.58/2.49  --splitting_cvd_svl                     false
% 15.58/2.49  --splitting_nvd                         32
% 15.58/2.49  --sub_typing                            true
% 15.58/2.49  --prep_gs_sim                           true
% 15.58/2.49  --prep_unflatten                        true
% 15.58/2.49  --prep_res_sim                          true
% 15.58/2.49  --prep_upred                            true
% 15.58/2.49  --prep_sem_filter                       exhaustive
% 15.58/2.49  --prep_sem_filter_out                   false
% 15.58/2.49  --pred_elim                             true
% 15.58/2.49  --res_sim_input                         true
% 15.58/2.49  --eq_ax_congr_red                       true
% 15.58/2.49  --pure_diseq_elim                       true
% 15.58/2.49  --brand_transform                       false
% 15.58/2.49  --non_eq_to_eq                          false
% 15.58/2.49  --prep_def_merge                        true
% 15.58/2.49  --prep_def_merge_prop_impl              false
% 15.58/2.49  --prep_def_merge_mbd                    true
% 15.58/2.49  --prep_def_merge_tr_red                 false
% 15.58/2.49  --prep_def_merge_tr_cl                  false
% 15.58/2.49  --smt_preprocessing                     true
% 15.58/2.49  --smt_ac_axioms                         fast
% 15.58/2.49  --preprocessed_out                      false
% 15.58/2.49  --preprocessed_stats                    false
% 15.58/2.49  
% 15.58/2.49  ------ Abstraction refinement Options
% 15.58/2.49  
% 15.58/2.49  --abstr_ref                             []
% 15.58/2.49  --abstr_ref_prep                        false
% 15.58/2.49  --abstr_ref_until_sat                   false
% 15.58/2.49  --abstr_ref_sig_restrict                funpre
% 15.58/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.58/2.49  --abstr_ref_under                       []
% 15.58/2.49  
% 15.58/2.49  ------ SAT Options
% 15.58/2.49  
% 15.58/2.49  --sat_mode                              false
% 15.58/2.49  --sat_fm_restart_options                ""
% 15.58/2.49  --sat_gr_def                            false
% 15.58/2.49  --sat_epr_types                         true
% 15.58/2.49  --sat_non_cyclic_types                  false
% 15.58/2.49  --sat_finite_models                     false
% 15.58/2.49  --sat_fm_lemmas                         false
% 15.58/2.49  --sat_fm_prep                           false
% 15.58/2.49  --sat_fm_uc_incr                        true
% 15.58/2.49  --sat_out_model                         small
% 15.58/2.49  --sat_out_clauses                       false
% 15.58/2.49  
% 15.58/2.49  ------ QBF Options
% 15.58/2.49  
% 15.58/2.49  --qbf_mode                              false
% 15.58/2.49  --qbf_elim_univ                         false
% 15.58/2.49  --qbf_dom_inst                          none
% 15.58/2.49  --qbf_dom_pre_inst                      false
% 15.58/2.49  --qbf_sk_in                             false
% 15.58/2.49  --qbf_pred_elim                         true
% 15.58/2.49  --qbf_split                             512
% 15.58/2.49  
% 15.58/2.49  ------ BMC1 Options
% 15.58/2.49  
% 15.58/2.49  --bmc1_incremental                      false
% 15.58/2.49  --bmc1_axioms                           reachable_all
% 15.58/2.49  --bmc1_min_bound                        0
% 15.58/2.49  --bmc1_max_bound                        -1
% 15.58/2.49  --bmc1_max_bound_default                -1
% 15.58/2.49  --bmc1_symbol_reachability              true
% 15.58/2.49  --bmc1_property_lemmas                  false
% 15.58/2.49  --bmc1_k_induction                      false
% 15.58/2.49  --bmc1_non_equiv_states                 false
% 15.58/2.49  --bmc1_deadlock                         false
% 15.58/2.49  --bmc1_ucm                              false
% 15.58/2.49  --bmc1_add_unsat_core                   none
% 15.58/2.49  --bmc1_unsat_core_children              false
% 15.58/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.58/2.49  --bmc1_out_stat                         full
% 15.58/2.49  --bmc1_ground_init                      false
% 15.58/2.49  --bmc1_pre_inst_next_state              false
% 15.58/2.49  --bmc1_pre_inst_state                   false
% 15.58/2.49  --bmc1_pre_inst_reach_state             false
% 15.58/2.49  --bmc1_out_unsat_core                   false
% 15.58/2.49  --bmc1_aig_witness_out                  false
% 15.58/2.49  --bmc1_verbose                          false
% 15.58/2.49  --bmc1_dump_clauses_tptp                false
% 15.58/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.58/2.49  --bmc1_dump_file                        -
% 15.58/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.58/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.58/2.49  --bmc1_ucm_extend_mode                  1
% 15.58/2.49  --bmc1_ucm_init_mode                    2
% 15.58/2.49  --bmc1_ucm_cone_mode                    none
% 15.58/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.58/2.49  --bmc1_ucm_relax_model                  4
% 15.58/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.58/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.58/2.49  --bmc1_ucm_layered_model                none
% 15.58/2.49  --bmc1_ucm_max_lemma_size               10
% 15.58/2.49  
% 15.58/2.49  ------ AIG Options
% 15.58/2.49  
% 15.58/2.49  --aig_mode                              false
% 15.58/2.49  
% 15.58/2.49  ------ Instantiation Options
% 15.58/2.49  
% 15.58/2.49  --instantiation_flag                    true
% 15.58/2.49  --inst_sos_flag                         true
% 15.58/2.49  --inst_sos_phase                        true
% 15.58/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.58/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.58/2.49  --inst_lit_sel_side                     none
% 15.58/2.49  --inst_solver_per_active                1400
% 15.58/2.49  --inst_solver_calls_frac                1.
% 15.58/2.49  --inst_passive_queue_type               priority_queues
% 15.58/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.58/2.49  --inst_passive_queues_freq              [25;2]
% 15.58/2.49  --inst_dismatching                      true
% 15.58/2.49  --inst_eager_unprocessed_to_passive     true
% 15.58/2.49  --inst_prop_sim_given                   true
% 15.58/2.49  --inst_prop_sim_new                     false
% 15.58/2.49  --inst_subs_new                         false
% 15.58/2.49  --inst_eq_res_simp                      false
% 15.58/2.49  --inst_subs_given                       false
% 15.58/2.49  --inst_orphan_elimination               true
% 15.58/2.49  --inst_learning_loop_flag               true
% 15.58/2.49  --inst_learning_start                   3000
% 15.58/2.49  --inst_learning_factor                  2
% 15.58/2.49  --inst_start_prop_sim_after_learn       3
% 15.58/2.49  --inst_sel_renew                        solver
% 15.58/2.49  --inst_lit_activity_flag                true
% 15.58/2.49  --inst_restr_to_given                   false
% 15.58/2.49  --inst_activity_threshold               500
% 15.58/2.49  --inst_out_proof                        true
% 15.58/2.49  
% 15.58/2.49  ------ Resolution Options
% 15.58/2.49  
% 15.58/2.49  --resolution_flag                       false
% 15.58/2.49  --res_lit_sel                           adaptive
% 15.58/2.49  --res_lit_sel_side                      none
% 15.58/2.49  --res_ordering                          kbo
% 15.58/2.49  --res_to_prop_solver                    active
% 15.58/2.49  --res_prop_simpl_new                    false
% 15.58/2.49  --res_prop_simpl_given                  true
% 15.58/2.49  --res_passive_queue_type                priority_queues
% 15.58/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.58/2.49  --res_passive_queues_freq               [15;5]
% 15.58/2.49  --res_forward_subs                      full
% 15.58/2.49  --res_backward_subs                     full
% 15.58/2.49  --res_forward_subs_resolution           true
% 15.58/2.49  --res_backward_subs_resolution          true
% 15.58/2.49  --res_orphan_elimination                true
% 15.58/2.49  --res_time_limit                        2.
% 15.58/2.49  --res_out_proof                         true
% 15.58/2.49  
% 15.58/2.49  ------ Superposition Options
% 15.58/2.49  
% 15.58/2.49  --superposition_flag                    true
% 15.58/2.49  --sup_passive_queue_type                priority_queues
% 15.58/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.58/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.58/2.49  --demod_completeness_check              fast
% 15.58/2.49  --demod_use_ground                      true
% 15.58/2.49  --sup_to_prop_solver                    passive
% 15.58/2.49  --sup_prop_simpl_new                    true
% 15.58/2.49  --sup_prop_simpl_given                  true
% 15.58/2.49  --sup_fun_splitting                     true
% 15.58/2.49  --sup_smt_interval                      50000
% 15.58/2.49  
% 15.58/2.49  ------ Superposition Simplification Setup
% 15.58/2.49  
% 15.58/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.58/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.58/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.58/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.58/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.58/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.58/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.58/2.49  --sup_immed_triv                        [TrivRules]
% 15.58/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.49  --sup_immed_bw_main                     []
% 15.58/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.58/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.58/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.49  --sup_input_bw                          []
% 15.58/2.49  
% 15.58/2.49  ------ Combination Options
% 15.58/2.49  
% 15.58/2.49  --comb_res_mult                         3
% 15.58/2.49  --comb_sup_mult                         2
% 15.58/2.49  --comb_inst_mult                        10
% 15.58/2.49  
% 15.58/2.49  ------ Debug Options
% 15.58/2.49  
% 15.58/2.49  --dbg_backtrace                         false
% 15.58/2.49  --dbg_dump_prop_clauses                 false
% 15.58/2.49  --dbg_dump_prop_clauses_file            -
% 15.58/2.49  --dbg_out_stat                          false
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  ------ Proving...
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  % SZS status Theorem for theBenchmark.p
% 15.58/2.49  
% 15.58/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.58/2.49  
% 15.58/2.49  fof(f5,axiom,(
% 15.58/2.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f52,plain,(
% 15.58/2.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f5])).
% 15.58/2.49  
% 15.58/2.49  fof(f15,axiom,(
% 15.58/2.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f70,plain,(
% 15.58/2.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f15])).
% 15.58/2.49  
% 15.58/2.49  fof(f84,plain,(
% 15.58/2.49    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 15.58/2.49    inference(definition_unfolding,[],[f52,f70])).
% 15.58/2.49  
% 15.58/2.49  fof(f17,conjecture,(
% 15.58/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f18,negated_conjecture,(
% 15.58/2.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.58/2.49    inference(negated_conjecture,[],[f17])).
% 15.58/2.49  
% 15.58/2.49  fof(f40,plain,(
% 15.58/2.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.58/2.49    inference(ennf_transformation,[],[f18])).
% 15.58/2.49  
% 15.58/2.49  fof(f41,plain,(
% 15.58/2.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.58/2.49    inference(flattening,[],[f40])).
% 15.58/2.49  
% 15.58/2.49  fof(f45,plain,(
% 15.58/2.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 15.58/2.49    introduced(choice_axiom,[])).
% 15.58/2.49  
% 15.58/2.49  fof(f44,plain,(
% 15.58/2.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 15.58/2.49    introduced(choice_axiom,[])).
% 15.58/2.49  
% 15.58/2.49  fof(f46,plain,(
% 15.58/2.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 15.58/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f45,f44])).
% 15.58/2.49  
% 15.58/2.49  fof(f74,plain,(
% 15.58/2.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f9,axiom,(
% 15.58/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f29,plain,(
% 15.58/2.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.58/2.49    inference(ennf_transformation,[],[f9])).
% 15.58/2.49  
% 15.58/2.49  fof(f57,plain,(
% 15.58/2.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f29])).
% 15.58/2.49  
% 15.58/2.49  fof(f78,plain,(
% 15.58/2.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f77,plain,(
% 15.58/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f11,axiom,(
% 15.58/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f32,plain,(
% 15.58/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.58/2.49    inference(ennf_transformation,[],[f11])).
% 15.58/2.49  
% 15.58/2.49  fof(f33,plain,(
% 15.58/2.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.58/2.49    inference(flattening,[],[f32])).
% 15.58/2.49  
% 15.58/2.49  fof(f43,plain,(
% 15.58/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.58/2.49    inference(nnf_transformation,[],[f33])).
% 15.58/2.49  
% 15.58/2.49  fof(f60,plain,(
% 15.58/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f43])).
% 15.58/2.49  
% 15.58/2.49  fof(f8,axiom,(
% 15.58/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f28,plain,(
% 15.58/2.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.58/2.49    inference(ennf_transformation,[],[f8])).
% 15.58/2.49  
% 15.58/2.49  fof(f56,plain,(
% 15.58/2.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f28])).
% 15.58/2.49  
% 15.58/2.49  fof(f76,plain,(
% 15.58/2.49    v1_funct_2(sK3,sK1,sK0)),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f81,plain,(
% 15.58/2.49    k1_xboole_0 != sK0),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f6,axiom,(
% 15.58/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f24,plain,(
% 15.58/2.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.58/2.49    inference(ennf_transformation,[],[f6])).
% 15.58/2.49  
% 15.58/2.49  fof(f25,plain,(
% 15.58/2.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.58/2.49    inference(flattening,[],[f24])).
% 15.58/2.49  
% 15.58/2.49  fof(f54,plain,(
% 15.58/2.49    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f25])).
% 15.58/2.49  
% 15.58/2.49  fof(f75,plain,(
% 15.58/2.49    v1_funct_1(sK3)),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f1,axiom,(
% 15.58/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f20,plain,(
% 15.58/2.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.58/2.49    inference(ennf_transformation,[],[f1])).
% 15.58/2.49  
% 15.58/2.49  fof(f47,plain,(
% 15.58/2.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f20])).
% 15.58/2.49  
% 15.58/2.49  fof(f2,axiom,(
% 15.58/2.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f48,plain,(
% 15.58/2.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f2])).
% 15.58/2.49  
% 15.58/2.49  fof(f14,axiom,(
% 15.58/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f36,plain,(
% 15.58/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.58/2.49    inference(ennf_transformation,[],[f14])).
% 15.58/2.49  
% 15.58/2.49  fof(f37,plain,(
% 15.58/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.58/2.49    inference(flattening,[],[f36])).
% 15.58/2.49  
% 15.58/2.49  fof(f69,plain,(
% 15.58/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f37])).
% 15.58/2.49  
% 15.58/2.49  fof(f10,axiom,(
% 15.58/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f30,plain,(
% 15.58/2.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.58/2.49    inference(ennf_transformation,[],[f10])).
% 15.58/2.49  
% 15.58/2.49  fof(f31,plain,(
% 15.58/2.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.58/2.49    inference(flattening,[],[f30])).
% 15.58/2.49  
% 15.58/2.49  fof(f42,plain,(
% 15.58/2.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.58/2.49    inference(nnf_transformation,[],[f31])).
% 15.58/2.49  
% 15.58/2.49  fof(f58,plain,(
% 15.58/2.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f42])).
% 15.58/2.49  
% 15.58/2.49  fof(f79,plain,(
% 15.58/2.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f13,axiom,(
% 15.58/2.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f19,plain,(
% 15.58/2.49    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 15.58/2.49    inference(pure_predicate_removal,[],[f13])).
% 15.58/2.49  
% 15.58/2.49  fof(f68,plain,(
% 15.58/2.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f19])).
% 15.58/2.49  
% 15.58/2.49  fof(f72,plain,(
% 15.58/2.49    v1_funct_1(sK2)),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f12,axiom,(
% 15.58/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f34,plain,(
% 15.58/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.58/2.49    inference(ennf_transformation,[],[f12])).
% 15.58/2.49  
% 15.58/2.49  fof(f35,plain,(
% 15.58/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.58/2.49    inference(flattening,[],[f34])).
% 15.58/2.49  
% 15.58/2.49  fof(f67,plain,(
% 15.58/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f35])).
% 15.58/2.49  
% 15.58/2.49  fof(f7,axiom,(
% 15.58/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f26,plain,(
% 15.58/2.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.58/2.49    inference(ennf_transformation,[],[f7])).
% 15.58/2.49  
% 15.58/2.49  fof(f27,plain,(
% 15.58/2.49    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.58/2.49    inference(flattening,[],[f26])).
% 15.58/2.49  
% 15.58/2.49  fof(f55,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f27])).
% 15.58/2.49  
% 15.58/2.49  fof(f86,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.58/2.49    inference(definition_unfolding,[],[f55,f70])).
% 15.58/2.49  
% 15.58/2.49  fof(f16,axiom,(
% 15.58/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f38,plain,(
% 15.58/2.49    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.58/2.49    inference(ennf_transformation,[],[f16])).
% 15.58/2.49  
% 15.58/2.49  fof(f39,plain,(
% 15.58/2.49    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.58/2.49    inference(flattening,[],[f38])).
% 15.58/2.49  
% 15.58/2.49  fof(f71,plain,(
% 15.58/2.49    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f39])).
% 15.58/2.49  
% 15.58/2.49  fof(f73,plain,(
% 15.58/2.49    v1_funct_2(sK2,sK0,sK1)),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f4,axiom,(
% 15.58/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f22,plain,(
% 15.58/2.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.58/2.49    inference(ennf_transformation,[],[f4])).
% 15.58/2.49  
% 15.58/2.49  fof(f23,plain,(
% 15.58/2.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.58/2.49    inference(flattening,[],[f22])).
% 15.58/2.49  
% 15.58/2.49  fof(f50,plain,(
% 15.58/2.49    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f23])).
% 15.58/2.49  
% 15.58/2.49  fof(f3,axiom,(
% 15.58/2.49    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 15.58/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f21,plain,(
% 15.58/2.49    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 15.58/2.49    inference(ennf_transformation,[],[f3])).
% 15.58/2.49  
% 15.58/2.49  fof(f49,plain,(
% 15.58/2.49    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f21])).
% 15.58/2.49  
% 15.58/2.49  fof(f80,plain,(
% 15.58/2.49    v2_funct_1(sK2)),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  fof(f83,plain,(
% 15.58/2.49    k2_funct_1(sK2) != sK3),
% 15.58/2.49    inference(cnf_transformation,[],[f46])).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4,plain,
% 15.58/2.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 15.58/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1208,plain,
% 15.58/2.49      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_33,negated_conjecture,
% 15.58/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.58/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1187,plain,
% 15.58/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_10,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.58/2.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1202,plain,
% 15.58/2.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.58/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2165,plain,
% 15.58/2.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1187,c_1202]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_29,negated_conjecture,
% 15.58/2.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 15.58/2.49      inference(cnf_transformation,[],[f78]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2166,plain,
% 15.58/2.49      ( k2_relat_1(sK2) = sK1 ),
% 15.58/2.49      inference(light_normalisation,[status(thm)],[c_2165,c_29]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_30,negated_conjecture,
% 15.58/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 15.58/2.49      inference(cnf_transformation,[],[f77]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1190,plain,
% 15.58/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_18,plain,
% 15.58/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.58/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.58/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.58/2.49      | k1_xboole_0 = X2 ),
% 15.58/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1196,plain,
% 15.58/2.49      ( k1_relset_1(X0,X1,X2) = X0
% 15.58/2.49      | k1_xboole_0 = X1
% 15.58/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.58/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3523,plain,
% 15.58/2.49      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 15.58/2.49      | sK0 = k1_xboole_0
% 15.58/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1190,c_1196]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_9,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.58/2.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1203,plain,
% 15.58/2.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.58/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2207,plain,
% 15.58/2.49      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1190,c_1203]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3526,plain,
% 15.58/2.49      ( k1_relat_1(sK3) = sK1
% 15.58/2.49      | sK0 = k1_xboole_0
% 15.58/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 15.58/2.49      inference(demodulation,[status(thm)],[c_3523,c_2207]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_31,negated_conjecture,
% 15.58/2.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_40,plain,
% 15.58/2.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_26,negated_conjecture,
% 15.58/2.49      ( k1_xboole_0 != sK0 ),
% 15.58/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_672,plain,( X0 = X0 ),theory(equality) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_701,plain,
% 15.58/2.49      ( k1_xboole_0 = k1_xboole_0 ),
% 15.58/2.49      inference(instantiation,[status(thm)],[c_672]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_673,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1292,plain,
% 15.58/2.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 15.58/2.49      inference(instantiation,[status(thm)],[c_673]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1293,plain,
% 15.58/2.49      ( sK0 != k1_xboole_0
% 15.58/2.49      | k1_xboole_0 = sK0
% 15.58/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.58/2.49      inference(instantiation,[status(thm)],[c_1292]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_5680,plain,
% 15.58/2.49      ( k1_relat_1(sK3) = sK1 ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_3526,c_40,c_26,c_701,c_1293]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_6,plain,
% 15.58/2.49      ( ~ v1_funct_1(X0)
% 15.58/2.49      | ~ v1_funct_1(X1)
% 15.58/2.49      | v2_funct_1(X0)
% 15.58/2.49      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 15.58/2.49      | ~ v1_relat_1(X0)
% 15.58/2.49      | ~ v1_relat_1(X1)
% 15.58/2.49      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 15.58/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1206,plain,
% 15.58/2.49      ( k1_relat_1(X0) != k2_relat_1(X1)
% 15.58/2.49      | v1_funct_1(X0) != iProver_top
% 15.58/2.49      | v1_funct_1(X1) != iProver_top
% 15.58/2.49      | v2_funct_1(X0) = iProver_top
% 15.58/2.49      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 15.58/2.49      | v1_relat_1(X0) != iProver_top
% 15.58/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_5683,plain,
% 15.58/2.49      ( k2_relat_1(X0) != sK1
% 15.58/2.49      | v1_funct_1(X0) != iProver_top
% 15.58/2.49      | v1_funct_1(sK3) != iProver_top
% 15.58/2.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) = iProver_top
% 15.58/2.49      | v1_relat_1(X0) != iProver_top
% 15.58/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_5680,c_1206]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_32,negated_conjecture,
% 15.58/2.49      ( v1_funct_1(sK3) ),
% 15.58/2.49      inference(cnf_transformation,[],[f75]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_39,plain,
% 15.58/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_0,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | ~ v1_relat_1(X1)
% 15.58/2.49      | v1_relat_1(X0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1212,plain,
% 15.58/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.58/2.49      | v1_relat_1(X1) != iProver_top
% 15.58/2.49      | v1_relat_1(X0) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2212,plain,
% 15.58/2.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 15.58/2.49      | v1_relat_1(sK3) = iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1190,c_1212]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1,plain,
% 15.58/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.58/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2331,plain,
% 15.58/2.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 15.58/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2332,plain,
% 15.58/2.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_2331]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_38410,plain,
% 15.58/2.49      ( v1_relat_1(X0) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) = iProver_top
% 15.58/2.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 15.58/2.49      | k2_relat_1(X0) != sK1
% 15.58/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_5683,c_39,c_2212,c_2332]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_38411,plain,
% 15.58/2.49      ( k2_relat_1(X0) != sK1
% 15.58/2.49      | v1_funct_1(X0) != iProver_top
% 15.58/2.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) = iProver_top
% 15.58/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.58/2.49      inference(renaming,[status(thm)],[c_38410]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_38416,plain,
% 15.58/2.49      ( v1_funct_1(sK2) != iProver_top
% 15.58/2.49      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) = iProver_top
% 15.58/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_2166,c_38411]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_22,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.58/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.58/2.49      | ~ v1_funct_1(X0)
% 15.58/2.49      | ~ v1_funct_1(X3)
% 15.58/2.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1192,plain,
% 15.58/2.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.58/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.58/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.58/2.49      | v1_funct_1(X4) != iProver_top
% 15.58/2.49      | v1_funct_1(X5) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2652,plain,
% 15.58/2.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.58/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.58/2.49      | v1_funct_1(X2) != iProver_top
% 15.58/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1190,c_1192]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3209,plain,
% 15.58/2.49      ( v1_funct_1(X2) != iProver_top
% 15.58/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.58/2.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_2652,c_39]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3210,plain,
% 15.58/2.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.58/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.58/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.58/2.49      inference(renaming,[status(thm)],[c_3209]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3217,plain,
% 15.58/2.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 15.58/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1187,c_3210]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_12,plain,
% 15.58/2.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.58/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.58/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.58/2.49      | X3 = X2 ),
% 15.58/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_28,negated_conjecture,
% 15.58/2.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 15.58/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_394,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.58/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.58/2.49      | X3 = X0
% 15.58/2.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 15.58/2.49      | k6_partfun1(sK0) != X3
% 15.58/2.49      | sK0 != X2
% 15.58/2.49      | sK0 != X1 ),
% 15.58/2.49      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_395,plain,
% 15.58/2.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.58/2.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.58/2.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.58/2.49      inference(unflattening,[status(thm)],[c_394]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_21,plain,
% 15.58/2.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.58/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_403,plain,
% 15.58/2.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.58/2.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.58/2.49      inference(forward_subsumption_resolution,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_395,c_21]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1183,plain,
% 15.58/2.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.58/2.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_35,negated_conjecture,
% 15.58/2.49      ( v1_funct_1(sK2) ),
% 15.58/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_19,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.58/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.58/2.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.58/2.49      | ~ v1_funct_1(X0)
% 15.58/2.49      | ~ v1_funct_1(X3) ),
% 15.58/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1294,plain,
% 15.58/2.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.58/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.58/2.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.58/2.49      | ~ v1_funct_1(sK3)
% 15.58/2.49      | ~ v1_funct_1(sK2) ),
% 15.58/2.49      inference(instantiation,[status(thm)],[c_19]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1943,plain,
% 15.58/2.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_1183,c_35,c_33,c_32,c_30,c_403,c_1294]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3218,plain,
% 15.58/2.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 15.58/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.58/2.49      inference(light_normalisation,[status(thm)],[c_3217,c_1943]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_36,plain,
% 15.58/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3774,plain,
% 15.58/2.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_3218,c_36]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_38418,plain,
% 15.58/2.49      ( v1_funct_1(sK2) != iProver_top
% 15.58/2.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) = iProver_top
% 15.58/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.58/2.49      inference(light_normalisation,[status(thm)],[c_38416,c_3774]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1211,plain,
% 15.58/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2213,plain,
% 15.58/2.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.58/2.49      | v1_relat_1(sK2) = iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1187,c_1212]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2468,plain,
% 15.58/2.49      ( v1_relat_1(sK2) = iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1211,c_2213]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_38461,plain,
% 15.58/2.49      ( v2_funct_1(sK3) = iProver_top
% 15.58/2.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_38418,c_36,c_2468]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_38462,plain,
% 15.58/2.49      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) = iProver_top ),
% 15.58/2.49      inference(renaming,[status(thm)],[c_38461]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_38465,plain,
% 15.58/2.49      ( v2_funct_1(sK3) = iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1208,c_38462]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_8,plain,
% 15.58/2.49      ( ~ v1_funct_1(X0)
% 15.58/2.49      | ~ v1_funct_1(X1)
% 15.58/2.49      | ~ v2_funct_1(X0)
% 15.58/2.49      | ~ v1_relat_1(X0)
% 15.58/2.49      | ~ v1_relat_1(X1)
% 15.58/2.49      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 15.58/2.49      | k1_relat_1(X0) != k2_relat_1(X1)
% 15.58/2.49      | k2_funct_1(X0) = X1 ),
% 15.58/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1204,plain,
% 15.58/2.49      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 15.58/2.49      | k1_relat_1(X1) != k2_relat_1(X0)
% 15.58/2.49      | k2_funct_1(X1) = X0
% 15.58/2.49      | v1_funct_1(X1) != iProver_top
% 15.58/2.49      | v1_funct_1(X0) != iProver_top
% 15.58/2.49      | v2_funct_1(X1) != iProver_top
% 15.58/2.49      | v1_relat_1(X1) != iProver_top
% 15.58/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4351,plain,
% 15.58/2.49      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 15.58/2.49      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 15.58/2.49      | k2_funct_1(sK3) = sK2
% 15.58/2.49      | v1_funct_1(sK3) != iProver_top
% 15.58/2.49      | v1_funct_1(sK2) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) != iProver_top
% 15.58/2.49      | v1_relat_1(sK3) != iProver_top
% 15.58/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_3774,c_1204]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2164,plain,
% 15.58/2.49      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1190,c_1202]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_23,plain,
% 15.58/2.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 15.58/2.49      | ~ v1_funct_2(X3,X1,X0)
% 15.58/2.49      | ~ v1_funct_2(X2,X0,X1)
% 15.58/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 15.58/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.58/2.49      | ~ v1_funct_1(X2)
% 15.58/2.49      | ~ v1_funct_1(X3)
% 15.58/2.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 15.58/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_407,plain,
% 15.58/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.58/2.49      | ~ v1_funct_2(X3,X2,X1)
% 15.58/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.58/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.58/2.49      | ~ v1_funct_1(X0)
% 15.58/2.49      | ~ v1_funct_1(X3)
% 15.58/2.49      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.58/2.49      | k2_relset_1(X1,X2,X0) = X2
% 15.58/2.49      | k6_partfun1(X2) != k6_partfun1(sK0)
% 15.58/2.49      | sK0 != X2 ),
% 15.58/2.49      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_408,plain,
% 15.58/2.49      ( ~ v1_funct_2(X0,X1,sK0)
% 15.58/2.49      | ~ v1_funct_2(X2,sK0,X1)
% 15.58/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 15.58/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 15.58/2.49      | ~ v1_funct_1(X0)
% 15.58/2.49      | ~ v1_funct_1(X2)
% 15.58/2.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.58/2.49      | k2_relset_1(X1,sK0,X0) = sK0
% 15.58/2.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 15.58/2.49      inference(unflattening,[status(thm)],[c_407]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_493,plain,
% 15.58/2.49      ( ~ v1_funct_2(X0,X1,sK0)
% 15.58/2.49      | ~ v1_funct_2(X2,sK0,X1)
% 15.58/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 15.58/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 15.58/2.49      | ~ v1_funct_1(X0)
% 15.58/2.49      | ~ v1_funct_1(X2)
% 15.58/2.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.58/2.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 15.58/2.49      inference(equality_resolution_simp,[status(thm)],[c_408]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1182,plain,
% 15.58/2.49      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.58/2.49      | k2_relset_1(X0,sK0,X2) = sK0
% 15.58/2.49      | v1_funct_2(X2,X0,sK0) != iProver_top
% 15.58/2.49      | v1_funct_2(X1,sK0,X0) != iProver_top
% 15.58/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 15.58/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 15.58/2.49      | v1_funct_1(X1) != iProver_top
% 15.58/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1682,plain,
% 15.58/2.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 15.58/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.58/2.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.58/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.58/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.58/2.49      | v1_funct_1(sK3) != iProver_top
% 15.58/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.58/2.49      inference(equality_resolution,[status(thm)],[c_1182]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_34,negated_conjecture,
% 15.58/2.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 15.58/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_37,plain,
% 15.58/2.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_38,plain,
% 15.58/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_41,plain,
% 15.58/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2009,plain,
% 15.58/2.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_1682,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2167,plain,
% 15.58/2.49      ( k2_relat_1(sK3) = sK0 ),
% 15.58/2.49      inference(light_normalisation,[status(thm)],[c_2164,c_2009]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4352,plain,
% 15.58/2.49      ( k1_relat_1(sK3) != sK1
% 15.58/2.49      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 15.58/2.49      | k2_funct_1(sK3) = sK2
% 15.58/2.49      | v1_funct_1(sK3) != iProver_top
% 15.58/2.49      | v1_funct_1(sK2) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) != iProver_top
% 15.58/2.49      | v1_relat_1(sK3) != iProver_top
% 15.58/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.58/2.49      inference(light_normalisation,[status(thm)],[c_4351,c_2166,c_2167]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4353,plain,
% 15.58/2.49      ( k1_relat_1(sK3) != sK1
% 15.58/2.49      | k2_funct_1(sK3) = sK2
% 15.58/2.49      | v1_funct_1(sK3) != iProver_top
% 15.58/2.49      | v1_funct_1(sK2) != iProver_top
% 15.58/2.49      | v2_funct_1(sK3) != iProver_top
% 15.58/2.49      | v1_relat_1(sK3) != iProver_top
% 15.58/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.58/2.49      inference(equality_resolution_simp,[status(thm)],[c_4352]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4934,plain,
% 15.58/2.49      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_4353,c_36,c_39,c_40,c_26,c_701,c_1293,c_2212,c_2332,
% 15.58/2.49                 c_2468,c_3526]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_39383,plain,
% 15.58/2.49      ( k2_funct_1(sK3) = sK2 ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_38465,c_4934]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1188,plain,
% 15.58/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3,plain,
% 15.58/2.49      ( ~ v1_funct_1(X0)
% 15.58/2.49      | ~ v2_funct_1(X0)
% 15.58/2.49      | ~ v1_relat_1(X0)
% 15.58/2.49      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1209,plain,
% 15.58/2.49      ( k2_funct_1(X0) = k4_relat_1(X0)
% 15.58/2.49      | v1_funct_1(X0) != iProver_top
% 15.58/2.49      | v2_funct_1(X0) != iProver_top
% 15.58/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2706,plain,
% 15.58/2.49      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 15.58/2.49      | v2_funct_1(sK3) != iProver_top
% 15.58/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1188,c_1209]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2893,plain,
% 15.58/2.49      ( v2_funct_1(sK3) != iProver_top
% 15.58/2.49      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_2706,c_2212,c_2332]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2894,plain,
% 15.58/2.49      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 15.58/2.49      | v2_funct_1(sK3) != iProver_top ),
% 15.58/2.49      inference(renaming,[status(thm)],[c_2893]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_39384,plain,
% 15.58/2.49      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_38465,c_2894]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_39385,plain,
% 15.58/2.49      ( k4_relat_1(sK3) = sK2 ),
% 15.58/2.49      inference(demodulation,[status(thm)],[c_39383,c_39384]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2462,plain,
% 15.58/2.49      ( v1_relat_1(sK3) = iProver_top ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_2212,c_2332]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2,plain,
% 15.58/2.49      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 15.58/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1210,plain,
% 15.58/2.49      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2466,plain,
% 15.58/2.49      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_2462,c_1210]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_43653,plain,
% 15.58/2.49      ( k4_relat_1(sK2) = sK3 ),
% 15.58/2.49      inference(demodulation,[status(thm)],[c_39385,c_2466]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1185,plain,
% 15.58/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2707,plain,
% 15.58/2.49      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 15.58/2.49      | v2_funct_1(sK2) != iProver_top
% 15.58/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1185,c_1209]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_27,negated_conjecture,
% 15.58/2.49      ( v2_funct_1(sK2) ),
% 15.58/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_43,plain,
% 15.58/2.49      ( v2_funct_1(sK2) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3050,plain,
% 15.58/2.49      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_2707,c_43,c_2468]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_24,negated_conjecture,
% 15.58/2.49      ( k2_funct_1(sK2) != sK3 ),
% 15.58/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3052,plain,
% 15.58/2.49      ( k4_relat_1(sK2) != sK3 ),
% 15.58/2.49      inference(demodulation,[status(thm)],[c_3050,c_24]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(contradiction,plain,
% 15.58/2.49      ( $false ),
% 15.58/2.49      inference(minisat,[status(thm)],[c_43653,c_3052]) ).
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.58/2.49  
% 15.58/2.49  ------                               Statistics
% 15.58/2.49  
% 15.58/2.49  ------ General
% 15.58/2.49  
% 15.58/2.49  abstr_ref_over_cycles:                  0
% 15.58/2.49  abstr_ref_under_cycles:                 0
% 15.58/2.49  gc_basic_clause_elim:                   0
% 15.58/2.49  forced_gc_time:                         0
% 15.58/2.49  parsing_time:                           0.008
% 15.58/2.49  unif_index_cands_time:                  0.
% 15.58/2.49  unif_index_add_time:                    0.
% 15.58/2.49  orderings_time:                         0.
% 15.58/2.49  out_proof_time:                         0.021
% 15.58/2.49  total_time:                             1.672
% 15.58/2.49  num_of_symbols:                         53
% 15.58/2.49  num_of_terms:                           58036
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing
% 15.58/2.49  
% 15.58/2.49  num_of_splits:                          0
% 15.58/2.49  num_of_split_atoms:                     0
% 15.58/2.49  num_of_reused_defs:                     0
% 15.58/2.49  num_eq_ax_congr_red:                    18
% 15.58/2.49  num_of_sem_filtered_clauses:            1
% 15.58/2.49  num_of_subtypes:                        0
% 15.58/2.49  monotx_restored_types:                  0
% 15.58/2.49  sat_num_of_epr_types:                   0
% 15.58/2.49  sat_num_of_non_cyclic_types:            0
% 15.58/2.49  sat_guarded_non_collapsed_types:        0
% 15.58/2.49  num_pure_diseq_elim:                    0
% 15.58/2.49  simp_replaced_by:                       0
% 15.58/2.49  res_preprocessed:                       172
% 15.58/2.49  prep_upred:                             0
% 15.58/2.49  prep_unflattend:                        12
% 15.58/2.49  smt_new_axioms:                         0
% 15.58/2.49  pred_elim_cands:                        5
% 15.58/2.49  pred_elim:                              1
% 15.58/2.49  pred_elim_cl:                           1
% 15.58/2.49  pred_elim_cycles:                       3
% 15.58/2.49  merged_defs:                            0
% 15.58/2.49  merged_defs_ncl:                        0
% 15.58/2.49  bin_hyper_res:                          0
% 15.58/2.49  prep_cycles:                            4
% 15.58/2.49  pred_elim_time:                         0.004
% 15.58/2.49  splitting_time:                         0.
% 15.58/2.49  sem_filter_time:                        0.
% 15.58/2.49  monotx_time:                            0.001
% 15.58/2.49  subtype_inf_time:                       0.
% 15.58/2.49  
% 15.58/2.49  ------ Problem properties
% 15.58/2.49  
% 15.58/2.49  clauses:                                35
% 15.58/2.49  conjectures:                            11
% 15.58/2.49  epr:                                    7
% 15.58/2.49  horn:                                   31
% 15.58/2.49  ground:                                 12
% 15.58/2.49  unary:                                  15
% 15.58/2.49  binary:                                 4
% 15.58/2.49  lits:                                   104
% 15.58/2.49  lits_eq:                                28
% 15.58/2.49  fd_pure:                                0
% 15.58/2.49  fd_pseudo:                              0
% 15.58/2.49  fd_cond:                                3
% 15.58/2.49  fd_pseudo_cond:                         1
% 15.58/2.49  ac_symbols:                             0
% 15.58/2.49  
% 15.58/2.49  ------ Propositional Solver
% 15.58/2.49  
% 15.58/2.49  prop_solver_calls:                      34
% 15.58/2.49  prop_fast_solver_calls:                 3781
% 15.58/2.49  smt_solver_calls:                       0
% 15.58/2.49  smt_fast_solver_calls:                  0
% 15.58/2.49  prop_num_of_clauses:                    21823
% 15.58/2.49  prop_preprocess_simplified:             37440
% 15.58/2.49  prop_fo_subsumed:                       1098
% 15.58/2.49  prop_solver_time:                       0.
% 15.58/2.49  smt_solver_time:                        0.
% 15.58/2.49  smt_fast_solver_time:                   0.
% 15.58/2.49  prop_fast_solver_time:                  0.
% 15.58/2.49  prop_unsat_core_time:                   0.003
% 15.58/2.49  
% 15.58/2.49  ------ QBF
% 15.58/2.49  
% 15.58/2.49  qbf_q_res:                              0
% 15.58/2.49  qbf_num_tautologies:                    0
% 15.58/2.49  qbf_prep_cycles:                        0
% 15.58/2.49  
% 15.58/2.49  ------ BMC1
% 15.58/2.49  
% 15.58/2.49  bmc1_current_bound:                     -1
% 15.58/2.49  bmc1_last_solved_bound:                 -1
% 15.58/2.49  bmc1_unsat_core_size:                   -1
% 15.58/2.49  bmc1_unsat_core_parents_size:           -1
% 15.58/2.49  bmc1_merge_next_fun:                    0
% 15.58/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.58/2.49  
% 15.58/2.49  ------ Instantiation
% 15.58/2.49  
% 15.58/2.49  inst_num_of_clauses:                    5550
% 15.58/2.49  inst_num_in_passive:                    1671
% 15.58/2.49  inst_num_in_active:                     2803
% 15.58/2.49  inst_num_in_unprocessed:                1076
% 15.58/2.49  inst_num_of_loops:                      2930
% 15.58/2.49  inst_num_of_learning_restarts:          0
% 15.58/2.49  inst_num_moves_active_passive:          123
% 15.58/2.49  inst_lit_activity:                      0
% 15.58/2.49  inst_lit_activity_moves:                1
% 15.58/2.49  inst_num_tautologies:                   0
% 15.58/2.49  inst_num_prop_implied:                  0
% 15.58/2.49  inst_num_existing_simplified:           0
% 15.58/2.49  inst_num_eq_res_simplified:             0
% 15.58/2.49  inst_num_child_elim:                    0
% 15.58/2.49  inst_num_of_dismatching_blockings:      2106
% 15.58/2.49  inst_num_of_non_proper_insts:           5689
% 15.58/2.49  inst_num_of_duplicates:                 0
% 15.58/2.49  inst_inst_num_from_inst_to_res:         0
% 15.58/2.49  inst_dismatching_checking_time:         0.
% 15.58/2.49  
% 15.58/2.49  ------ Resolution
% 15.58/2.49  
% 15.58/2.49  res_num_of_clauses:                     0
% 15.58/2.49  res_num_in_passive:                     0
% 15.58/2.49  res_num_in_active:                      0
% 15.58/2.49  res_num_of_loops:                       176
% 15.58/2.49  res_forward_subset_subsumed:            413
% 15.58/2.49  res_backward_subset_subsumed:           0
% 15.58/2.49  res_forward_subsumed:                   0
% 15.58/2.49  res_backward_subsumed:                  0
% 15.58/2.49  res_forward_subsumption_resolution:     2
% 15.58/2.49  res_backward_subsumption_resolution:    0
% 15.58/2.49  res_clause_to_clause_subsumption:       5283
% 15.58/2.49  res_orphan_elimination:                 0
% 15.58/2.49  res_tautology_del:                      208
% 15.58/2.49  res_num_eq_res_simplified:              1
% 15.58/2.49  res_num_sel_changes:                    0
% 15.58/2.49  res_moves_from_active_to_pass:          0
% 15.58/2.49  
% 15.58/2.49  ------ Superposition
% 15.58/2.49  
% 15.58/2.49  sup_time_total:                         0.
% 15.58/2.49  sup_time_generating:                    0.
% 15.58/2.49  sup_time_sim_full:                      0.
% 15.58/2.49  sup_time_sim_immed:                     0.
% 15.58/2.49  
% 15.58/2.49  sup_num_of_clauses:                     2046
% 15.58/2.49  sup_num_in_active:                      559
% 15.58/2.49  sup_num_in_passive:                     1487
% 15.58/2.49  sup_num_of_loops:                       584
% 15.58/2.49  sup_fw_superposition:                   1156
% 15.58/2.49  sup_bw_superposition:                   1157
% 15.58/2.49  sup_immediate_simplified:               1109
% 15.58/2.49  sup_given_eliminated:                   0
% 15.58/2.49  comparisons_done:                       0
% 15.58/2.49  comparisons_avoided:                    1
% 15.58/2.49  
% 15.58/2.49  ------ Simplifications
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  sim_fw_subset_subsumed:                 49
% 15.58/2.49  sim_bw_subset_subsumed:                 133
% 15.58/2.49  sim_fw_subsumed:                        10
% 15.58/2.49  sim_bw_subsumed:                        4
% 15.58/2.49  sim_fw_subsumption_res:                 0
% 15.58/2.49  sim_bw_subsumption_res:                 0
% 15.58/2.49  sim_tautology_del:                      0
% 15.58/2.49  sim_eq_tautology_del:                   72
% 15.58/2.49  sim_eq_res_simp:                        1
% 15.58/2.49  sim_fw_demodulated:                     47
% 15.58/2.49  sim_bw_demodulated:                     7
% 15.58/2.49  sim_light_normalised:                   1081
% 15.58/2.49  sim_joinable_taut:                      0
% 15.58/2.49  sim_joinable_simp:                      0
% 15.58/2.49  sim_ac_normalised:                      0
% 15.58/2.49  sim_smt_subsumption:                    0
% 15.58/2.49  
%------------------------------------------------------------------------------
