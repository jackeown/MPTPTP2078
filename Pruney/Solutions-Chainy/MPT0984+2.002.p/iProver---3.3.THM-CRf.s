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
% DateTime   : Thu Dec  3 12:02:19 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  148 (2065 expanded)
%              Number of clauses        :  105 ( 727 expanded)
%              Number of leaves         :   12 ( 503 expanded)
%              Depth                    :   20
%              Number of atoms          :  551 (17130 expanded)
%              Number of equality atoms :  268 (5179 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
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
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( ( ~ v2_funct_1(sK4)
          | ~ v2_funct_1(X3) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X2 )
        & k2_relset_1(X0,X1,X3) = X1
        & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK4))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ v2_funct_1(X4)
              | ~ v2_funct_1(X3) )
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & k2_relset_1(X0,X1,X3) = X1
            & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(sK3) )
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & k2_relset_1(sK0,sK1,sK3) = sK1
          & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ~ v2_funct_1(sK4)
      | ~ v2_funct_1(sK3) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & k2_relset_1(sK0,sK1,sK3) = sK1
    & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f22,f21])).

fof(f40,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
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

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f30])).

fof(f44,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f33])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_295,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_297,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_295,c_16])).

cnf(c_450,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_297])).

cnf(c_458,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_781,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_776,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_1162,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_781,c_776])).

cnf(c_1246,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_450,c_1162])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_468,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | v2_funct_1(X1_47)
    | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
    | k1_relat_1(X1_47) != k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_773,plain,
    ( k1_relat_1(X0_47) != k2_relat_1(X1_47)
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v2_funct_1(X0_47) = iProver_top
    | v2_funct_1(k5_relat_1(X1_47,X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_1660,plain,
    ( k2_relat_1(X0_47) != sK1
    | sK2 = k1_xboole_0
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_773])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_22,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_28,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_933,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_934,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_936,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_937,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_467,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | v2_funct_1(X0_47)
    | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
    | k1_relat_1(X1_47) != k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1007,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,X0_47))
    | v2_funct_1(sK3)
    | k1_relat_1(X0_47) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_1153,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_1154,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_456,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_783,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_777,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_1172,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_783,c_777])).

cnf(c_14,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_460,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1174,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1172,c_460])).

cnf(c_1006,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK3)
    | v2_funct_1(X0_47)
    | ~ v2_funct_1(k5_relat_1(sK3,X0_47))
    | k1_relat_1(X0_47) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_1188,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_1189,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1188])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47)
    | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_47,X4_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1_47,X2_47,X3_47,X4_47,X0_47,sK4) = k5_relat_1(X0_47,sK4) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_1056,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0_47,X1_47,X2_47,X3_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,X0_47,X1_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1210,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_473,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1017,plain,
    ( X0_47 != X1_47
    | X0_47 = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != X1_47 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1211,plain,
    ( X0_47 = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
    | X0_47 != k5_relat_1(sK3,sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_1347,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4)
    | k5_relat_1(sK3,sK4) = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
    | k5_relat_1(sK3,sK4) != k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_470,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1348,plain,
    ( k5_relat_1(sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_474,plain,
    ( ~ v2_funct_1(X0_47)
    | v2_funct_1(X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_939,plain,
    ( v2_funct_1(X0_47)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | X0_47 != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_1432,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v2_funct_1(k5_relat_1(sK3,sK4))
    | k5_relat_1(sK3,sK4) != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_1433,plain,
    ( k5_relat_1(sK3,sK4) != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1432])).

cnf(c_1633,plain,
    ( k1_relat_1(sK4) != X0_47
    | k1_relat_1(sK4) = k2_relat_1(sK3)
    | k2_relat_1(sK3) != X0_47 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1928,plain,
    ( k1_relat_1(sK4) = k2_relat_1(sK3)
    | k1_relat_1(sK4) != sK1
    | k2_relat_1(sK3) != sK1 ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_1951,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1660,c_21,c_22,c_19,c_24,c_18,c_25,c_16,c_27,c_28,c_29,c_934,c_937,c_1154,c_1174,c_1189,c_1210,c_1246,c_1347,c_1348,c_1433,c_1928])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_269,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_452,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_787,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_1960,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1951,c_787])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_461,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1965,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1951,c_461])).

cnf(c_1966,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1965])).

cnf(c_1978,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1960,c_1966])).

cnf(c_1979,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1978])).

cnf(c_1962,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_1951,c_1162])).

cnf(c_1972,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_1962,c_1966])).

cnf(c_1980,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1979,c_1972])).

cnf(c_1964,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1951,c_781])).

cnf(c_1969,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1964,c_1966])).

cnf(c_1983,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1980,c_1969])).

cnf(c_1706,plain,
    ( X0_47 != X1_47
    | X0_47 = sK1
    | sK1 != X1_47 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1927,plain,
    ( k1_relat_1(sK4) != X0_47
    | k1_relat_1(sK4) = sK1
    | sK1 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_1929,plain,
    ( k1_relat_1(sK4) = sK1
    | k1_relat_1(sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_233,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_454,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(subtyping,[status(esa)],[c_233])).

cnf(c_785,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_491,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_1549,plain,
    ( X0_47 != X1_47
    | X0_47 = sK2
    | sK2 != X1_47 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1550,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_1782,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_785,c_491,c_461,c_1550])).

cnf(c_1129,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_959,plain,
    ( sK1 != X0_47
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0_47 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1128,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1983,c_1928,c_1929,c_1782,c_1433,c_1348,c_1347,c_1246,c_1210,c_1189,c_1174,c_1154,c_1129,c_1128,c_937,c_934,c_29,c_28,c_27,c_16,c_25,c_18,c_24,c_19,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:16:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.99/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.99  
% 1.99/0.99  ------  iProver source info
% 1.99/0.99  
% 1.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.99  git: non_committed_changes: false
% 1.99/0.99  git: last_make_outside_of_git: false
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     num_symb
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.99  --inst_passive_queues_freq              [25;2]
% 1.99/0.99  --inst_dismatching                      true
% 1.99/0.99  --inst_eager_unprocessed_to_passive     true
% 1.99/0.99  --inst_prop_sim_given                   true
% 1.99/0.99  --inst_prop_sim_new                     false
% 1.99/0.99  --inst_subs_new                         false
% 1.99/0.99  --inst_eq_res_simp                      false
% 1.99/0.99  --inst_subs_given                       false
% 1.99/0.99  --inst_orphan_elimination               true
% 1.99/0.99  --inst_learning_loop_flag               true
% 1.99/0.99  --inst_learning_start                   3000
% 1.99/0.99  --inst_learning_factor                  2
% 1.99/0.99  --inst_start_prop_sim_after_learn       3
% 1.99/0.99  --inst_sel_renew                        solver
% 1.99/0.99  --inst_lit_activity_flag                true
% 1.99/0.99  --inst_restr_to_given                   false
% 1.99/0.99  --inst_activity_threshold               500
% 1.99/0.99  --inst_out_proof                        true
% 1.99/0.99  
% 1.99/0.99  ------ Resolution Options
% 1.99/0.99  
% 1.99/0.99  --resolution_flag                       true
% 1.99/0.99  --res_lit_sel                           adaptive
% 1.99/0.99  --res_lit_sel_side                      none
% 1.99/0.99  --res_ordering                          kbo
% 1.99/0.99  --res_to_prop_solver                    active
% 1.99/0.99  --res_prop_simpl_new                    false
% 1.99/0.99  --res_prop_simpl_given                  true
% 1.99/0.99  --res_passive_queue_type                priority_queues
% 1.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.99  --res_passive_queues_freq               [15;5]
% 1.99/0.99  --res_forward_subs                      full
% 1.99/0.99  --res_backward_subs                     full
% 1.99/0.99  --res_forward_subs_resolution           true
% 1.99/0.99  --res_backward_subs_resolution          true
% 1.99/0.99  --res_orphan_elimination                true
% 1.99/0.99  --res_time_limit                        2.
% 1.99/0.99  --res_out_proof                         true
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Options
% 1.99/0.99  
% 1.99/0.99  --superposition_flag                    true
% 1.99/0.99  --sup_passive_queue_type                priority_queues
% 1.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.99  --demod_completeness_check              fast
% 1.99/0.99  --demod_use_ground                      true
% 1.99/0.99  --sup_to_prop_solver                    passive
% 1.99/0.99  --sup_prop_simpl_new                    true
% 1.99/0.99  --sup_prop_simpl_given                  true
% 1.99/0.99  --sup_fun_splitting                     false
% 1.99/0.99  --sup_smt_interval                      50000
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Simplification Setup
% 1.99/0.99  
% 1.99/0.99  --sup_indices_passive                   []
% 1.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_full_bw                           [BwDemod]
% 1.99/0.99  --sup_immed_triv                        [TrivRules]
% 1.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_immed_bw_main                     []
% 1.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  
% 1.99/0.99  ------ Combination Options
% 1.99/0.99  
% 1.99/0.99  --comb_res_mult                         3
% 1.99/0.99  --comb_sup_mult                         2
% 1.99/0.99  --comb_inst_mult                        10
% 1.99/0.99  
% 1.99/0.99  ------ Debug Options
% 1.99/0.99  
% 1.99/0.99  --dbg_backtrace                         false
% 1.99/0.99  --dbg_dump_prop_clauses                 false
% 1.99/0.99  --dbg_dump_prop_clauses_file            -
% 1.99/0.99  --dbg_out_stat                          false
% 1.99/0.99  ------ Parsing...
% 1.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.99  ------ Proving...
% 1.99/0.99  ------ Problem Properties 
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  clauses                                 20
% 1.99/0.99  conjectures                             8
% 1.99/0.99  EPR                                     4
% 1.99/0.99  Horn                                    16
% 1.99/0.99  unary                                   6
% 1.99/0.99  binary                                  7
% 1.99/0.99  lits                                    53
% 1.99/0.99  lits eq                                 22
% 1.99/0.99  fd_pure                                 0
% 1.99/0.99  fd_pseudo                               0
% 1.99/0.99  fd_cond                                 0
% 1.99/0.99  fd_pseudo_cond                          0
% 1.99/0.99  AC symbols                              0
% 1.99/0.99  
% 1.99/0.99  ------ Schedule dynamic 5 is on 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  Current options:
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     none
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.99  --inst_passive_queues_freq              [25;2]
% 1.99/0.99  --inst_dismatching                      true
% 1.99/0.99  --inst_eager_unprocessed_to_passive     true
% 1.99/0.99  --inst_prop_sim_given                   true
% 1.99/0.99  --inst_prop_sim_new                     false
% 1.99/0.99  --inst_subs_new                         false
% 1.99/0.99  --inst_eq_res_simp                      false
% 1.99/0.99  --inst_subs_given                       false
% 1.99/0.99  --inst_orphan_elimination               true
% 1.99/0.99  --inst_learning_loop_flag               true
% 1.99/0.99  --inst_learning_start                   3000
% 1.99/0.99  --inst_learning_factor                  2
% 1.99/0.99  --inst_start_prop_sim_after_learn       3
% 1.99/0.99  --inst_sel_renew                        solver
% 1.99/0.99  --inst_lit_activity_flag                true
% 1.99/0.99  --inst_restr_to_given                   false
% 1.99/0.99  --inst_activity_threshold               500
% 1.99/0.99  --inst_out_proof                        true
% 1.99/0.99  
% 1.99/0.99  ------ Resolution Options
% 1.99/0.99  
% 1.99/0.99  --resolution_flag                       false
% 1.99/0.99  --res_lit_sel                           adaptive
% 1.99/0.99  --res_lit_sel_side                      none
% 1.99/0.99  --res_ordering                          kbo
% 1.99/0.99  --res_to_prop_solver                    active
% 1.99/0.99  --res_prop_simpl_new                    false
% 1.99/0.99  --res_prop_simpl_given                  true
% 1.99/0.99  --res_passive_queue_type                priority_queues
% 1.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.99  --res_passive_queues_freq               [15;5]
% 1.99/0.99  --res_forward_subs                      full
% 1.99/0.99  --res_backward_subs                     full
% 1.99/0.99  --res_forward_subs_resolution           true
% 1.99/0.99  --res_backward_subs_resolution          true
% 1.99/0.99  --res_orphan_elimination                true
% 1.99/0.99  --res_time_limit                        2.
% 1.99/0.99  --res_out_proof                         true
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Options
% 1.99/0.99  
% 1.99/0.99  --superposition_flag                    true
% 1.99/0.99  --sup_passive_queue_type                priority_queues
% 1.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.99  --demod_completeness_check              fast
% 1.99/0.99  --demod_use_ground                      true
% 1.99/0.99  --sup_to_prop_solver                    passive
% 1.99/0.99  --sup_prop_simpl_new                    true
% 1.99/0.99  --sup_prop_simpl_given                  true
% 1.99/0.99  --sup_fun_splitting                     false
% 1.99/0.99  --sup_smt_interval                      50000
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Simplification Setup
% 1.99/0.99  
% 1.99/0.99  --sup_indices_passive                   []
% 1.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_full_bw                           [BwDemod]
% 1.99/0.99  --sup_immed_triv                        [TrivRules]
% 1.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_immed_bw_main                     []
% 1.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  
% 1.99/0.99  ------ Combination Options
% 1.99/0.99  
% 1.99/0.99  --comb_res_mult                         3
% 1.99/0.99  --comb_sup_mult                         2
% 1.99/0.99  --comb_inst_mult                        10
% 1.99/0.99  
% 1.99/0.99  ------ Debug Options
% 1.99/0.99  
% 1.99/0.99  --dbg_backtrace                         false
% 1.99/0.99  --dbg_dump_prop_clauses                 false
% 1.99/0.99  --dbg_dump_prop_clauses_file            -
% 1.99/0.99  --dbg_out_stat                          false
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  ------ Proving...
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  % SZS status Theorem for theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  fof(f5,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f14,plain,(
% 1.99/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.99    inference(ennf_transformation,[],[f5])).
% 1.99/0.99  
% 1.99/0.99  fof(f15,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.99    inference(flattening,[],[f14])).
% 1.99/0.99  
% 1.99/0.99  fof(f20,plain,(
% 1.99/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.99    inference(nnf_transformation,[],[f15])).
% 1.99/0.99  
% 1.99/0.99  fof(f29,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f20])).
% 1.99/0.99  
% 1.99/0.99  fof(f7,conjecture,(
% 1.99/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f8,negated_conjecture,(
% 1.99/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.99/0.99    inference(negated_conjecture,[],[f7])).
% 1.99/0.99  
% 1.99/0.99  fof(f18,plain,(
% 1.99/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & (k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.99/0.99    inference(ennf_transformation,[],[f8])).
% 1.99/0.99  
% 1.99/0.99  fof(f19,plain,(
% 1.99/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.99/0.99    inference(flattening,[],[f18])).
% 1.99/0.99  
% 1.99/0.99  fof(f22,plain,(
% 1.99/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((~v2_funct_1(sK4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f21,plain,(
% 1.99/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(sK3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & k2_relset_1(sK0,sK1,sK3) = sK1 & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f23,plain,(
% 1.99/0.99    ((~v2_funct_1(sK4) | ~v2_funct_1(sK3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & k2_relset_1(sK0,sK1,sK3) = sK1 & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f22,f21])).
% 1.99/0.99  
% 1.99/0.99  fof(f40,plain,(
% 1.99/0.99    v1_funct_2(sK4,sK1,sK2)),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f41,plain,(
% 1.99/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f3,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f12,plain,(
% 1.99/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.99    inference(ennf_transformation,[],[f3])).
% 1.99/0.99  
% 1.99/0.99  fof(f27,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f12])).
% 1.99/0.99  
% 1.99/0.99  fof(f1,axiom,(
% 1.99/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f9,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f1])).
% 1.99/0.99  
% 1.99/0.99  fof(f10,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.99/0.99    inference(flattening,[],[f9])).
% 1.99/0.99  
% 1.99/0.99  fof(f25,plain,(
% 1.99/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f10])).
% 1.99/0.99  
% 1.99/0.99  fof(f36,plain,(
% 1.99/0.99    v1_funct_1(sK3)),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f38,plain,(
% 1.99/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f39,plain,(
% 1.99/0.99    v1_funct_1(sK4)),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f42,plain,(
% 1.99/0.99    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f45,plain,(
% 1.99/0.99    ~v2_funct_1(sK4) | ~v2_funct_1(sK3)),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f2,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f11,plain,(
% 1.99/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.99    inference(ennf_transformation,[],[f2])).
% 1.99/0.99  
% 1.99/0.99  fof(f26,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f11])).
% 1.99/0.99  
% 1.99/0.99  fof(f24,plain,(
% 1.99/0.99    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f10])).
% 1.99/0.99  
% 1.99/0.99  fof(f4,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f13,plain,(
% 1.99/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.99    inference(ennf_transformation,[],[f4])).
% 1.99/0.99  
% 1.99/0.99  fof(f28,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f13])).
% 1.99/0.99  
% 1.99/0.99  fof(f43,plain,(
% 1.99/0.99    k2_relset_1(sK0,sK1,sK3) = sK1),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f6,axiom,(
% 1.99/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f16,plain,(
% 1.99/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.99/0.99    inference(ennf_transformation,[],[f6])).
% 1.99/0.99  
% 1.99/0.99  fof(f17,plain,(
% 1.99/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.99/0.99    inference(flattening,[],[f16])).
% 1.99/0.99  
% 1.99/0.99  fof(f35,plain,(
% 1.99/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f17])).
% 1.99/0.99  
% 1.99/0.99  fof(f30,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f20])).
% 1.99/0.99  
% 1.99/0.99  fof(f50,plain,(
% 1.99/0.99    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.99/0.99    inference(equality_resolution,[],[f30])).
% 1.99/0.99  
% 1.99/0.99  fof(f44,plain,(
% 1.99/0.99    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 1.99/0.99    inference(cnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f33,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f20])).
% 1.99/0.99  
% 1.99/0.99  fof(f48,plain,(
% 1.99/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.99/0.99    inference(equality_resolution,[],[f33])).
% 1.99/0.99  
% 1.99/0.99  cnf(c_10,plain,
% 1.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.99/0.99      | k1_xboole_0 = X2 ),
% 1.99/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_17,negated_conjecture,
% 1.99/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 1.99/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_294,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.99/0.99      | sK2 != X2
% 1.99/0.99      | sK1 != X1
% 1.99/0.99      | sK4 != X0
% 1.99/0.99      | k1_xboole_0 = X2 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_295,plain,
% 1.99/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.99/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 1.99/0.99      | k1_xboole_0 = sK2 ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_294]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_16,negated_conjecture,
% 1.99/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.99/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_297,plain,
% 1.99/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_295,c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_450,plain,
% 1.99/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_297]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_458,negated_conjecture,
% 1.99/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_781,plain,
% 1.99/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_3,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f27]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_465,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.99/0.99      | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_776,plain,
% 1.99/0.99      ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
% 1.99/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1162,plain,
% 1.99/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_781,c_776]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1246,plain,
% 1.99/0.99      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_450,c_1162]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_0,plain,
% 1.99/0.99      ( ~ v1_relat_1(X0)
% 1.99/0.99      | ~ v1_relat_1(X1)
% 1.99/0.99      | ~ v1_funct_1(X0)
% 1.99/0.99      | ~ v1_funct_1(X1)
% 1.99/0.99      | v2_funct_1(X1)
% 1.99/0.99      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 1.99/0.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f25]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_468,plain,
% 1.99/0.99      ( ~ v1_relat_1(X0_47)
% 1.99/0.99      | ~ v1_relat_1(X1_47)
% 1.99/0.99      | ~ v1_funct_1(X0_47)
% 1.99/0.99      | ~ v1_funct_1(X1_47)
% 1.99/0.99      | v2_funct_1(X1_47)
% 1.99/0.99      | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
% 1.99/0.99      | k1_relat_1(X1_47) != k2_relat_1(X0_47) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_773,plain,
% 1.99/0.99      ( k1_relat_1(X0_47) != k2_relat_1(X1_47)
% 1.99/0.99      | v1_relat_1(X1_47) != iProver_top
% 1.99/0.99      | v1_relat_1(X0_47) != iProver_top
% 1.99/0.99      | v1_funct_1(X0_47) != iProver_top
% 1.99/0.99      | v1_funct_1(X1_47) != iProver_top
% 1.99/0.99      | v2_funct_1(X0_47) = iProver_top
% 1.99/0.99      | v2_funct_1(k5_relat_1(X1_47,X0_47)) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1660,plain,
% 1.99/0.99      ( k2_relat_1(X0_47) != sK1
% 1.99/0.99      | sK2 = k1_xboole_0
% 1.99/0.99      | v1_relat_1(X0_47) != iProver_top
% 1.99/0.99      | v1_relat_1(sK4) != iProver_top
% 1.99/0.99      | v1_funct_1(X0_47) != iProver_top
% 1.99/0.99      | v1_funct_1(sK4) != iProver_top
% 1.99/0.99      | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
% 1.99/0.99      | v2_funct_1(sK4) = iProver_top ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_1246,c_773]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_21,negated_conjecture,
% 1.99/0.99      ( v1_funct_1(sK3) ),
% 1.99/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_22,plain,
% 1.99/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_19,negated_conjecture,
% 1.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.99/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_24,plain,
% 1.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_18,negated_conjecture,
% 1.99/0.99      ( v1_funct_1(sK4) ),
% 1.99/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_25,plain,
% 1.99/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_27,plain,
% 1.99/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_15,negated_conjecture,
% 1.99/0.99      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 1.99/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_28,plain,
% 1.99/0.99      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_12,negated_conjecture,
% 1.99/0.99      ( ~ v2_funct_1(sK3) | ~ v2_funct_1(sK4) ),
% 1.99/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_29,plain,
% 1.99/0.99      ( v2_funct_1(sK3) != iProver_top | v2_funct_1(sK4) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.99      | v1_relat_1(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f26]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_466,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.99/0.99      | v1_relat_1(X0_47) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_933,plain,
% 1.99/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.99/0.99      | v1_relat_1(sK4) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_466]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_934,plain,
% 1.99/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.99/0.99      | v1_relat_1(sK4) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_936,plain,
% 1.99/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.99/0.99      | v1_relat_1(sK3) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_466]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_937,plain,
% 1.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 1.99/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1,plain,
% 1.99/0.99      ( ~ v1_relat_1(X0)
% 1.99/0.99      | ~ v1_relat_1(X1)
% 1.99/0.99      | ~ v1_funct_1(X0)
% 1.99/0.99      | ~ v1_funct_1(X1)
% 1.99/0.99      | v2_funct_1(X0)
% 1.99/0.99      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 1.99/0.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f24]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_467,plain,
% 1.99/0.99      ( ~ v1_relat_1(X0_47)
% 1.99/0.99      | ~ v1_relat_1(X1_47)
% 1.99/0.99      | ~ v1_funct_1(X0_47)
% 1.99/0.99      | ~ v1_funct_1(X1_47)
% 1.99/0.99      | v2_funct_1(X0_47)
% 1.99/0.99      | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
% 1.99/0.99      | k1_relat_1(X1_47) != k2_relat_1(X0_47) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1007,plain,
% 1.99/0.99      ( ~ v1_relat_1(X0_47)
% 1.99/0.99      | ~ v1_relat_1(sK3)
% 1.99/0.99      | ~ v1_funct_1(X0_47)
% 1.99/0.99      | ~ v1_funct_1(sK3)
% 1.99/0.99      | ~ v2_funct_1(k5_relat_1(sK3,X0_47))
% 1.99/0.99      | v2_funct_1(sK3)
% 1.99/0.99      | k1_relat_1(X0_47) != k2_relat_1(sK3) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_467]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1153,plain,
% 1.99/0.99      ( ~ v1_relat_1(sK3)
% 1.99/0.99      | ~ v1_relat_1(sK4)
% 1.99/0.99      | ~ v1_funct_1(sK3)
% 1.99/0.99      | ~ v1_funct_1(sK4)
% 1.99/0.99      | ~ v2_funct_1(k5_relat_1(sK3,sK4))
% 1.99/0.99      | v2_funct_1(sK3)
% 1.99/0.99      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_1007]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1154,plain,
% 1.99/0.99      ( k1_relat_1(sK4) != k2_relat_1(sK3)
% 1.99/0.99      | v1_relat_1(sK3) != iProver_top
% 1.99/0.99      | v1_relat_1(sK4) != iProver_top
% 1.99/0.99      | v1_funct_1(sK3) != iProver_top
% 1.99/0.99      | v1_funct_1(sK4) != iProver_top
% 1.99/0.99      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 1.99/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_456,negated_conjecture,
% 1.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_783,plain,
% 1.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_464,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.99/0.99      | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_777,plain,
% 1.99/0.99      ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
% 1.99/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1172,plain,
% 1.99/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_783,c_777]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_14,negated_conjecture,
% 1.99/0.99      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 1.99/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_460,negated_conjecture,
% 1.99/0.99      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1174,plain,
% 1.99/0.99      ( k2_relat_1(sK3) = sK1 ),
% 1.99/0.99      inference(light_normalisation,[status(thm)],[c_1172,c_460]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1006,plain,
% 1.99/0.99      ( ~ v1_relat_1(X0_47)
% 1.99/0.99      | ~ v1_relat_1(sK3)
% 1.99/0.99      | ~ v1_funct_1(X0_47)
% 1.99/0.99      | ~ v1_funct_1(sK3)
% 1.99/0.99      | v2_funct_1(X0_47)
% 1.99/0.99      | ~ v2_funct_1(k5_relat_1(sK3,X0_47))
% 1.99/0.99      | k1_relat_1(X0_47) != k2_relat_1(sK3) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_468]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1188,plain,
% 1.99/0.99      ( ~ v1_relat_1(sK3)
% 1.99/0.99      | ~ v1_relat_1(sK4)
% 1.99/0.99      | ~ v1_funct_1(sK3)
% 1.99/0.99      | ~ v1_funct_1(sK4)
% 1.99/0.99      | ~ v2_funct_1(k5_relat_1(sK3,sK4))
% 1.99/0.99      | v2_funct_1(sK4)
% 1.99/0.99      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_1006]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1189,plain,
% 1.99/0.99      ( k1_relat_1(sK4) != k2_relat_1(sK3)
% 1.99/0.99      | v1_relat_1(sK3) != iProver_top
% 1.99/0.99      | v1_relat_1(sK4) != iProver_top
% 1.99/0.99      | v1_funct_1(sK3) != iProver_top
% 1.99/1.00      | v1_funct_1(sK4) != iProver_top
% 1.99/1.00      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 1.99/1.00      | v2_funct_1(sK4) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_1188]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_11,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.99/1.00      | ~ v1_funct_1(X0)
% 1.99/1.00      | ~ v1_funct_1(X3)
% 1.99/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_463,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.99/1.00      | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
% 1.99/1.00      | ~ v1_funct_1(X0_47)
% 1.99/1.00      | ~ v1_funct_1(X3_47)
% 1.99/1.00      | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
% 1.99/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_986,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.99/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_47,X4_47)))
% 1.99/1.00      | ~ v1_funct_1(X0_47)
% 1.99/1.00      | ~ v1_funct_1(sK4)
% 1.99/1.00      | k1_partfun1(X1_47,X2_47,X3_47,X4_47,X0_47,sK4) = k5_relat_1(X0_47,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_463]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1056,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 1.99/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 1.99/1.00      | ~ v1_funct_1(sK3)
% 1.99/1.00      | ~ v1_funct_1(sK4)
% 1.99/1.00      | k1_partfun1(X0_47,X1_47,X2_47,X3_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_986]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1090,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.99/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 1.99/1.00      | ~ v1_funct_1(sK3)
% 1.99/1.00      | ~ v1_funct_1(sK4)
% 1.99/1.00      | k1_partfun1(sK0,sK1,X0_47,X1_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1056]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1210,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.99/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.99/1.00      | ~ v1_funct_1(sK3)
% 1.99/1.00      | ~ v1_funct_1(sK4)
% 1.99/1.00      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1090]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_473,plain,
% 1.99/1.00      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 1.99/1.00      theory(equality) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1017,plain,
% 1.99/1.00      ( X0_47 != X1_47
% 1.99/1.00      | X0_47 = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
% 1.99/1.00      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != X1_47 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_473]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1211,plain,
% 1.99/1.00      ( X0_47 = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
% 1.99/1.00      | X0_47 != k5_relat_1(sK3,sK4)
% 1.99/1.00      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1017]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1347,plain,
% 1.99/1.00      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4)
% 1.99/1.00      | k5_relat_1(sK3,sK4) = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
% 1.99/1.00      | k5_relat_1(sK3,sK4) != k5_relat_1(sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1211]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_470,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1348,plain,
% 1.99/1.00      ( k5_relat_1(sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_470]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_474,plain,
% 1.99/1.00      ( ~ v2_funct_1(X0_47) | v2_funct_1(X1_47) | X1_47 != X0_47 ),
% 1.99/1.00      theory(equality) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_939,plain,
% 1.99/1.00      ( v2_funct_1(X0_47)
% 1.99/1.00      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 1.99/1.00      | X0_47 != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_474]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1432,plain,
% 1.99/1.00      ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 1.99/1.00      | v2_funct_1(k5_relat_1(sK3,sK4))
% 1.99/1.00      | k5_relat_1(sK3,sK4) != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_939]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1433,plain,
% 1.99/1.00      ( k5_relat_1(sK3,sK4) != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
% 1.99/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != iProver_top
% 1.99/1.00      | v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_1432]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1633,plain,
% 1.99/1.00      ( k1_relat_1(sK4) != X0_47
% 1.99/1.00      | k1_relat_1(sK4) = k2_relat_1(sK3)
% 1.99/1.00      | k2_relat_1(sK3) != X0_47 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_473]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1928,plain,
% 1.99/1.00      ( k1_relat_1(sK4) = k2_relat_1(sK3)
% 1.99/1.00      | k1_relat_1(sK4) != sK1
% 1.99/1.00      | k2_relat_1(sK3) != sK1 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1633]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1951,plain,
% 1.99/1.00      ( sK2 = k1_xboole_0 ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_1660,c_21,c_22,c_19,c_24,c_18,c_25,c_16,c_27,c_28,
% 1.99/1.00                 c_29,c_934,c_937,c_1154,c_1174,c_1189,c_1210,c_1246,
% 1.99/1.00                 c_1347,c_1348,c_1433,c_1928]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_9,plain,
% 1.99/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.99/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.99/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_268,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.99/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.99/1.00      | sK2 != X1
% 1.99/1.00      | sK1 != k1_xboole_0
% 1.99/1.00      | sK4 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_269,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 1.99/1.00      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 1.99/1.00      | sK1 != k1_xboole_0 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_268]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_452,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 1.99/1.00      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 1.99/1.00      | sK1 != k1_xboole_0 ),
% 1.99/1.00      inference(subtyping,[status(esa)],[c_269]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_787,plain,
% 1.99/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 1.99/1.00      | sK1 != k1_xboole_0
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1960,plain,
% 1.99/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 1.99/1.00      | sK1 != k1_xboole_0
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.99/1.00      inference(demodulation,[status(thm)],[c_1951,c_787]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_13,negated_conjecture,
% 1.99/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 1.99/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_461,negated_conjecture,
% 1.99/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 1.99/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1965,plain,
% 1.99/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.99/1.00      inference(demodulation,[status(thm)],[c_1951,c_461]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1966,plain,
% 1.99/1.00      ( sK1 = k1_xboole_0 ),
% 1.99/1.00      inference(equality_resolution_simp,[status(thm)],[c_1965]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1978,plain,
% 1.99/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 1.99/1.00      | k1_xboole_0 != k1_xboole_0
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.99/1.00      inference(light_normalisation,[status(thm)],[c_1960,c_1966]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1979,plain,
% 1.99/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.99/1.00      inference(equality_resolution_simp,[status(thm)],[c_1978]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1962,plain,
% 1.99/1.00      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 1.99/1.00      inference(demodulation,[status(thm)],[c_1951,c_1162]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1972,plain,
% 1.99/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 1.99/1.00      inference(light_normalisation,[status(thm)],[c_1962,c_1966]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1980,plain,
% 1.99/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.99/1.00      inference(demodulation,[status(thm)],[c_1979,c_1972]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1964,plain,
% 1.99/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 1.99/1.00      inference(demodulation,[status(thm)],[c_1951,c_781]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1969,plain,
% 1.99/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 1.99/1.00      inference(light_normalisation,[status(thm)],[c_1964,c_1966]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1983,plain,
% 1.99/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 1.99/1.00      inference(forward_subsumption_resolution,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_1980,c_1969]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1706,plain,
% 1.99/1.00      ( X0_47 != X1_47 | X0_47 = sK1 | sK1 != X1_47 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_473]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1927,plain,
% 1.99/1.00      ( k1_relat_1(sK4) != X0_47 | k1_relat_1(sK4) = sK1 | sK1 != X0_47 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1706]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1929,plain,
% 1.99/1.00      ( k1_relat_1(sK4) = sK1
% 1.99/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 1.99/1.00      | sK1 != k1_xboole_0 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1927]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_6,plain,
% 1.99/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 1.99/1.00      | k1_xboole_0 = X1
% 1.99/1.00      | k1_xboole_0 = X0 ),
% 1.99/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_232,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 1.99/1.00      | sK2 != k1_xboole_0
% 1.99/1.00      | sK1 != X1
% 1.99/1.00      | sK4 != X0
% 1.99/1.00      | k1_xboole_0 = X0
% 1.99/1.00      | k1_xboole_0 = X1 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_233,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 1.99/1.00      | sK2 != k1_xboole_0
% 1.99/1.00      | k1_xboole_0 = sK1
% 1.99/1.00      | k1_xboole_0 = sK4 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_232]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_454,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 1.99/1.00      | sK2 != k1_xboole_0
% 1.99/1.00      | k1_xboole_0 = sK1
% 1.99/1.00      | k1_xboole_0 = sK4 ),
% 1.99/1.00      inference(subtyping,[status(esa)],[c_233]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_785,plain,
% 1.99/1.00      ( sK2 != k1_xboole_0
% 1.99/1.00      | k1_xboole_0 = sK1
% 1.99/1.00      | k1_xboole_0 = sK4
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_491,plain,
% 1.99/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_470]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1549,plain,
% 1.99/1.00      ( X0_47 != X1_47 | X0_47 = sK2 | sK2 != X1_47 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_473]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1550,plain,
% 1.99/1.00      ( sK2 != k1_xboole_0
% 1.99/1.00      | k1_xboole_0 = sK2
% 1.99/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1549]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1782,plain,
% 1.99/1.00      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_785,c_491,c_461,c_1550]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1129,plain,
% 1.99/1.00      ( sK1 = sK1 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_470]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_959,plain,
% 1.99/1.00      ( sK1 != X0_47 | sK1 = k1_xboole_0 | k1_xboole_0 != X0_47 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_473]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1128,plain,
% 1.99/1.00      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_959]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(contradiction,plain,
% 1.99/1.00      ( $false ),
% 1.99/1.00      inference(minisat,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_1983,c_1928,c_1929,c_1782,c_1433,c_1348,c_1347,c_1246,
% 1.99/1.00                 c_1210,c_1189,c_1174,c_1154,c_1129,c_1128,c_937,c_934,
% 1.99/1.00                 c_29,c_28,c_27,c_16,c_25,c_18,c_24,c_19,c_22,c_21]) ).
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  ------                               Statistics
% 1.99/1.00  
% 1.99/1.00  ------ General
% 1.99/1.00  
% 1.99/1.00  abstr_ref_over_cycles:                  0
% 1.99/1.00  abstr_ref_under_cycles:                 0
% 1.99/1.00  gc_basic_clause_elim:                   0
% 1.99/1.00  forced_gc_time:                         0
% 1.99/1.00  parsing_time:                           0.008
% 1.99/1.00  unif_index_cands_time:                  0.
% 1.99/1.00  unif_index_add_time:                    0.
% 1.99/1.00  orderings_time:                         0.
% 1.99/1.00  out_proof_time:                         0.011
% 1.99/1.00  total_time:                             0.112
% 1.99/1.00  num_of_symbols:                         53
% 1.99/1.00  num_of_terms:                           1752
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing
% 1.99/1.00  
% 1.99/1.00  num_of_splits:                          0
% 1.99/1.00  num_of_split_atoms:                     0
% 1.99/1.00  num_of_reused_defs:                     0
% 1.99/1.00  num_eq_ax_congr_red:                    17
% 1.99/1.00  num_of_sem_filtered_clauses:            1
% 1.99/1.00  num_of_subtypes:                        3
% 1.99/1.00  monotx_restored_types:                  0
% 1.99/1.00  sat_num_of_epr_types:                   0
% 1.99/1.00  sat_num_of_non_cyclic_types:            0
% 1.99/1.00  sat_guarded_non_collapsed_types:        0
% 1.99/1.00  num_pure_diseq_elim:                    0
% 1.99/1.00  simp_replaced_by:                       0
% 1.99/1.00  res_preprocessed:                       107
% 1.99/1.00  prep_upred:                             0
% 1.99/1.00  prep_unflattend:                        34
% 1.99/1.00  smt_new_axioms:                         0
% 1.99/1.00  pred_elim_cands:                        4
% 1.99/1.00  pred_elim:                              1
% 1.99/1.00  pred_elim_cl:                           2
% 1.99/1.00  pred_elim_cycles:                       3
% 1.99/1.00  merged_defs:                            0
% 1.99/1.00  merged_defs_ncl:                        0
% 1.99/1.00  bin_hyper_res:                          0
% 1.99/1.00  prep_cycles:                            4
% 1.99/1.00  pred_elim_time:                         0.003
% 1.99/1.00  splitting_time:                         0.
% 1.99/1.00  sem_filter_time:                        0.
% 1.99/1.00  monotx_time:                            0.
% 1.99/1.00  subtype_inf_time:                       0.
% 1.99/1.00  
% 1.99/1.00  ------ Problem properties
% 1.99/1.00  
% 1.99/1.00  clauses:                                20
% 1.99/1.00  conjectures:                            8
% 1.99/1.00  epr:                                    4
% 1.99/1.00  horn:                                   16
% 1.99/1.00  ground:                                 14
% 1.99/1.00  unary:                                  6
% 1.99/1.00  binary:                                 7
% 1.99/1.00  lits:                                   53
% 1.99/1.00  lits_eq:                                22
% 1.99/1.00  fd_pure:                                0
% 1.99/1.00  fd_pseudo:                              0
% 1.99/1.00  fd_cond:                                0
% 1.99/1.00  fd_pseudo_cond:                         0
% 1.99/1.00  ac_symbols:                             0
% 1.99/1.00  
% 1.99/1.00  ------ Propositional Solver
% 1.99/1.00  
% 1.99/1.00  prop_solver_calls:                      28
% 1.99/1.00  prop_fast_solver_calls:                 728
% 1.99/1.00  smt_solver_calls:                       0
% 1.99/1.00  smt_fast_solver_calls:                  0
% 1.99/1.00  prop_num_of_clauses:                    578
% 1.99/1.00  prop_preprocess_simplified:             2628
% 1.99/1.00  prop_fo_subsumed:                       22
% 1.99/1.00  prop_solver_time:                       0.
% 1.99/1.00  smt_solver_time:                        0.
% 1.99/1.00  smt_fast_solver_time:                   0.
% 1.99/1.00  prop_fast_solver_time:                  0.
% 1.99/1.00  prop_unsat_core_time:                   0.
% 1.99/1.00  
% 1.99/1.00  ------ QBF
% 1.99/1.00  
% 1.99/1.00  qbf_q_res:                              0
% 1.99/1.00  qbf_num_tautologies:                    0
% 1.99/1.00  qbf_prep_cycles:                        0
% 1.99/1.00  
% 1.99/1.00  ------ BMC1
% 1.99/1.00  
% 1.99/1.00  bmc1_current_bound:                     -1
% 1.99/1.00  bmc1_last_solved_bound:                 -1
% 1.99/1.00  bmc1_unsat_core_size:                   -1
% 1.99/1.00  bmc1_unsat_core_parents_size:           -1
% 1.99/1.00  bmc1_merge_next_fun:                    0
% 1.99/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.99/1.00  
% 1.99/1.00  ------ Instantiation
% 1.99/1.00  
% 1.99/1.00  inst_num_of_clauses:                    203
% 1.99/1.00  inst_num_in_passive:                    34
% 1.99/1.00  inst_num_in_active:                     166
% 1.99/1.00  inst_num_in_unprocessed:                3
% 1.99/1.00  inst_num_of_loops:                      200
% 1.99/1.00  inst_num_of_learning_restarts:          0
% 1.99/1.00  inst_num_moves_active_passive:          28
% 1.99/1.00  inst_lit_activity:                      0
% 1.99/1.00  inst_lit_activity_moves:                0
% 1.99/1.00  inst_num_tautologies:                   0
% 1.99/1.00  inst_num_prop_implied:                  0
% 1.99/1.00  inst_num_existing_simplified:           0
% 1.99/1.00  inst_num_eq_res_simplified:             0
% 1.99/1.00  inst_num_child_elim:                    0
% 1.99/1.00  inst_num_of_dismatching_blockings:      19
% 1.99/1.00  inst_num_of_non_proper_insts:           203
% 1.99/1.00  inst_num_of_duplicates:                 0
% 1.99/1.00  inst_inst_num_from_inst_to_res:         0
% 1.99/1.00  inst_dismatching_checking_time:         0.
% 1.99/1.00  
% 1.99/1.00  ------ Resolution
% 1.99/1.00  
% 1.99/1.00  res_num_of_clauses:                     0
% 1.99/1.00  res_num_in_passive:                     0
% 1.99/1.00  res_num_in_active:                      0
% 1.99/1.00  res_num_of_loops:                       111
% 1.99/1.00  res_forward_subset_subsumed:            39
% 1.99/1.00  res_backward_subset_subsumed:           0
% 1.99/1.00  res_forward_subsumed:                   0
% 1.99/1.00  res_backward_subsumed:                  0
% 1.99/1.00  res_forward_subsumption_resolution:     0
% 1.99/1.00  res_backward_subsumption_resolution:    0
% 1.99/1.00  res_clause_to_clause_subsumption:       65
% 1.99/1.00  res_orphan_elimination:                 0
% 1.99/1.00  res_tautology_del:                      41
% 1.99/1.00  res_num_eq_res_simplified:              0
% 1.99/1.00  res_num_sel_changes:                    0
% 1.99/1.00  res_moves_from_active_to_pass:          0
% 1.99/1.00  
% 1.99/1.00  ------ Superposition
% 1.99/1.00  
% 1.99/1.00  sup_time_total:                         0.
% 1.99/1.00  sup_time_generating:                    0.
% 1.99/1.00  sup_time_sim_full:                      0.
% 1.99/1.00  sup_time_sim_immed:                     0.
% 1.99/1.00  
% 1.99/1.00  sup_num_of_clauses:                     30
% 1.99/1.00  sup_num_in_active:                      23
% 1.99/1.00  sup_num_in_passive:                     7
% 1.99/1.00  sup_num_of_loops:                       38
% 1.99/1.00  sup_fw_superposition:                   15
% 1.99/1.00  sup_bw_superposition:                   7
% 1.99/1.00  sup_immediate_simplified:               10
% 1.99/1.00  sup_given_eliminated:                   0
% 1.99/1.00  comparisons_done:                       0
% 1.99/1.00  comparisons_avoided:                    8
% 1.99/1.00  
% 1.99/1.00  ------ Simplifications
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  sim_fw_subset_subsumed:                 1
% 1.99/1.00  sim_bw_subset_subsumed:                 2
% 1.99/1.00  sim_fw_subsumed:                        0
% 1.99/1.00  sim_bw_subsumed:                        0
% 1.99/1.00  sim_fw_subsumption_res:                 1
% 1.99/1.00  sim_bw_subsumption_res:                 0
% 1.99/1.00  sim_tautology_del:                      0
% 1.99/1.00  sim_eq_tautology_del:                   2
% 1.99/1.00  sim_eq_res_simp:                        3
% 1.99/1.00  sim_fw_demodulated:                     1
% 1.99/1.00  sim_bw_demodulated:                     14
% 1.99/1.00  sim_light_normalised:                   9
% 1.99/1.00  sim_joinable_taut:                      0
% 1.99/1.00  sim_joinable_simp:                      0
% 1.99/1.00  sim_ac_normalised:                      0
% 1.99/1.00  sim_smt_subsumption:                    0
% 1.99/1.00  
%------------------------------------------------------------------------------
