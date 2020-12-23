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
% DateTime   : Thu Dec  3 12:01:22 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 412 expanded)
%              Number of clauses        :   78 ( 138 expanded)
%              Number of leaves         :   14 ( 100 expanded)
%              Depth                    :   18
%              Number of atoms          :  396 (2699 expanded)
%              Number of equality atoms :  213 (1175 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X1,X2,X4) = X2
              & k2_relset_1(X0,X1,X3) = X1 )
           => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) != X2
        & k1_xboole_0 != X2
        & k2_relset_1(X1,X2,sK4) = X2
        & k2_relset_1(X0,X1,X3) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
            & k1_xboole_0 != X2
            & k2_relset_1(X1,X2,X4) = X2
            & k2_relset_1(X0,X1,X3) = X1
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) != sK2
          & k1_xboole_0 != sK2
          & k2_relset_1(sK1,sK2,X4) = sK2
          & k2_relset_1(sK0,sK1,sK3) = sK1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2
    & k1_xboole_0 != sK2
    & k2_relset_1(sK1,sK2,sK4) = sK2
    & k2_relset_1(sK0,sK1,sK3) = sK1
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f30,f29])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_828,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_838,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2710,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_838])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_996,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1204,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_1205,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1630,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1631,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1630])).

cnf(c_2848,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2710,c_33,c_1205,c_1631])).

cnf(c_3,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_826,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_833,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1854,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_826,c_833])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1856,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1854,c_21])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_relat_1(X2) != k2_relat_1(X0)
    | k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_836,plain,
    ( k2_relat_1(X0) != k2_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2740,plain,
    ( k2_relat_1(X0) != sK1
    | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(sK3,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1856,c_836])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1207,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_1208,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_1633,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1634,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1633])).

cnf(c_3158,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(sK3,X1))
    | k2_relat_1(X0) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2740,c_30,c_1208,c_1634])).

cnf(c_3159,plain,
    ( k2_relat_1(X0) != sK1
    | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(sK3,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3158])).

cnf(c_3168,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(sK3,X1))
    | sK1 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3159])).

cnf(c_3370,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(sK1),X0)) = k2_relat_1(k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3168])).

cnf(c_8,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_832,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2709,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_838])).

cnf(c_837,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4846,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2709,c_837])).

cnf(c_11063,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(sK1),X0)) = k2_relat_1(k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3370,c_4846])).

cnf(c_11069,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(sK1),sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2848,c_11063])).

cnf(c_1853,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_828,c_833])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1859,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1853,c_20])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_835,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2853,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK4)),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_2848,c_835])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_834,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2069,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_828,c_834])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK1 != X1
    | sK2 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_330,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_332,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_22,c_19])).

cnf(c_2074,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2069,c_332])).

cnf(c_2854,plain,
    ( k5_relat_1(k6_relat_1(sK1),sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2853,c_2074])).

cnf(c_11097,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_11069,c_1859,c_2854])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_829,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1872,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_829])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2250,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1872,c_31])).

cnf(c_2251,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2250])).

cnf(c_2261,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_826,c_2251])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2589,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2261,c_28])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_831,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3188,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_831])).

cnf(c_6131,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3188,c_28,c_30,c_31,c_33])).

cnf(c_6141,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_6131,c_833])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2592,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2 ),
    inference(demodulation,[status(thm)],[c_2589,c_18])).

cnf(c_6865,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) != sK2 ),
    inference(demodulation,[status(thm)],[c_6141,c_2592])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11097,c_6865])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n010.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 16:36:29 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  % Running in FOF mode
% 3.72/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.98  
% 3.72/0.98  ------  iProver source info
% 3.72/0.98  
% 3.72/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.98  git: non_committed_changes: false
% 3.72/0.98  git: last_make_outside_of_git: false
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options
% 3.72/0.98  
% 3.72/0.98  --out_options                           all
% 3.72/0.98  --tptp_safe_out                         true
% 3.72/0.98  --problem_path                          ""
% 3.72/0.98  --include_path                          ""
% 3.72/0.98  --clausifier                            res/vclausify_rel
% 3.72/0.98  --clausifier_options                    --mode clausify
% 3.72/0.98  --stdin                                 false
% 3.72/0.98  --stats_out                             all
% 3.72/0.98  
% 3.72/0.98  ------ General Options
% 3.72/0.98  
% 3.72/0.98  --fof                                   false
% 3.72/0.98  --time_out_real                         305.
% 3.72/0.98  --time_out_virtual                      -1.
% 3.72/0.98  --symbol_type_check                     false
% 3.72/0.98  --clausify_out                          false
% 3.72/0.98  --sig_cnt_out                           false
% 3.72/0.98  --trig_cnt_out                          false
% 3.72/0.98  --trig_cnt_out_tolerance                1.
% 3.72/0.98  --trig_cnt_out_sk_spl                   false
% 3.72/0.98  --abstr_cl_out                          false
% 3.72/0.98  
% 3.72/0.98  ------ Global Options
% 3.72/0.98  
% 3.72/0.98  --schedule                              default
% 3.72/0.98  --add_important_lit                     false
% 3.72/0.98  --prop_solver_per_cl                    1000
% 3.72/0.98  --min_unsat_core                        false
% 3.72/0.98  --soft_assumptions                      false
% 3.72/0.98  --soft_lemma_size                       3
% 3.72/0.98  --prop_impl_unit_size                   0
% 3.72/0.98  --prop_impl_unit                        []
% 3.72/0.98  --share_sel_clauses                     true
% 3.72/0.98  --reset_solvers                         false
% 3.72/0.98  --bc_imp_inh                            [conj_cone]
% 3.72/0.98  --conj_cone_tolerance                   3.
% 3.72/0.98  --extra_neg_conj                        none
% 3.72/0.98  --large_theory_mode                     true
% 3.72/0.98  --prolific_symb_bound                   200
% 3.72/0.98  --lt_threshold                          2000
% 3.72/0.98  --clause_weak_htbl                      true
% 3.72/0.98  --gc_record_bc_elim                     false
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing Options
% 3.72/0.98  
% 3.72/0.98  --preprocessing_flag                    true
% 3.72/0.98  --time_out_prep_mult                    0.1
% 3.72/0.98  --splitting_mode                        input
% 3.72/0.98  --splitting_grd                         true
% 3.72/0.98  --splitting_cvd                         false
% 3.72/0.98  --splitting_cvd_svl                     false
% 3.72/0.98  --splitting_nvd                         32
% 3.72/0.98  --sub_typing                            true
% 3.72/0.98  --prep_gs_sim                           true
% 3.72/0.98  --prep_unflatten                        true
% 3.72/0.98  --prep_res_sim                          true
% 3.72/0.98  --prep_upred                            true
% 3.72/0.98  --prep_sem_filter                       exhaustive
% 3.72/0.98  --prep_sem_filter_out                   false
% 3.72/0.98  --pred_elim                             true
% 3.72/0.98  --res_sim_input                         true
% 3.72/0.98  --eq_ax_congr_red                       true
% 3.72/0.98  --pure_diseq_elim                       true
% 3.72/0.98  --brand_transform                       false
% 3.72/0.98  --non_eq_to_eq                          false
% 3.72/0.98  --prep_def_merge                        true
% 3.72/0.98  --prep_def_merge_prop_impl              false
% 3.72/0.98  --prep_def_merge_mbd                    true
% 3.72/0.98  --prep_def_merge_tr_red                 false
% 3.72/0.98  --prep_def_merge_tr_cl                  false
% 3.72/0.98  --smt_preprocessing                     true
% 3.72/0.98  --smt_ac_axioms                         fast
% 3.72/0.98  --preprocessed_out                      false
% 3.72/0.98  --preprocessed_stats                    false
% 3.72/0.98  
% 3.72/0.98  ------ Abstraction refinement Options
% 3.72/0.98  
% 3.72/0.98  --abstr_ref                             []
% 3.72/0.98  --abstr_ref_prep                        false
% 3.72/0.98  --abstr_ref_until_sat                   false
% 3.72/0.98  --abstr_ref_sig_restrict                funpre
% 3.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.98  --abstr_ref_under                       []
% 3.72/0.98  
% 3.72/0.98  ------ SAT Options
% 3.72/0.98  
% 3.72/0.98  --sat_mode                              false
% 3.72/0.98  --sat_fm_restart_options                ""
% 3.72/0.98  --sat_gr_def                            false
% 3.72/0.98  --sat_epr_types                         true
% 3.72/0.98  --sat_non_cyclic_types                  false
% 3.72/0.98  --sat_finite_models                     false
% 3.72/0.98  --sat_fm_lemmas                         false
% 3.72/0.98  --sat_fm_prep                           false
% 3.72/0.98  --sat_fm_uc_incr                        true
% 3.72/0.98  --sat_out_model                         small
% 3.72/0.98  --sat_out_clauses                       false
% 3.72/0.98  
% 3.72/0.98  ------ QBF Options
% 3.72/0.98  
% 3.72/0.98  --qbf_mode                              false
% 3.72/0.98  --qbf_elim_univ                         false
% 3.72/0.98  --qbf_dom_inst                          none
% 3.72/0.98  --qbf_dom_pre_inst                      false
% 3.72/0.98  --qbf_sk_in                             false
% 3.72/0.98  --qbf_pred_elim                         true
% 3.72/0.98  --qbf_split                             512
% 3.72/0.98  
% 3.72/0.98  ------ BMC1 Options
% 3.72/0.98  
% 3.72/0.98  --bmc1_incremental                      false
% 3.72/0.98  --bmc1_axioms                           reachable_all
% 3.72/0.98  --bmc1_min_bound                        0
% 3.72/0.98  --bmc1_max_bound                        -1
% 3.72/0.98  --bmc1_max_bound_default                -1
% 3.72/0.98  --bmc1_symbol_reachability              true
% 3.72/0.98  --bmc1_property_lemmas                  false
% 3.72/0.98  --bmc1_k_induction                      false
% 3.72/0.98  --bmc1_non_equiv_states                 false
% 3.72/0.98  --bmc1_deadlock                         false
% 3.72/0.98  --bmc1_ucm                              false
% 3.72/0.98  --bmc1_add_unsat_core                   none
% 3.72/0.98  --bmc1_unsat_core_children              false
% 3.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.98  --bmc1_out_stat                         full
% 3.72/0.98  --bmc1_ground_init                      false
% 3.72/0.98  --bmc1_pre_inst_next_state              false
% 3.72/0.98  --bmc1_pre_inst_state                   false
% 3.72/0.98  --bmc1_pre_inst_reach_state             false
% 3.72/0.98  --bmc1_out_unsat_core                   false
% 3.72/0.98  --bmc1_aig_witness_out                  false
% 3.72/0.98  --bmc1_verbose                          false
% 3.72/0.98  --bmc1_dump_clauses_tptp                false
% 3.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.98  --bmc1_dump_file                        -
% 3.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.98  --bmc1_ucm_extend_mode                  1
% 3.72/0.98  --bmc1_ucm_init_mode                    2
% 3.72/0.98  --bmc1_ucm_cone_mode                    none
% 3.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.98  --bmc1_ucm_relax_model                  4
% 3.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.98  --bmc1_ucm_layered_model                none
% 3.72/0.98  --bmc1_ucm_max_lemma_size               10
% 3.72/0.98  
% 3.72/0.98  ------ AIG Options
% 3.72/0.98  
% 3.72/0.98  --aig_mode                              false
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation Options
% 3.72/0.98  
% 3.72/0.98  --instantiation_flag                    true
% 3.72/0.98  --inst_sos_flag                         false
% 3.72/0.98  --inst_sos_phase                        true
% 3.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel_side                     num_symb
% 3.72/0.98  --inst_solver_per_active                1400
% 3.72/0.98  --inst_solver_calls_frac                1.
% 3.72/0.98  --inst_passive_queue_type               priority_queues
% 3.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.98  --inst_passive_queues_freq              [25;2]
% 3.72/0.98  --inst_dismatching                      true
% 3.72/0.98  --inst_eager_unprocessed_to_passive     true
% 3.72/0.98  --inst_prop_sim_given                   true
% 3.72/0.98  --inst_prop_sim_new                     false
% 3.72/0.98  --inst_subs_new                         false
% 3.72/0.98  --inst_eq_res_simp                      false
% 3.72/0.98  --inst_subs_given                       false
% 3.72/0.98  --inst_orphan_elimination               true
% 3.72/0.98  --inst_learning_loop_flag               true
% 3.72/0.98  --inst_learning_start                   3000
% 3.72/0.98  --inst_learning_factor                  2
% 3.72/0.98  --inst_start_prop_sim_after_learn       3
% 3.72/0.98  --inst_sel_renew                        solver
% 3.72/0.98  --inst_lit_activity_flag                true
% 3.72/0.98  --inst_restr_to_given                   false
% 3.72/0.98  --inst_activity_threshold               500
% 3.72/0.98  --inst_out_proof                        true
% 3.72/0.98  
% 3.72/0.98  ------ Resolution Options
% 3.72/0.98  
% 3.72/0.98  --resolution_flag                       true
% 3.72/0.98  --res_lit_sel                           adaptive
% 3.72/0.98  --res_lit_sel_side                      none
% 3.72/0.98  --res_ordering                          kbo
% 3.72/0.98  --res_to_prop_solver                    active
% 3.72/0.98  --res_prop_simpl_new                    false
% 3.72/0.98  --res_prop_simpl_given                  true
% 3.72/0.98  --res_passive_queue_type                priority_queues
% 3.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.98  --res_passive_queues_freq               [15;5]
% 3.72/0.98  --res_forward_subs                      full
% 3.72/0.98  --res_backward_subs                     full
% 3.72/0.98  --res_forward_subs_resolution           true
% 3.72/0.98  --res_backward_subs_resolution          true
% 3.72/0.98  --res_orphan_elimination                true
% 3.72/0.98  --res_time_limit                        2.
% 3.72/0.98  --res_out_proof                         true
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Options
% 3.72/0.98  
% 3.72/0.98  --superposition_flag                    true
% 3.72/0.98  --sup_passive_queue_type                priority_queues
% 3.72/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.98  --demod_completeness_check              fast
% 3.72/0.98  --demod_use_ground                      true
% 3.72/0.98  --sup_to_prop_solver                    passive
% 3.72/0.98  --sup_prop_simpl_new                    true
% 3.72/0.98  --sup_prop_simpl_given                  true
% 3.72/0.98  --sup_fun_splitting                     false
% 3.72/0.98  --sup_smt_interval                      50000
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Simplification Setup
% 3.72/0.98  
% 3.72/0.98  --sup_indices_passive                   []
% 3.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_full_bw                           [BwDemod]
% 3.72/0.98  --sup_immed_triv                        [TrivRules]
% 3.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_immed_bw_main                     []
% 3.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  
% 3.72/0.98  ------ Combination Options
% 3.72/0.98  
% 3.72/0.98  --comb_res_mult                         3
% 3.72/0.98  --comb_sup_mult                         2
% 3.72/0.98  --comb_inst_mult                        10
% 3.72/0.98  
% 3.72/0.98  ------ Debug Options
% 3.72/0.98  
% 3.72/0.98  --dbg_backtrace                         false
% 3.72/0.98  --dbg_dump_prop_clauses                 false
% 3.72/0.98  --dbg_dump_prop_clauses_file            -
% 3.72/0.98  --dbg_out_stat                          false
% 3.72/0.98  ------ Parsing...
% 3.72/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  ------ Proving...
% 3.72/0.98  ------ Problem Properties 
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  clauses                                 26
% 3.72/0.98  conjectures                             8
% 3.72/0.98  EPR                                     3
% 3.72/0.98  Horn                                    23
% 3.72/0.98  unary                                   13
% 3.72/0.98  binary                                  4
% 3.72/0.98  lits                                    58
% 3.72/0.98  lits eq                                 25
% 3.72/0.98  fd_pure                                 0
% 3.72/0.98  fd_pseudo                               0
% 3.72/0.98  fd_cond                                 0
% 3.72/0.98  fd_pseudo_cond                          0
% 3.72/0.98  AC symbols                              0
% 3.72/0.98  
% 3.72/0.98  ------ Schedule dynamic 5 is on 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  Current options:
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options
% 3.72/0.98  
% 3.72/0.98  --out_options                           all
% 3.72/0.98  --tptp_safe_out                         true
% 3.72/0.98  --problem_path                          ""
% 3.72/0.98  --include_path                          ""
% 3.72/0.98  --clausifier                            res/vclausify_rel
% 3.72/0.98  --clausifier_options                    --mode clausify
% 3.72/0.98  --stdin                                 false
% 3.72/0.98  --stats_out                             all
% 3.72/0.98  
% 3.72/0.98  ------ General Options
% 3.72/0.98  
% 3.72/0.98  --fof                                   false
% 3.72/0.98  --time_out_real                         305.
% 3.72/0.98  --time_out_virtual                      -1.
% 3.72/0.98  --symbol_type_check                     false
% 3.72/0.98  --clausify_out                          false
% 3.72/0.98  --sig_cnt_out                           false
% 3.72/0.98  --trig_cnt_out                          false
% 3.72/0.98  --trig_cnt_out_tolerance                1.
% 3.72/0.98  --trig_cnt_out_sk_spl                   false
% 3.72/0.98  --abstr_cl_out                          false
% 3.72/0.98  
% 3.72/0.98  ------ Global Options
% 3.72/0.98  
% 3.72/0.98  --schedule                              default
% 3.72/0.98  --add_important_lit                     false
% 3.72/0.98  --prop_solver_per_cl                    1000
% 3.72/0.98  --min_unsat_core                        false
% 3.72/0.98  --soft_assumptions                      false
% 3.72/0.98  --soft_lemma_size                       3
% 3.72/0.98  --prop_impl_unit_size                   0
% 3.72/0.98  --prop_impl_unit                        []
% 3.72/0.98  --share_sel_clauses                     true
% 3.72/0.98  --reset_solvers                         false
% 3.72/0.98  --bc_imp_inh                            [conj_cone]
% 3.72/0.98  --conj_cone_tolerance                   3.
% 3.72/0.98  --extra_neg_conj                        none
% 3.72/0.98  --large_theory_mode                     true
% 3.72/0.98  --prolific_symb_bound                   200
% 3.72/0.98  --lt_threshold                          2000
% 3.72/0.98  --clause_weak_htbl                      true
% 3.72/0.98  --gc_record_bc_elim                     false
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing Options
% 3.72/0.98  
% 3.72/0.98  --preprocessing_flag                    true
% 3.72/0.98  --time_out_prep_mult                    0.1
% 3.72/0.98  --splitting_mode                        input
% 3.72/0.98  --splitting_grd                         true
% 3.72/0.98  --splitting_cvd                         false
% 3.72/0.98  --splitting_cvd_svl                     false
% 3.72/0.98  --splitting_nvd                         32
% 3.72/0.98  --sub_typing                            true
% 3.72/0.98  --prep_gs_sim                           true
% 3.72/0.98  --prep_unflatten                        true
% 3.72/0.98  --prep_res_sim                          true
% 3.72/0.98  --prep_upred                            true
% 3.72/0.98  --prep_sem_filter                       exhaustive
% 3.72/0.98  --prep_sem_filter_out                   false
% 3.72/0.98  --pred_elim                             true
% 3.72/0.98  --res_sim_input                         true
% 3.72/0.98  --eq_ax_congr_red                       true
% 3.72/0.98  --pure_diseq_elim                       true
% 3.72/0.98  --brand_transform                       false
% 3.72/0.98  --non_eq_to_eq                          false
% 3.72/0.98  --prep_def_merge                        true
% 3.72/0.98  --prep_def_merge_prop_impl              false
% 3.72/0.98  --prep_def_merge_mbd                    true
% 3.72/0.98  --prep_def_merge_tr_red                 false
% 3.72/0.98  --prep_def_merge_tr_cl                  false
% 3.72/0.98  --smt_preprocessing                     true
% 3.72/0.98  --smt_ac_axioms                         fast
% 3.72/0.98  --preprocessed_out                      false
% 3.72/0.98  --preprocessed_stats                    false
% 3.72/0.98  
% 3.72/0.98  ------ Abstraction refinement Options
% 3.72/0.98  
% 3.72/0.98  --abstr_ref                             []
% 3.72/0.98  --abstr_ref_prep                        false
% 3.72/0.98  --abstr_ref_until_sat                   false
% 3.72/0.98  --abstr_ref_sig_restrict                funpre
% 3.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.98  --abstr_ref_under                       []
% 3.72/0.98  
% 3.72/0.98  ------ SAT Options
% 3.72/0.98  
% 3.72/0.98  --sat_mode                              false
% 3.72/0.98  --sat_fm_restart_options                ""
% 3.72/0.98  --sat_gr_def                            false
% 3.72/0.98  --sat_epr_types                         true
% 3.72/0.98  --sat_non_cyclic_types                  false
% 3.72/0.98  --sat_finite_models                     false
% 3.72/0.98  --sat_fm_lemmas                         false
% 3.72/0.98  --sat_fm_prep                           false
% 3.72/0.98  --sat_fm_uc_incr                        true
% 3.72/0.98  --sat_out_model                         small
% 3.72/0.98  --sat_out_clauses                       false
% 3.72/0.98  
% 3.72/0.98  ------ QBF Options
% 3.72/0.98  
% 3.72/0.98  --qbf_mode                              false
% 3.72/0.98  --qbf_elim_univ                         false
% 3.72/0.98  --qbf_dom_inst                          none
% 3.72/0.98  --qbf_dom_pre_inst                      false
% 3.72/0.98  --qbf_sk_in                             false
% 3.72/0.98  --qbf_pred_elim                         true
% 3.72/0.98  --qbf_split                             512
% 3.72/0.98  
% 3.72/0.98  ------ BMC1 Options
% 3.72/0.98  
% 3.72/0.98  --bmc1_incremental                      false
% 3.72/0.98  --bmc1_axioms                           reachable_all
% 3.72/0.98  --bmc1_min_bound                        0
% 3.72/0.98  --bmc1_max_bound                        -1
% 3.72/0.98  --bmc1_max_bound_default                -1
% 3.72/0.98  --bmc1_symbol_reachability              true
% 3.72/0.98  --bmc1_property_lemmas                  false
% 3.72/0.98  --bmc1_k_induction                      false
% 3.72/0.98  --bmc1_non_equiv_states                 false
% 3.72/0.98  --bmc1_deadlock                         false
% 3.72/0.98  --bmc1_ucm                              false
% 3.72/0.98  --bmc1_add_unsat_core                   none
% 3.72/0.98  --bmc1_unsat_core_children              false
% 3.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.98  --bmc1_out_stat                         full
% 3.72/0.98  --bmc1_ground_init                      false
% 3.72/0.98  --bmc1_pre_inst_next_state              false
% 3.72/0.98  --bmc1_pre_inst_state                   false
% 3.72/0.98  --bmc1_pre_inst_reach_state             false
% 3.72/0.98  --bmc1_out_unsat_core                   false
% 3.72/0.98  --bmc1_aig_witness_out                  false
% 3.72/0.98  --bmc1_verbose                          false
% 3.72/0.98  --bmc1_dump_clauses_tptp                false
% 3.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.98  --bmc1_dump_file                        -
% 3.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.98  --bmc1_ucm_extend_mode                  1
% 3.72/0.98  --bmc1_ucm_init_mode                    2
% 3.72/0.98  --bmc1_ucm_cone_mode                    none
% 3.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.98  --bmc1_ucm_relax_model                  4
% 3.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.98  --bmc1_ucm_layered_model                none
% 3.72/0.98  --bmc1_ucm_max_lemma_size               10
% 3.72/0.98  
% 3.72/0.98  ------ AIG Options
% 3.72/0.98  
% 3.72/0.98  --aig_mode                              false
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation Options
% 3.72/0.98  
% 3.72/0.98  --instantiation_flag                    true
% 3.72/0.98  --inst_sos_flag                         false
% 3.72/0.98  --inst_sos_phase                        true
% 3.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel_side                     none
% 3.72/0.98  --inst_solver_per_active                1400
% 3.72/0.98  --inst_solver_calls_frac                1.
% 3.72/0.98  --inst_passive_queue_type               priority_queues
% 3.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.98  --inst_passive_queues_freq              [25;2]
% 3.72/0.98  --inst_dismatching                      true
% 3.72/0.98  --inst_eager_unprocessed_to_passive     true
% 3.72/0.98  --inst_prop_sim_given                   true
% 3.72/0.98  --inst_prop_sim_new                     false
% 3.72/0.98  --inst_subs_new                         false
% 3.72/0.98  --inst_eq_res_simp                      false
% 3.72/0.98  --inst_subs_given                       false
% 3.72/0.98  --inst_orphan_elimination               true
% 3.72/0.98  --inst_learning_loop_flag               true
% 3.72/0.98  --inst_learning_start                   3000
% 3.72/0.98  --inst_learning_factor                  2
% 3.72/0.98  --inst_start_prop_sim_after_learn       3
% 3.72/0.98  --inst_sel_renew                        solver
% 3.72/0.98  --inst_lit_activity_flag                true
% 3.72/0.98  --inst_restr_to_given                   false
% 3.72/0.98  --inst_activity_threshold               500
% 3.72/0.98  --inst_out_proof                        true
% 3.72/0.98  
% 3.72/0.98  ------ Resolution Options
% 3.72/0.98  
% 3.72/0.98  --resolution_flag                       false
% 3.72/0.98  --res_lit_sel                           adaptive
% 3.72/0.98  --res_lit_sel_side                      none
% 3.72/0.98  --res_ordering                          kbo
% 3.72/0.98  --res_to_prop_solver                    active
% 3.72/0.98  --res_prop_simpl_new                    false
% 3.72/0.98  --res_prop_simpl_given                  true
% 3.72/0.98  --res_passive_queue_type                priority_queues
% 3.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.98  --res_passive_queues_freq               [15;5]
% 3.72/0.98  --res_forward_subs                      full
% 3.72/0.98  --res_backward_subs                     full
% 3.72/0.98  --res_forward_subs_resolution           true
% 3.72/0.98  --res_backward_subs_resolution          true
% 3.72/0.98  --res_orphan_elimination                true
% 3.72/0.98  --res_time_limit                        2.
% 3.72/0.98  --res_out_proof                         true
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Options
% 3.72/0.98  
% 3.72/0.98  --superposition_flag                    true
% 3.72/0.98  --sup_passive_queue_type                priority_queues
% 3.72/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.98  --demod_completeness_check              fast
% 3.72/0.98  --demod_use_ground                      true
% 3.72/0.98  --sup_to_prop_solver                    passive
% 3.72/0.98  --sup_prop_simpl_new                    true
% 3.72/0.98  --sup_prop_simpl_given                  true
% 3.72/0.98  --sup_fun_splitting                     false
% 3.72/0.98  --sup_smt_interval                      50000
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Simplification Setup
% 3.72/0.98  
% 3.72/0.98  --sup_indices_passive                   []
% 3.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_full_bw                           [BwDemod]
% 3.72/0.98  --sup_immed_triv                        [TrivRules]
% 3.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_immed_bw_main                     []
% 3.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  
% 3.72/0.98  ------ Combination Options
% 3.72/0.98  
% 3.72/0.98  --comb_res_mult                         3
% 3.72/0.98  --comb_sup_mult                         2
% 3.72/0.98  --comb_inst_mult                        10
% 3.72/0.98  
% 3.72/0.98  ------ Debug Options
% 3.72/0.98  
% 3.72/0.98  --dbg_backtrace                         false
% 3.72/0.98  --dbg_dump_prop_clauses                 false
% 3.72/0.98  --dbg_dump_prop_clauses_file            -
% 3.72/0.98  --dbg_out_stat                          false
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS status Theorem for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  fof(f12,conjecture,(
% 3.72/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f13,negated_conjecture,(
% 3.72/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 3.72/0.98    inference(negated_conjecture,[],[f12])).
% 3.72/0.98  
% 3.72/0.98  fof(f26,plain,(
% 3.72/0.98    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2) & (k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.72/0.98    inference(ennf_transformation,[],[f13])).
% 3.72/0.98  
% 3.72/0.98  fof(f27,plain,(
% 3.72/0.98    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.72/0.98    inference(flattening,[],[f26])).
% 3.72/0.98  
% 3.72/0.98  fof(f30,plain,(
% 3.72/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,sK4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f29,plain,(
% 3.72/0.98    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) != sK2 & k1_xboole_0 != sK2 & k2_relset_1(sK1,sK2,X4) = sK2 & k2_relset_1(sK0,sK1,sK3) = sK1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f31,plain,(
% 3.72/0.98    (k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 & k1_xboole_0 != sK2 & k2_relset_1(sK1,sK2,sK4) = sK2 & k2_relset_1(sK0,sK1,sK3) = sK1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f30,f29])).
% 3.72/0.98  
% 3.72/0.98  fof(f55,plain,(
% 3.72/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f1,axiom,(
% 3.72/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f14,plain,(
% 3.72/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.72/0.98    inference(ennf_transformation,[],[f1])).
% 3.72/0.98  
% 3.72/0.98  fof(f32,plain,(
% 3.72/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f14])).
% 3.72/0.98  
% 3.72/0.98  fof(f2,axiom,(
% 3.72/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f33,plain,(
% 3.72/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f2])).
% 3.72/0.98  
% 3.72/0.98  fof(f4,axiom,(
% 3.72/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f36,plain,(
% 3.72/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.72/0.98    inference(cnf_transformation,[],[f4])).
% 3.72/0.98  
% 3.72/0.98  fof(f52,plain,(
% 3.72/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f7,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f19,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f7])).
% 3.72/0.98  
% 3.72/0.98  fof(f39,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f19])).
% 3.72/0.98  
% 3.72/0.98  fof(f56,plain,(
% 3.72/0.98    k2_relset_1(sK0,sK1,sK3) = sK1),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f3,axiom,(
% 3.72/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f15,plain,(
% 3.72/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.72/0.98    inference(ennf_transformation,[],[f3])).
% 3.72/0.98  
% 3.72/0.98  fof(f16,plain,(
% 3.72/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.72/0.98    inference(flattening,[],[f15])).
% 3.72/0.98  
% 3.72/0.98  fof(f34,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f16])).
% 3.72/0.98  
% 3.72/0.98  fof(f8,axiom,(
% 3.72/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f40,plain,(
% 3.72/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f8])).
% 3.72/0.98  
% 3.72/0.98  fof(f57,plain,(
% 3.72/0.98    k2_relset_1(sK1,sK2,sK4) = sK2),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f5,axiom,(
% 3.72/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f17,plain,(
% 3.72/0.98    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 3.72/0.98    inference(ennf_transformation,[],[f5])).
% 3.72/0.98  
% 3.72/0.98  fof(f37,plain,(
% 3.72/0.98    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f17])).
% 3.72/0.98  
% 3.72/0.98  fof(f6,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f18,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f6])).
% 3.72/0.98  
% 3.72/0.98  fof(f38,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f18])).
% 3.72/0.98  
% 3.72/0.98  fof(f9,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f20,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f9])).
% 3.72/0.98  
% 3.72/0.98  fof(f21,plain,(
% 3.72/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(flattening,[],[f20])).
% 3.72/0.98  
% 3.72/0.98  fof(f28,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(nnf_transformation,[],[f21])).
% 3.72/0.98  
% 3.72/0.98  fof(f41,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f28])).
% 3.72/0.98  
% 3.72/0.98  fof(f54,plain,(
% 3.72/0.98    v1_funct_2(sK4,sK1,sK2)),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f58,plain,(
% 3.72/0.98    k1_xboole_0 != sK2),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f11,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f24,plain,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.72/0.98    inference(ennf_transformation,[],[f11])).
% 3.72/0.98  
% 3.72/0.98  fof(f25,plain,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.72/0.98    inference(flattening,[],[f24])).
% 3.72/0.98  
% 3.72/0.98  fof(f49,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f25])).
% 3.72/0.98  
% 3.72/0.98  fof(f53,plain,(
% 3.72/0.98    v1_funct_1(sK4)),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f50,plain,(
% 3.72/0.98    v1_funct_1(sK3)),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f10,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f22,plain,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.72/0.98    inference(ennf_transformation,[],[f10])).
% 3.72/0.98  
% 3.72/0.98  fof(f23,plain,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.72/0.98    inference(flattening,[],[f22])).
% 3.72/0.98  
% 3.72/0.98  fof(f48,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f23])).
% 3.72/0.98  
% 3.72/0.98  fof(f59,plain,(
% 3.72/0.98    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  cnf(c_22,negated_conjecture,
% 3.72/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.72/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_828,plain,
% 3.72/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_0,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.98      | ~ v1_relat_1(X1)
% 3.72/0.98      | v1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_838,plain,
% 3.72/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.72/0.98      | v1_relat_1(X1) != iProver_top
% 3.72/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2710,plain,
% 3.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.72/0.98      | v1_relat_1(sK4) = iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_828,c_838]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_33,plain,
% 3.72/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_996,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | v1_relat_1(X0)
% 3.72/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1204,plain,
% 3.72/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.72/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 3.72/0.98      | v1_relat_1(sK4) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_996]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1205,plain,
% 3.72/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.72/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.72/0.98      | v1_relat_1(sK4) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1204]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1,plain,
% 3.72/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.72/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1630,plain,
% 3.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1631,plain,
% 3.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1630]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2848,plain,
% 3.72/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_2710,c_33,c_1205,c_1631]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3,plain,
% 3.72/0.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_25,negated_conjecture,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.72/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_826,plain,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_833,plain,
% 3.72/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1854,plain,
% 3.72/0.98      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_826,c_833]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_21,negated_conjecture,
% 3.72/0.98      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 3.72/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1856,plain,
% 3.72/0.98      ( k2_relat_1(sK3) = sK1 ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_1854,c_21]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2,plain,
% 3.72/0.98      ( ~ v1_relat_1(X0)
% 3.72/0.98      | ~ v1_relat_1(X1)
% 3.72/0.98      | ~ v1_relat_1(X2)
% 3.72/0.98      | k2_relat_1(X2) != k2_relat_1(X0)
% 3.72/0.98      | k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 3.72/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_836,plain,
% 3.72/0.98      ( k2_relat_1(X0) != k2_relat_1(X1)
% 3.72/0.98      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
% 3.72/0.98      | v1_relat_1(X1) != iProver_top
% 3.72/0.98      | v1_relat_1(X2) != iProver_top
% 3.72/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2740,plain,
% 3.72/0.98      ( k2_relat_1(X0) != sK1
% 3.72/0.98      | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(sK3,X1))
% 3.72/0.98      | v1_relat_1(X0) != iProver_top
% 3.72/0.98      | v1_relat_1(X1) != iProver_top
% 3.72/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1856,c_836]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_30,plain,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1207,plain,
% 3.72/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.72/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.72/0.98      | v1_relat_1(sK3) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_996]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1208,plain,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.72/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.72/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1633,plain,
% 3.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1634,plain,
% 3.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1633]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3158,plain,
% 3.72/0.98      ( v1_relat_1(X1) != iProver_top
% 3.72/0.98      | v1_relat_1(X0) != iProver_top
% 3.72/0.98      | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(sK3,X1))
% 3.72/0.98      | k2_relat_1(X0) != sK1 ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_2740,c_30,c_1208,c_1634]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3159,plain,
% 3.72/0.98      ( k2_relat_1(X0) != sK1
% 3.72/0.98      | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(sK3,X1))
% 3.72/0.98      | v1_relat_1(X0) != iProver_top
% 3.72/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.72/0.98      inference(renaming,[status(thm)],[c_3158]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3168,plain,
% 3.72/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(sK3,X1))
% 3.72/0.98      | sK1 != X0
% 3.72/0.98      | v1_relat_1(X1) != iProver_top
% 3.72/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_3,c_3159]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3370,plain,
% 3.72/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(sK1),X0)) = k2_relat_1(k5_relat_1(sK3,X0))
% 3.72/0.98      | v1_relat_1(X0) != iProver_top
% 3.72/0.98      | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
% 3.72/0.98      inference(equality_resolution,[status(thm)],[c_3168]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_8,plain,
% 3.72/0.98      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.72/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_832,plain,
% 3.72/0.98      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2709,plain,
% 3.72/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
% 3.72/0.98      | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_832,c_838]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_837,plain,
% 3.72/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4846,plain,
% 3.72/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.72/0.98      inference(forward_subsumption_resolution,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_2709,c_837]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_11063,plain,
% 3.72/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(sK1),X0)) = k2_relat_1(k5_relat_1(sK3,X0))
% 3.72/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.98      inference(forward_subsumption_resolution,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_3370,c_4846]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_11069,plain,
% 3.72/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(sK1),sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2848,c_11063]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1853,plain,
% 3.72/0.98      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_828,c_833]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_20,negated_conjecture,
% 3.72/0.98      ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1859,plain,
% 3.72/0.98      ( k2_relat_1(sK4) = sK2 ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_1853,c_20]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5,plain,
% 3.72/0.98      ( ~ v1_relat_1(X0)
% 3.72/0.98      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_835,plain,
% 3.72/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 3.72/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2853,plain,
% 3.72/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(sK4)),sK4) = sK4 ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2848,c_835]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_834,plain,
% 3.72/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2069,plain,
% 3.72/0.98      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_828,c_834]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_14,plain,
% 3.72/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.72/0.98      | k1_xboole_0 = X2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_23,negated_conjecture,
% 3.72/0.98      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.72/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_329,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.72/0.98      | sK4 != X0
% 3.72/0.98      | sK1 != X1
% 3.72/0.98      | sK2 != X2
% 3.72/0.98      | k1_xboole_0 = X2 ),
% 3.72/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_330,plain,
% 3.72/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.72/0.98      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.72/0.98      | k1_xboole_0 = sK2 ),
% 3.72/0.98      inference(unflattening,[status(thm)],[c_329]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_19,negated_conjecture,
% 3.72/0.98      ( k1_xboole_0 != sK2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_332,plain,
% 3.72/0.98      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_330,c_22,c_19]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2074,plain,
% 3.72/0.98      ( k1_relat_1(sK4) = sK1 ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_2069,c_332]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2854,plain,
% 3.72/0.98      ( k5_relat_1(k6_relat_1(sK1),sK4) = sK4 ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_2853,c_2074]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_11097,plain,
% 3.72/0.98      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.72/0.98      inference(light_normalisation,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_11069,c_1859,c_2854]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_17,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.72/0.98      | ~ v1_funct_1(X0)
% 3.72/0.98      | ~ v1_funct_1(X3)
% 3.72/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_829,plain,
% 3.72/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.72/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.72/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.98      | v1_funct_1(X5) != iProver_top
% 3.72/0.98      | v1_funct_1(X4) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1872,plain,
% 3.72/0.98      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.98      | v1_funct_1(X2) != iProver_top
% 3.72/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_828,c_829]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_24,negated_conjecture,
% 3.72/0.98      ( v1_funct_1(sK4) ),
% 3.72/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_31,plain,
% 3.72/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2250,plain,
% 3.72/0.98      ( v1_funct_1(X2) != iProver_top
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.98      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_1872,c_31]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2251,plain,
% 3.72/0.98      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.72/0.98      inference(renaming,[status(thm)],[c_2250]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2261,plain,
% 3.72/0.98      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.72/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_826,c_2251]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_27,negated_conjecture,
% 3.72/0.98      ( v1_funct_1(sK3) ),
% 3.72/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_28,plain,
% 3.72/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2589,plain,
% 3.72/0.98      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_2261,c_28]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_15,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.72/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.98      | ~ v1_funct_1(X0)
% 3.72/0.98      | ~ v1_funct_1(X3) ),
% 3.72/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_831,plain,
% 3.72/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.72/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.72/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.72/0.98      | v1_funct_1(X0) != iProver_top
% 3.72/0.98      | v1_funct_1(X3) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3188,plain,
% 3.72/0.98      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.72/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.72/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.72/0.98      | v1_funct_1(sK4) != iProver_top
% 3.72/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2589,c_831]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6131,plain,
% 3.72/0.98      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_3188,c_28,c_30,c_31,c_33]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6141,plain,
% 3.72/0.98      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_6131,c_833]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_18,negated_conjecture,
% 3.72/0.98      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2592,plain,
% 3.72/0.98      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2 ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_2589,c_18]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6865,plain,
% 3.72/0.98      ( k2_relat_1(k5_relat_1(sK3,sK4)) != sK2 ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_6141,c_2592]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(contradiction,plain,
% 3.72/0.98      ( $false ),
% 3.72/0.98      inference(minisat,[status(thm)],[c_11097,c_6865]) ).
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  ------                               Statistics
% 3.72/0.98  
% 3.72/0.98  ------ General
% 3.72/0.98  
% 3.72/0.98  abstr_ref_over_cycles:                  0
% 3.72/0.98  abstr_ref_under_cycles:                 0
% 3.72/0.98  gc_basic_clause_elim:                   0
% 3.72/0.98  forced_gc_time:                         0
% 3.72/0.98  parsing_time:                           0.008
% 3.72/0.98  unif_index_cands_time:                  0.
% 3.72/0.98  unif_index_add_time:                    0.
% 3.72/0.98  orderings_time:                         0.
% 3.72/0.98  out_proof_time:                         0.011
% 3.72/0.98  total_time:                             0.39
% 3.72/0.98  num_of_symbols:                         50
% 3.72/0.98  num_of_terms:                           12745
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing
% 3.72/0.98  
% 3.72/0.98  num_of_splits:                          0
% 3.72/0.98  num_of_split_atoms:                     0
% 3.72/0.98  num_of_reused_defs:                     0
% 3.72/0.98  num_eq_ax_congr_red:                    5
% 3.72/0.98  num_of_sem_filtered_clauses:            1
% 3.72/0.98  num_of_subtypes:                        0
% 3.72/0.98  monotx_restored_types:                  0
% 3.72/0.98  sat_num_of_epr_types:                   0
% 3.72/0.98  sat_num_of_non_cyclic_types:            0
% 3.72/0.98  sat_guarded_non_collapsed_types:        0
% 3.72/0.98  num_pure_diseq_elim:                    0
% 3.72/0.98  simp_replaced_by:                       0
% 3.72/0.98  res_preprocessed:                       135
% 3.72/0.98  prep_upred:                             0
% 3.72/0.98  prep_unflattend:                        34
% 3.72/0.98  smt_new_axioms:                         0
% 3.72/0.98  pred_elim_cands:                        3
% 3.72/0.98  pred_elim:                              1
% 3.72/0.98  pred_elim_cl:                           2
% 3.72/0.98  pred_elim_cycles:                       3
% 3.72/0.98  merged_defs:                            0
% 3.72/0.98  merged_defs_ncl:                        0
% 3.72/0.98  bin_hyper_res:                          0
% 3.72/0.98  prep_cycles:                            4
% 3.72/0.98  pred_elim_time:                         0.003
% 3.72/0.98  splitting_time:                         0.
% 3.72/0.98  sem_filter_time:                        0.
% 3.72/0.98  monotx_time:                            0.
% 3.72/0.98  subtype_inf_time:                       0.
% 3.72/0.98  
% 3.72/0.98  ------ Problem properties
% 3.72/0.98  
% 3.72/0.98  clauses:                                26
% 3.72/0.98  conjectures:                            8
% 3.72/0.98  epr:                                    3
% 3.72/0.98  horn:                                   23
% 3.72/0.98  ground:                                 14
% 3.72/0.98  unary:                                  13
% 3.72/0.98  binary:                                 4
% 3.72/0.98  lits:                                   58
% 3.72/0.98  lits_eq:                                25
% 3.72/0.98  fd_pure:                                0
% 3.72/0.98  fd_pseudo:                              0
% 3.72/0.98  fd_cond:                                0
% 3.72/0.98  fd_pseudo_cond:                         0
% 3.72/0.98  ac_symbols:                             0
% 3.72/0.98  
% 3.72/0.98  ------ Propositional Solver
% 3.72/0.98  
% 3.72/0.98  prop_solver_calls:                      26
% 3.72/0.98  prop_fast_solver_calls:                 1116
% 3.72/0.98  smt_solver_calls:                       0
% 3.72/0.98  smt_fast_solver_calls:                  0
% 3.72/0.98  prop_num_of_clauses:                    5453
% 3.72/0.98  prop_preprocess_simplified:             9636
% 3.72/0.98  prop_fo_subsumed:                       80
% 3.72/0.98  prop_solver_time:                       0.
% 3.72/0.98  smt_solver_time:                        0.
% 3.72/0.98  smt_fast_solver_time:                   0.
% 3.72/0.98  prop_fast_solver_time:                  0.
% 3.72/0.98  prop_unsat_core_time:                   0.001
% 3.72/0.98  
% 3.72/0.98  ------ QBF
% 3.72/0.98  
% 3.72/0.98  qbf_q_res:                              0
% 3.72/0.98  qbf_num_tautologies:                    0
% 3.72/0.98  qbf_prep_cycles:                        0
% 3.72/0.98  
% 3.72/0.98  ------ BMC1
% 3.72/0.98  
% 3.72/0.98  bmc1_current_bound:                     -1
% 3.72/0.98  bmc1_last_solved_bound:                 -1
% 3.72/0.98  bmc1_unsat_core_size:                   -1
% 3.72/0.98  bmc1_unsat_core_parents_size:           -1
% 3.72/0.98  bmc1_merge_next_fun:                    0
% 3.72/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation
% 3.72/0.98  
% 3.72/0.98  inst_num_of_clauses:                    1375
% 3.72/0.98  inst_num_in_passive:                    92
% 3.72/0.98  inst_num_in_active:                     603
% 3.72/0.98  inst_num_in_unprocessed:                682
% 3.72/0.98  inst_num_of_loops:                      610
% 3.72/0.98  inst_num_of_learning_restarts:          0
% 3.72/0.98  inst_num_moves_active_passive:          6
% 3.72/0.98  inst_lit_activity:                      0
% 3.72/0.98  inst_lit_activity_moves:                0
% 3.72/0.98  inst_num_tautologies:                   0
% 3.72/0.98  inst_num_prop_implied:                  0
% 3.72/0.98  inst_num_existing_simplified:           0
% 3.72/0.98  inst_num_eq_res_simplified:             0
% 3.72/0.98  inst_num_child_elim:                    0
% 3.72/0.98  inst_num_of_dismatching_blockings:      103
% 3.72/0.98  inst_num_of_non_proper_insts:           821
% 3.72/0.98  inst_num_of_duplicates:                 0
% 3.72/0.98  inst_inst_num_from_inst_to_res:         0
% 3.72/0.99  inst_dismatching_checking_time:         0.
% 3.72/0.99  
% 3.72/0.99  ------ Resolution
% 3.72/0.99  
% 3.72/0.99  res_num_of_clauses:                     0
% 3.72/0.99  res_num_in_passive:                     0
% 3.72/0.99  res_num_in_active:                      0
% 3.72/0.99  res_num_of_loops:                       139
% 3.72/0.99  res_forward_subset_subsumed:            36
% 3.72/0.99  res_backward_subset_subsumed:           4
% 3.72/0.99  res_forward_subsumed:                   0
% 3.72/0.99  res_backward_subsumed:                  0
% 3.72/0.99  res_forward_subsumption_resolution:     0
% 3.72/0.99  res_backward_subsumption_resolution:    0
% 3.72/0.99  res_clause_to_clause_subsumption:       728
% 3.72/0.99  res_orphan_elimination:                 0
% 3.72/0.99  res_tautology_del:                      69
% 3.72/0.99  res_num_eq_res_simplified:              0
% 3.72/0.99  res_num_sel_changes:                    0
% 3.72/0.99  res_moves_from_active_to_pass:          0
% 3.72/0.99  
% 3.72/0.99  ------ Superposition
% 3.72/0.99  
% 3.72/0.99  sup_time_total:                         0.
% 3.72/0.99  sup_time_generating:                    0.
% 3.72/0.99  sup_time_sim_full:                      0.
% 3.72/0.99  sup_time_sim_immed:                     0.
% 3.72/0.99  
% 3.72/0.99  sup_num_of_clauses:                     302
% 3.72/0.99  sup_num_in_active:                      119
% 3.72/0.99  sup_num_in_passive:                     183
% 3.72/0.99  sup_num_of_loops:                       120
% 3.72/0.99  sup_fw_superposition:                   213
% 3.72/0.99  sup_bw_superposition:                   87
% 3.72/0.99  sup_immediate_simplified:               69
% 3.72/0.99  sup_given_eliminated:                   0
% 3.72/0.99  comparisons_done:                       0
% 3.72/0.99  comparisons_avoided:                    3
% 3.72/0.99  
% 3.72/0.99  ------ Simplifications
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  sim_fw_subset_subsumed:                 1
% 3.72/0.99  sim_bw_subset_subsumed:                 5
% 3.72/0.99  sim_fw_subsumed:                        0
% 3.72/0.99  sim_bw_subsumed:                        0
% 3.72/0.99  sim_fw_subsumption_res:                 7
% 3.72/0.99  sim_bw_subsumption_res:                 0
% 3.72/0.99  sim_tautology_del:                      0
% 3.72/0.99  sim_eq_tautology_del:                   15
% 3.72/0.99  sim_eq_res_simp:                        0
% 3.72/0.99  sim_fw_demodulated:                     0
% 3.72/0.99  sim_bw_demodulated:                     2
% 3.72/0.99  sim_light_normalised:                   68
% 3.72/0.99  sim_joinable_taut:                      0
% 3.72/0.99  sim_joinable_simp:                      0
% 3.72/0.99  sim_ac_normalised:                      0
% 3.72/0.99  sim_smt_subsumption:                    0
% 3.72/0.99  
%------------------------------------------------------------------------------
