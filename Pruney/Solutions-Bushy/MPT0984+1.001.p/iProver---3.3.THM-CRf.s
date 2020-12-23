%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0984+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:34 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  146 (1612 expanded)
%              Number of clauses        :  103 ( 562 expanded)
%              Number of leaves         :   12 ( 393 expanded)
%              Depth                    :   21
%              Number of atoms          :  574 (13267 expanded)
%              Number of equality atoms :  287 (4143 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(nnf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(equality_resolution,[],[f29])).

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

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f26])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

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

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_470,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_491,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_461,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_933,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47)
    | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1006,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_47,X4_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1_47,X2_47,X3_47,X4_47,X0_47,sK4) = k5_relat_1(X0_47,sK4) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_1098,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0_47,X1_47,X2_47,X3_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_1177,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_473,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1028,plain,
    ( X0_47 != X1_47
    | X0_47 = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != X1_47 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1178,plain,
    ( X0_47 = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
    | X0_47 != k5_relat_1(sK3,sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1341,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4)
    | k5_relat_1(sK3,sK4) = k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
    | k5_relat_1(sK3,sK4) != k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_1342,plain,
    ( k5_relat_1(sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_481,plain,
    ( ~ v2_funct_1(X0_47)
    | v2_funct_1(X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_953,plain,
    ( v2_funct_1(X0_47)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | X0_47 != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1455,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v2_funct_1(k5_relat_1(sK3,sK4))
    | k5_relat_1(sK3,sK4) != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_1554,plain,
    ( X0_47 != X1_47
    | X0_47 = sK2
    | sK2 != X1_47 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1555,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1554])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_295,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_294])).

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

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_775,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_1126,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_781,c_775])).

cnf(c_1267,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_450,c_1126])).

cnf(c_456,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_783,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_776,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_1136,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_783,c_776])).

cnf(c_14,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_460,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1138,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1136,c_460])).

cnf(c_11,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_463,plain,
    ( v2_funct_1(X0_47)
    | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | k2_relat_1(X0_47) != k1_relat_1(X1_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_778,plain,
    ( k2_relat_1(X0_47) != k1_relat_1(X1_47)
    | v2_funct_1(X0_47) = iProver_top
    | v2_funct_1(k5_relat_1(X0_47,X1_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1481,plain,
    ( k1_relat_1(X0_47) != sK1
    | v2_funct_1(k5_relat_1(sK3,X0_47)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_778])).

cnf(c_22,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_936,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_937,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_1719,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | k1_relat_1(X0_47) != sK1
    | v2_funct_1(k5_relat_1(sK3,X0_47)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1481,c_22,c_24,c_937])).

cnf(c_1720,plain,
    ( k1_relat_1(X0_47) != sK1
    | v2_funct_1(k5_relat_1(sK3,X0_47)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1719])).

cnf(c_1732,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1720])).

cnf(c_1754,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1732])).

cnf(c_10,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_464,plain,
    ( v2_funct_1(X0_47)
    | ~ v2_funct_1(k5_relat_1(X1_47,X0_47))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | k2_relat_1(X1_47) != k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_777,plain,
    ( k2_relat_1(X0_47) != k1_relat_1(X1_47)
    | v2_funct_1(X1_47) = iProver_top
    | v2_funct_1(k5_relat_1(X0_47,X1_47)) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_1469,plain,
    ( k1_relat_1(X0_47) != sK1
    | v2_funct_1(X0_47) = iProver_top
    | v2_funct_1(k5_relat_1(sK3,X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_777])).

cnf(c_1669,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | k1_relat_1(X0_47) != sK1
    | v2_funct_1(X0_47) = iProver_top
    | v2_funct_1(k5_relat_1(sK3,X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1469,c_22,c_24,c_937])).

cnf(c_1670,plain,
    ( k1_relat_1(X0_47) != sK1
    | v2_funct_1(X0_47) = iProver_top
    | v2_funct_1(k5_relat_1(sK3,X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1669])).

cnf(c_1733,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1670])).

cnf(c_1755,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1733])).

cnf(c_1783,plain,
    ( k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_785,c_21,c_19,c_18,c_16,c_15,c_12,c_491,c_461,c_933,c_1177,c_1341,c_1342,c_1455,c_1555,c_1754,c_1755])).

cnf(c_5,plain,
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
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

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

cnf(c_1796,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1783,c_787])).

cnf(c_1825,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1796])).

cnf(c_1799,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_1783,c_1126])).

cnf(c_1826,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1825,c_1799])).

cnf(c_1804,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1783,c_781])).

cnf(c_1829,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1826,c_1804])).

cnf(c_1801,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1783,c_1138])).

cnf(c_1641,plain,
    ( k2_relat_1(sK3) != X0_47
    | k2_relat_1(sK3) = k1_relat_1(sK4)
    | k1_relat_1(sK4) != X0_47 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1642,plain,
    ( k2_relat_1(sK3) = k1_relat_1(sK4)
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1641])).

cnf(c_1456,plain,
    ( k5_relat_1(sK3,sK4) != k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_992,plain,
    ( ~ v2_funct_1(k5_relat_1(X0_47,sK4))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(X0_47) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_1064,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK3) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_1065,plain,
    ( k2_relat_1(sK3) != k1_relat_1(sK4)
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_987,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,X0_47))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != k1_relat_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_1057,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK3) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_1058,plain,
    ( k2_relat_1(sK3) != k1_relat_1(sK4)
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_934,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_29,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_28,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1829,c_1801,c_1642,c_1456,c_1342,c_1341,c_1177,c_1065,c_1058,c_937,c_934,c_29,c_28,c_27,c_16,c_25,c_18,c_24,c_19,c_22,c_21])).


%------------------------------------------------------------------------------
