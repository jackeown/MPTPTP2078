%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:19 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  150 (4027 expanded)
%              Number of clauses        :  107 (1391 expanded)
%              Number of leaves         :   11 ( 953 expanded)
%              Depth                    :   25
%              Number of atoms          :  566 (33077 expanded)
%              Number of equality atoms :  281 (9622 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f23,plain,(
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

fof(f22,plain,
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

fof(f24,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f23,f22])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f32])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_471,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_825,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_819,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_1198,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_825,c_819])).

cnf(c_15,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_475,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1200,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1198,c_475])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_304,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_306,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_17])).

cnf(c_465,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_306])).

cnf(c_473,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_823,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_818,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_1188,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_823,c_818])).

cnf(c_1261,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_465,c_1188])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_481,plain,
    ( ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | v2_funct_1(X0_47)
    | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | k1_relat_1(X1_47) != k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_817,plain,
    ( k1_relat_1(X0_47) != k2_relat_1(X1_47)
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v2_funct_1(X1_47) = iProver_top
    | v2_funct_1(k5_relat_1(X1_47,X0_47)) != iProver_top
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_1528,plain,
    ( k2_relat_1(X0_47) != sK1
    | sK2 = k1_xboole_0
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(X0_47) = iProver_top
    | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_817])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ v1_relat_1(X1_47)
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_982,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47)
    | ~ v1_relat_1(k2_zfmisc_1(X1_47,X2_47)) ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_1153,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_1154,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_483,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1242,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1243,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_2328,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
    | v2_funct_1(X0_47) = iProver_top
    | k2_relat_1(X0_47) != sK1
    | sK2 = k1_xboole_0
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1528,c_26,c_28,c_1154,c_1243])).

cnf(c_2329,plain,
    ( k2_relat_1(X0_47) != sK1
    | sK2 = k1_xboole_0
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) = iProver_top
    | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2328])).

cnf(c_2340,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_2329])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_30,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_1157,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_1245,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1246,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47)
    | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_820,plain,
    ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X4_47,X5_47) = k5_relat_1(X4_47,X5_47)
    | m1_subset_1(X5_47,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(X4_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X5_47) != iProver_top
    | v1_funct_1(X4_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_1606,plain,
    ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_820])).

cnf(c_1682,plain,
    ( v1_funct_1(X2_47) != iProver_top
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1606,c_26])).

cnf(c_1683,plain,
    ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1682])).

cnf(c_1692,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_1683])).

cnf(c_1059,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_47,X4_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1_47,X2_47,X3_47,X4_47,X0_47,sK4) = k5_relat_1(X0_47,sK4) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0_47,X1_47,X2_47,X3_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_1143,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,X0_47,X1_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_1251,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_1758,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1692,c_22,c_20,c_19,c_17,c_1251])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_474,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_822,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_1761,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1758,c_822])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_482,plain,
    ( ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | v2_funct_1(X1_47)
    | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | k1_relat_1(X1_47) != k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_816,plain,
    ( k1_relat_1(X0_47) != k2_relat_1(X1_47)
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v2_funct_1(X0_47) = iProver_top
    | v2_funct_1(k5_relat_1(X1_47,X0_47)) != iProver_top
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_1480,plain,
    ( k2_relat_1(X0_47) != sK1
    | sK2 = k1_xboole_0
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_816])).

cnf(c_1952,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
    | k2_relat_1(X0_47) != sK1
    | sK2 = k1_xboole_0
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1480,c_26,c_28,c_1154,c_1243])).

cnf(c_1953,plain,
    ( k2_relat_1(X0_47) != sK1
    | sK2 = k1_xboole_0
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1952])).

cnf(c_1964,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1953])).

cnf(c_2041,plain,
    ( v2_funct_1(sK4) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1964,c_23,c_25,c_1157,c_1246,c_1761])).

cnf(c_2042,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2041])).

cnf(c_2343,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2340,c_23,c_25,c_30,c_1157,c_1246,c_1761,c_2042])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_476,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2358,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2343,c_476])).

cnf(c_2359,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2358])).

cnf(c_2478,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2359,c_1200])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_278,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_467,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_278])).

cnf(c_829,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_2353,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2343,c_829])).

cnf(c_2371,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2353,c_2359])).

cnf(c_2372,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2371])).

cnf(c_2355,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2343,c_1188])).

cnf(c_2365,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2355,c_2359])).

cnf(c_2373,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2372,c_2365])).

cnf(c_2357,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2343,c_823])).

cnf(c_2362,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2357,c_2359])).

cnf(c_2376,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2373,c_2362])).

cnf(c_488,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1943,plain,
    ( k1_relat_1(sK4) != X0_47
    | k1_relat_1(sK4) = k2_relat_1(sK3)
    | k2_relat_1(sK3) != X0_47 ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_1944,plain,
    ( k1_relat_1(sK4) = k2_relat_1(sK3)
    | k1_relat_1(sK4) != k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_1050,plain,
    ( ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK3)
    | v2_funct_1(X0_47)
    | ~ v2_funct_1(k5_relat_1(sK3,X0_47))
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(X0_47) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_1423,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1424,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1423])).

cnf(c_1040,plain,
    ( ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,X0_47))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(X0_47) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1417,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_1418,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1417])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2478,c_2376,c_1944,c_1761,c_1424,c_1418,c_1246,c_1243,c_1157,c_1154,c_30,c_28,c_26,c_25,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.16/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.00  
% 2.16/1.00  ------  iProver source info
% 2.16/1.00  
% 2.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.00  git: non_committed_changes: false
% 2.16/1.00  git: last_make_outside_of_git: false
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     num_symb
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       true
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  ------ Parsing...
% 2.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.00  ------ Proving...
% 2.16/1.00  ------ Problem Properties 
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  clauses                                 21
% 2.16/1.00  conjectures                             8
% 2.16/1.00  EPR                                     4
% 2.16/1.00  Horn                                    17
% 2.16/1.00  unary                                   7
% 2.16/1.00  binary                                  6
% 2.16/1.00  lits                                    55
% 2.16/1.00  lits eq                                 22
% 2.16/1.00  fd_pure                                 0
% 2.16/1.00  fd_pseudo                               0
% 2.16/1.00  fd_cond                                 0
% 2.16/1.00  fd_pseudo_cond                          0
% 2.16/1.00  AC symbols                              0
% 2.16/1.00  
% 2.16/1.00  ------ Schedule dynamic 5 is on 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  Current options:
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     none
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       false
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ Proving...
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS status Theorem for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  fof(f8,conjecture,(
% 2.16/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f9,negated_conjecture,(
% 2.16/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.16/1.00    inference(negated_conjecture,[],[f8])).
% 2.16/1.00  
% 2.16/1.00  fof(f19,plain,(
% 2.16/1.00    ? [X0,X1,X2,X3] : (? [X4] : ((((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & (k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.16/1.00    inference(ennf_transformation,[],[f9])).
% 2.16/1.00  
% 2.16/1.00  fof(f20,plain,(
% 2.16/1.00    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.16/1.00    inference(flattening,[],[f19])).
% 2.16/1.00  
% 2.16/1.00  fof(f23,plain,(
% 2.16/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((~v2_funct_1(sK4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f22,plain,(
% 2.16/1.00    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(sK3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & k2_relset_1(sK0,sK1,sK3) = sK1 & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f24,plain,(
% 2.16/1.00    ((~v2_funct_1(sK4) | ~v2_funct_1(sK3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & k2_relset_1(sK0,sK1,sK3) = sK1 & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f23,f22])).
% 2.16/1.00  
% 2.16/1.00  fof(f40,plain,(
% 2.16/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f5,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f14,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.00    inference(ennf_transformation,[],[f5])).
% 2.16/1.00  
% 2.16/1.00  fof(f30,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f14])).
% 2.16/1.00  
% 2.16/1.00  fof(f45,plain,(
% 2.16/1.00    k2_relset_1(sK0,sK1,sK3) = sK1),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f6,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f15,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.00    inference(ennf_transformation,[],[f6])).
% 2.16/1.00  
% 2.16/1.00  fof(f16,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.00    inference(flattening,[],[f15])).
% 2.16/1.00  
% 2.16/1.00  fof(f21,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.00    inference(nnf_transformation,[],[f16])).
% 2.16/1.00  
% 2.16/1.00  fof(f31,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f21])).
% 2.16/1.00  
% 2.16/1.00  fof(f42,plain,(
% 2.16/1.00    v1_funct_2(sK4,sK1,sK2)),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f43,plain,(
% 2.16/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f4,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f13,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.00    inference(ennf_transformation,[],[f4])).
% 2.16/1.00  
% 2.16/1.00  fof(f29,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f13])).
% 2.16/1.00  
% 2.16/1.00  fof(f3,axiom,(
% 2.16/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f11,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f3])).
% 2.16/1.00  
% 2.16/1.00  fof(f12,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.00    inference(flattening,[],[f11])).
% 2.16/1.00  
% 2.16/1.00  fof(f27,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f12])).
% 2.16/1.00  
% 2.16/1.00  fof(f41,plain,(
% 2.16/1.00    v1_funct_1(sK4)),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f1,axiom,(
% 2.16/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f10,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.16/1.00    inference(ennf_transformation,[],[f1])).
% 2.16/1.00  
% 2.16/1.00  fof(f25,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f10])).
% 2.16/1.00  
% 2.16/1.00  fof(f2,axiom,(
% 2.16/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f26,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f2])).
% 2.16/1.00  
% 2.16/1.00  fof(f38,plain,(
% 2.16/1.00    v1_funct_1(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f47,plain,(
% 2.16/1.00    ~v2_funct_1(sK4) | ~v2_funct_1(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f7,axiom,(
% 2.16/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f17,plain,(
% 2.16/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.16/1.00    inference(ennf_transformation,[],[f7])).
% 2.16/1.00  
% 2.16/1.00  fof(f18,plain,(
% 2.16/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.16/1.00    inference(flattening,[],[f17])).
% 2.16/1.00  
% 2.16/1.00  fof(f37,plain,(
% 2.16/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f18])).
% 2.16/1.00  
% 2.16/1.00  fof(f44,plain,(
% 2.16/1.00    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f28,plain,(
% 2.16/1.00    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f12])).
% 2.16/1.00  
% 2.16/1.00  fof(f46,plain,(
% 2.16/1.00    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f32,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f21])).
% 2.16/1.00  
% 2.16/1.00  fof(f52,plain,(
% 2.16/1.00    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.16/1.00    inference(equality_resolution,[],[f32])).
% 2.16/1.00  
% 2.16/1.00  cnf(c_20,negated_conjecture,
% 2.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.16/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_471,negated_conjecture,
% 2.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_825,plain,
% 2.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_5,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_479,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.16/1.00      | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_819,plain,
% 2.16/1.00      ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
% 2.16/1.00      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1198,plain,
% 2.16/1.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_825,c_819]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_15,negated_conjecture,
% 2.16/1.00      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 2.16/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_475,negated_conjecture,
% 2.16/1.00      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1200,plain,
% 2.16/1.00      ( k2_relat_1(sK3) = sK1 ),
% 2.16/1.00      inference(light_normalisation,[status(thm)],[c_1198,c_475]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_11,plain,
% 2.16/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.16/1.00      | k1_xboole_0 = X2 ),
% 2.16/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_18,negated_conjecture,
% 2.16/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.16/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_303,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.16/1.00      | sK2 != X2
% 2.16/1.00      | sK1 != X1
% 2.16/1.00      | sK4 != X0
% 2.16/1.00      | k1_xboole_0 = X2 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_304,plain,
% 2.16/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.16/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.16/1.00      | k1_xboole_0 = sK2 ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_303]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_17,negated_conjecture,
% 2.16/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.16/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_306,plain,
% 2.16/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_304,c_17]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_465,plain,
% 2.16/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_306]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_473,negated_conjecture,
% 2.16/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_823,plain,
% 2.16/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_4,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_480,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.16/1.00      | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_818,plain,
% 2.16/1.00      ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
% 2.16/1.00      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1188,plain,
% 2.16/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_823,c_818]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1261,plain,
% 2.16/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_465,c_1188]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0)
% 2.16/1.00      | ~ v1_funct_1(X1)
% 2.16/1.00      | v2_funct_1(X0)
% 2.16/1.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.16/1.00      | ~ v1_relat_1(X1)
% 2.16/1.00      | ~ v1_relat_1(X0)
% 2.16/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f27]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_481,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0_47)
% 2.16/1.00      | ~ v1_funct_1(X1_47)
% 2.16/1.00      | v2_funct_1(X0_47)
% 2.16/1.00      | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
% 2.16/1.00      | ~ v1_relat_1(X1_47)
% 2.16/1.00      | ~ v1_relat_1(X0_47)
% 2.16/1.00      | k1_relat_1(X1_47) != k2_relat_1(X0_47) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_817,plain,
% 2.16/1.00      ( k1_relat_1(X0_47) != k2_relat_1(X1_47)
% 2.16/1.00      | v1_funct_1(X0_47) != iProver_top
% 2.16/1.00      | v1_funct_1(X1_47) != iProver_top
% 2.16/1.00      | v2_funct_1(X1_47) = iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(X1_47,X0_47)) != iProver_top
% 2.16/1.00      | v1_relat_1(X1_47) != iProver_top
% 2.16/1.00      | v1_relat_1(X0_47) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1528,plain,
% 2.16/1.00      ( k2_relat_1(X0_47) != sK1
% 2.16/1.00      | sK2 = k1_xboole_0
% 2.16/1.00      | v1_funct_1(X0_47) != iProver_top
% 2.16/1.00      | v1_funct_1(sK4) != iProver_top
% 2.16/1.00      | v2_funct_1(X0_47) = iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
% 2.16/1.00      | v1_relat_1(X0_47) != iProver_top
% 2.16/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_1261,c_817]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_19,negated_conjecture,
% 2.16/1.00      ( v1_funct_1(sK4) ),
% 2.16/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_26,plain,
% 2.16/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_28,plain,
% 2.16/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_0,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.16/1.00      | ~ v1_relat_1(X1)
% 2.16/1.00      | v1_relat_1(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f25]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_484,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 2.16/1.00      | ~ v1_relat_1(X1_47)
% 2.16/1.00      | v1_relat_1(X0_47) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_982,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.16/1.00      | v1_relat_1(X0_47)
% 2.16/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1_47,X2_47)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_484]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1153,plain,
% 2.16/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.16/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.16/1.00      | v1_relat_1(sK4) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_982]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1154,plain,
% 2.16/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.16/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.16/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1,plain,
% 2.16/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.16/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_483,plain,
% 2.16/1.00      ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1242,plain,
% 2.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1243,plain,
% 2.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2328,plain,
% 2.16/1.00      ( v1_relat_1(X0_47) != iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
% 2.16/1.00      | v2_funct_1(X0_47) = iProver_top
% 2.16/1.00      | k2_relat_1(X0_47) != sK1
% 2.16/1.00      | sK2 = k1_xboole_0
% 2.16/1.00      | v1_funct_1(X0_47) != iProver_top ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1528,c_26,c_28,c_1154,c_1243]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2329,plain,
% 2.16/1.00      ( k2_relat_1(X0_47) != sK1
% 2.16/1.00      | sK2 = k1_xboole_0
% 2.16/1.00      | v1_funct_1(X0_47) != iProver_top
% 2.16/1.00      | v2_funct_1(X0_47) = iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
% 2.16/1.00      | v1_relat_1(X0_47) != iProver_top ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_2328]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2340,plain,
% 2.16/1.00      ( sK2 = k1_xboole_0
% 2.16/1.00      | v1_funct_1(sK3) != iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 2.16/1.00      | v2_funct_1(sK3) = iProver_top
% 2.16/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_1200,c_2329]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_22,negated_conjecture,
% 2.16/1.00      ( v1_funct_1(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_23,plain,
% 2.16/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_25,plain,
% 2.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_13,negated_conjecture,
% 2.16/1.00      ( ~ v2_funct_1(sK3) | ~ v2_funct_1(sK4) ),
% 2.16/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_30,plain,
% 2.16/1.00      ( v2_funct_1(sK3) != iProver_top | v2_funct_1(sK4) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1156,plain,
% 2.16/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.16/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.16/1.00      | v1_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_982]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1157,plain,
% 2.16/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.16/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.16/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1245,plain,
% 2.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1246,plain,
% 2.16/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_12,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.16/1.00      | ~ v1_funct_1(X0)
% 2.16/1.00      | ~ v1_funct_1(X3)
% 2.16/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_478,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.16/1.00      | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
% 2.16/1.00      | ~ v1_funct_1(X0_47)
% 2.16/1.00      | ~ v1_funct_1(X3_47)
% 2.16/1.00      | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_820,plain,
% 2.16/1.00      ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X4_47,X5_47) = k5_relat_1(X4_47,X5_47)
% 2.16/1.00      | m1_subset_1(X5_47,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
% 2.16/1.00      | m1_subset_1(X4_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.16/1.00      | v1_funct_1(X5_47) != iProver_top
% 2.16/1.00      | v1_funct_1(X4_47) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1606,plain,
% 2.16/1.00      ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
% 2.16/1.00      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.16/1.00      | v1_funct_1(X2_47) != iProver_top
% 2.16/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_823,c_820]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1682,plain,
% 2.16/1.00      ( v1_funct_1(X2_47) != iProver_top
% 2.16/1.00      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.16/1.00      | k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1606,c_26]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1683,plain,
% 2.16/1.00      ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
% 2.16/1.00      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.16/1.00      | v1_funct_1(X2_47) != iProver_top ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1682]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1692,plain,
% 2.16/1.00      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 2.16/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_825,c_1683]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1059,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.16/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_47,X4_47)))
% 2.16/1.00      | ~ v1_funct_1(X0_47)
% 2.16/1.00      | ~ v1_funct_1(sK4)
% 2.16/1.00      | k1_partfun1(X1_47,X2_47,X3_47,X4_47,X0_47,sK4) = k5_relat_1(X0_47,sK4) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_478]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1109,plain,
% 2.16/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.16/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_funct_1(sK4)
% 2.16/1.00      | k1_partfun1(X0_47,X1_47,X2_47,X3_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1059]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1143,plain,
% 2.16/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.16/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_funct_1(sK4)
% 2.16/1.00      | k1_partfun1(sK0,sK1,X0_47,X1_47,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1109]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1251,plain,
% 2.16/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.16/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_funct_1(sK4)
% 2.16/1.00      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1143]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1758,plain,
% 2.16/1.00      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1692,c_22,c_20,c_19,c_17,c_1251]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_16,negated_conjecture,
% 2.16/1.00      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 2.16/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_474,negated_conjecture,
% 2.16/1.00      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_822,plain,
% 2.16/1.00      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1761,plain,
% 2.16/1.00      ( v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_1758,c_822]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0)
% 2.16/1.00      | ~ v1_funct_1(X1)
% 2.16/1.00      | v2_funct_1(X1)
% 2.16/1.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.16/1.00      | ~ v1_relat_1(X1)
% 2.16/1.00      | ~ v1_relat_1(X0)
% 2.16/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_482,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0_47)
% 2.16/1.00      | ~ v1_funct_1(X1_47)
% 2.16/1.00      | v2_funct_1(X1_47)
% 2.16/1.00      | ~ v2_funct_1(k5_relat_1(X0_47,X1_47))
% 2.16/1.00      | ~ v1_relat_1(X1_47)
% 2.16/1.00      | ~ v1_relat_1(X0_47)
% 2.16/1.00      | k1_relat_1(X1_47) != k2_relat_1(X0_47) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_816,plain,
% 2.16/1.00      ( k1_relat_1(X0_47) != k2_relat_1(X1_47)
% 2.16/1.00      | v1_funct_1(X0_47) != iProver_top
% 2.16/1.00      | v1_funct_1(X1_47) != iProver_top
% 2.16/1.00      | v2_funct_1(X0_47) = iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(X1_47,X0_47)) != iProver_top
% 2.16/1.00      | v1_relat_1(X1_47) != iProver_top
% 2.16/1.00      | v1_relat_1(X0_47) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1480,plain,
% 2.16/1.00      ( k2_relat_1(X0_47) != sK1
% 2.16/1.00      | sK2 = k1_xboole_0
% 2.16/1.00      | v1_funct_1(X0_47) != iProver_top
% 2.16/1.00      | v1_funct_1(sK4) != iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
% 2.16/1.00      | v2_funct_1(sK4) = iProver_top
% 2.16/1.00      | v1_relat_1(X0_47) != iProver_top
% 2.16/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_1261,c_816]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1952,plain,
% 2.16/1.00      ( v1_relat_1(X0_47) != iProver_top
% 2.16/1.00      | v2_funct_1(sK4) = iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
% 2.16/1.00      | k2_relat_1(X0_47) != sK1
% 2.16/1.00      | sK2 = k1_xboole_0
% 2.16/1.00      | v1_funct_1(X0_47) != iProver_top ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1480,c_26,c_28,c_1154,c_1243]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1953,plain,
% 2.16/1.00      ( k2_relat_1(X0_47) != sK1
% 2.16/1.00      | sK2 = k1_xboole_0
% 2.16/1.00      | v1_funct_1(X0_47) != iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(X0_47,sK4)) != iProver_top
% 2.16/1.00      | v2_funct_1(sK4) = iProver_top
% 2.16/1.00      | v1_relat_1(X0_47) != iProver_top ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1952]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1964,plain,
% 2.16/1.00      ( sK2 = k1_xboole_0
% 2.16/1.00      | v1_funct_1(sK3) != iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 2.16/1.00      | v2_funct_1(sK4) = iProver_top
% 2.16/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_1200,c_1953]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2041,plain,
% 2.16/1.00      ( v2_funct_1(sK4) = iProver_top | sK2 = k1_xboole_0 ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1964,c_23,c_25,c_1157,c_1246,c_1761]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2042,plain,
% 2.16/1.00      ( sK2 = k1_xboole_0 | v2_funct_1(sK4) = iProver_top ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_2041]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2343,plain,
% 2.16/1.00      ( sK2 = k1_xboole_0 ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_2340,c_23,c_25,c_30,c_1157,c_1246,c_1761,c_2042]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_14,negated_conjecture,
% 2.16/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.16/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_476,negated_conjecture,
% 2.16/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2358,plain,
% 2.16/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_2343,c_476]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2359,plain,
% 2.16/1.00      ( sK1 = k1_xboole_0 ),
% 2.16/1.00      inference(equality_resolution_simp,[status(thm)],[c_2358]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2478,plain,
% 2.16/1.00      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_2359,c_1200]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_10,plain,
% 2.16/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.16/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.16/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_277,plain,
% 2.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.16/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.16/1.00      | sK2 != X1
% 2.16/1.00      | sK1 != k1_xboole_0
% 2.16/1.00      | sK4 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_278,plain,
% 2.16/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.16/1.00      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.16/1.00      | sK1 != k1_xboole_0 ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_277]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_467,plain,
% 2.16/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.16/1.00      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.16/1.00      | sK1 != k1_xboole_0 ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_278]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_829,plain,
% 2.16/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.16/1.00      | sK1 != k1_xboole_0
% 2.16/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2353,plain,
% 2.16/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.16/1.00      | sK1 != k1_xboole_0
% 2.16/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_2343,c_829]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2371,plain,
% 2.16/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.16/1.00      | k1_xboole_0 != k1_xboole_0
% 2.16/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.16/1.00      inference(light_normalisation,[status(thm)],[c_2353,c_2359]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2372,plain,
% 2.16/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.16/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.16/1.00      inference(equality_resolution_simp,[status(thm)],[c_2371]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2355,plain,
% 2.16/1.00      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_2343,c_1188]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2365,plain,
% 2.16/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.16/1.00      inference(light_normalisation,[status(thm)],[c_2355,c_2359]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2373,plain,
% 2.16/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 2.16/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_2372,c_2365]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2357,plain,
% 2.16/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_2343,c_823]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2362,plain,
% 2.16/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.16/1.00      inference(light_normalisation,[status(thm)],[c_2357,c_2359]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2376,plain,
% 2.16/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.16/1.00      inference(forward_subsumption_resolution,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_2373,c_2362]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_488,plain,
% 2.16/1.00      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.16/1.00      theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1943,plain,
% 2.16/1.00      ( k1_relat_1(sK4) != X0_47
% 2.16/1.00      | k1_relat_1(sK4) = k2_relat_1(sK3)
% 2.16/1.00      | k2_relat_1(sK3) != X0_47 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_488]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1944,plain,
% 2.16/1.00      ( k1_relat_1(sK4) = k2_relat_1(sK3)
% 2.16/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 2.16/1.00      | k2_relat_1(sK3) != k1_xboole_0 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1943]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1050,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0_47)
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | v2_funct_1(X0_47)
% 2.16/1.00      | ~ v2_funct_1(k5_relat_1(sK3,X0_47))
% 2.16/1.00      | ~ v1_relat_1(X0_47)
% 2.16/1.00      | ~ v1_relat_1(sK3)
% 2.16/1.00      | k1_relat_1(X0_47) != k2_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_482]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1423,plain,
% 2.16/1.00      ( ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_funct_1(sK4)
% 2.16/1.00      | ~ v2_funct_1(k5_relat_1(sK3,sK4))
% 2.16/1.00      | v2_funct_1(sK4)
% 2.16/1.00      | ~ v1_relat_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(sK4)
% 2.16/1.00      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1050]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1424,plain,
% 2.16/1.00      ( k1_relat_1(sK4) != k2_relat_1(sK3)
% 2.16/1.00      | v1_funct_1(sK3) != iProver_top
% 2.16/1.00      | v1_funct_1(sK4) != iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 2.16/1.00      | v2_funct_1(sK4) = iProver_top
% 2.16/1.00      | v1_relat_1(sK3) != iProver_top
% 2.16/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1423]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1040,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0_47)
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v2_funct_1(k5_relat_1(sK3,X0_47))
% 2.16/1.00      | v2_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(X0_47)
% 2.16/1.00      | ~ v1_relat_1(sK3)
% 2.16/1.00      | k1_relat_1(X0_47) != k2_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_481]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1417,plain,
% 2.16/1.00      ( ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_funct_1(sK4)
% 2.16/1.00      | ~ v2_funct_1(k5_relat_1(sK3,sK4))
% 2.16/1.00      | v2_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(sK4)
% 2.16/1.00      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1040]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1418,plain,
% 2.16/1.00      ( k1_relat_1(sK4) != k2_relat_1(sK3)
% 2.16/1.00      | v1_funct_1(sK3) != iProver_top
% 2.16/1.00      | v1_funct_1(sK4) != iProver_top
% 2.16/1.00      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 2.16/1.00      | v2_funct_1(sK3) = iProver_top
% 2.16/1.00      | v1_relat_1(sK3) != iProver_top
% 2.16/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1417]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(contradiction,plain,
% 2.16/1.00      ( $false ),
% 2.16/1.00      inference(minisat,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_2478,c_2376,c_1944,c_1761,c_1424,c_1418,c_1246,c_1243,
% 2.16/1.00                 c_1157,c_1154,c_30,c_28,c_26,c_25,c_23]) ).
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  ------                               Statistics
% 2.16/1.00  
% 2.16/1.00  ------ General
% 2.16/1.00  
% 2.16/1.00  abstr_ref_over_cycles:                  0
% 2.16/1.00  abstr_ref_under_cycles:                 0
% 2.16/1.00  gc_basic_clause_elim:                   0
% 2.16/1.00  forced_gc_time:                         0
% 2.16/1.00  parsing_time:                           0.009
% 2.16/1.00  unif_index_cands_time:                  0.
% 2.16/1.00  unif_index_add_time:                    0.
% 2.16/1.00  orderings_time:                         0.
% 2.16/1.00  out_proof_time:                         0.012
% 2.16/1.00  total_time:                             0.116
% 2.16/1.00  num_of_symbols:                         52
% 2.16/1.00  num_of_terms:                           2160
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing
% 2.16/1.00  
% 2.16/1.00  num_of_splits:                          0
% 2.16/1.00  num_of_split_atoms:                     0
% 2.16/1.00  num_of_reused_defs:                     0
% 2.16/1.00  num_eq_ax_congr_red:                    14
% 2.16/1.00  num_of_sem_filtered_clauses:            1
% 2.16/1.00  num_of_subtypes:                        2
% 2.16/1.00  monotx_restored_types:                  0
% 2.16/1.00  sat_num_of_epr_types:                   0
% 2.16/1.00  sat_num_of_non_cyclic_types:            0
% 2.16/1.00  sat_guarded_non_collapsed_types:        0
% 2.16/1.00  num_pure_diseq_elim:                    0
% 2.16/1.00  simp_replaced_by:                       0
% 2.16/1.00  res_preprocessed:                       111
% 2.16/1.00  prep_upred:                             0
% 2.16/1.00  prep_unflattend:                        34
% 2.16/1.00  smt_new_axioms:                         0
% 2.16/1.00  pred_elim_cands:                        4
% 2.16/1.00  pred_elim:                              1
% 2.16/1.00  pred_elim_cl:                           2
% 2.16/1.00  pred_elim_cycles:                       3
% 2.16/1.00  merged_defs:                            0
% 2.16/1.00  merged_defs_ncl:                        0
% 2.16/1.00  bin_hyper_res:                          0
% 2.16/1.00  prep_cycles:                            4
% 2.16/1.00  pred_elim_time:                         0.003
% 2.16/1.00  splitting_time:                         0.
% 2.16/1.00  sem_filter_time:                        0.
% 2.16/1.00  monotx_time:                            0.
% 2.16/1.00  subtype_inf_time:                       0.
% 2.16/1.00  
% 2.16/1.00  ------ Problem properties
% 2.16/1.00  
% 2.16/1.00  clauses:                                21
% 2.16/1.00  conjectures:                            8
% 2.16/1.00  epr:                                    4
% 2.16/1.00  horn:                                   17
% 2.16/1.00  ground:                                 14
% 2.16/1.00  unary:                                  7
% 2.16/1.00  binary:                                 6
% 2.16/1.00  lits:                                   55
% 2.16/1.00  lits_eq:                                22
% 2.16/1.00  fd_pure:                                0
% 2.16/1.00  fd_pseudo:                              0
% 2.16/1.00  fd_cond:                                0
% 2.16/1.00  fd_pseudo_cond:                         0
% 2.16/1.00  ac_symbols:                             0
% 2.16/1.00  
% 2.16/1.00  ------ Propositional Solver
% 2.16/1.00  
% 2.16/1.00  prop_solver_calls:                      30
% 2.16/1.00  prop_fast_solver_calls:                 789
% 2.16/1.00  smt_solver_calls:                       0
% 2.16/1.00  smt_fast_solver_calls:                  0
% 2.16/1.00  prop_num_of_clauses:                    775
% 2.16/1.00  prop_preprocess_simplified:             2983
% 2.16/1.00  prop_fo_subsumed:                       28
% 2.16/1.00  prop_solver_time:                       0.
% 2.16/1.00  smt_solver_time:                        0.
% 2.16/1.00  smt_fast_solver_time:                   0.
% 2.16/1.00  prop_fast_solver_time:                  0.
% 2.16/1.00  prop_unsat_core_time:                   0.
% 2.16/1.00  
% 2.16/1.00  ------ QBF
% 2.16/1.00  
% 2.16/1.00  qbf_q_res:                              0
% 2.16/1.00  qbf_num_tautologies:                    0
% 2.16/1.00  qbf_prep_cycles:                        0
% 2.16/1.00  
% 2.16/1.00  ------ BMC1
% 2.16/1.00  
% 2.16/1.00  bmc1_current_bound:                     -1
% 2.16/1.00  bmc1_last_solved_bound:                 -1
% 2.16/1.00  bmc1_unsat_core_size:                   -1
% 2.16/1.00  bmc1_unsat_core_parents_size:           -1
% 2.16/1.00  bmc1_merge_next_fun:                    0
% 2.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation
% 2.16/1.00  
% 2.16/1.00  inst_num_of_clauses:                    285
% 2.16/1.00  inst_num_in_passive:                    99
% 2.16/1.00  inst_num_in_active:                     186
% 2.16/1.00  inst_num_in_unprocessed:                0
% 2.16/1.00  inst_num_of_loops:                      220
% 2.16/1.00  inst_num_of_learning_restarts:          0
% 2.16/1.00  inst_num_moves_active_passive:          28
% 2.16/1.00  inst_lit_activity:                      0
% 2.16/1.00  inst_lit_activity_moves:                0
% 2.16/1.00  inst_num_tautologies:                   0
% 2.16/1.00  inst_num_prop_implied:                  0
% 2.16/1.00  inst_num_existing_simplified:           0
% 2.16/1.00  inst_num_eq_res_simplified:             0
% 2.16/1.00  inst_num_child_elim:                    0
% 2.16/1.00  inst_num_of_dismatching_blockings:      89
% 2.16/1.00  inst_num_of_non_proper_insts:           293
% 2.16/1.00  inst_num_of_duplicates:                 0
% 2.16/1.00  inst_inst_num_from_inst_to_res:         0
% 2.16/1.00  inst_dismatching_checking_time:         0.
% 2.16/1.00  
% 2.16/1.00  ------ Resolution
% 2.16/1.00  
% 2.16/1.00  res_num_of_clauses:                     0
% 2.16/1.00  res_num_in_passive:                     0
% 2.16/1.00  res_num_in_active:                      0
% 2.16/1.00  res_num_of_loops:                       115
% 2.16/1.00  res_forward_subset_subsumed:            55
% 2.16/1.00  res_backward_subset_subsumed:           0
% 2.16/1.00  res_forward_subsumed:                   0
% 2.16/1.00  res_backward_subsumed:                  0
% 2.16/1.00  res_forward_subsumption_resolution:     0
% 2.16/1.00  res_backward_subsumption_resolution:    0
% 2.16/1.00  res_clause_to_clause_subsumption:       75
% 2.16/1.00  res_orphan_elimination:                 0
% 2.16/1.00  res_tautology_del:                      57
% 2.16/1.00  res_num_eq_res_simplified:              0
% 2.16/1.00  res_num_sel_changes:                    0
% 2.16/1.00  res_moves_from_active_to_pass:          0
% 2.16/1.00  
% 2.16/1.00  ------ Superposition
% 2.16/1.00  
% 2.16/1.00  sup_time_total:                         0.
% 2.16/1.00  sup_time_generating:                    0.
% 2.16/1.00  sup_time_sim_full:                      0.
% 2.16/1.00  sup_time_sim_immed:                     0.
% 2.16/1.00  
% 2.16/1.00  sup_num_of_clauses:                     30
% 2.16/1.00  sup_num_in_active:                      15
% 2.16/1.00  sup_num_in_passive:                     15
% 2.16/1.00  sup_num_of_loops:                       42
% 2.16/1.00  sup_fw_superposition:                   21
% 2.16/1.00  sup_bw_superposition:                   2
% 2.16/1.00  sup_immediate_simplified:               11
% 2.16/1.00  sup_given_eliminated:                   0
% 2.16/1.00  comparisons_done:                       0
% 2.16/1.00  comparisons_avoided:                    8
% 2.16/1.00  
% 2.16/1.00  ------ Simplifications
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  sim_fw_subset_subsumed:                 2
% 2.16/1.00  sim_bw_subset_subsumed:                 1
% 2.16/1.00  sim_fw_subsumed:                        0
% 2.16/1.00  sim_bw_subsumed:                        0
% 2.16/1.00  sim_fw_subsumption_res:                 2
% 2.16/1.00  sim_bw_subsumption_res:                 0
% 2.16/1.00  sim_tautology_del:                      0
% 2.16/1.00  sim_eq_tautology_del:                   6
% 2.16/1.00  sim_eq_res_simp:                        4
% 2.16/1.00  sim_fw_demodulated:                     1
% 2.16/1.00  sim_bw_demodulated:                     27
% 2.16/1.00  sim_light_normalised:                   9
% 2.16/1.00  sim_joinable_taut:                      0
% 2.16/1.00  sim_joinable_simp:                      0
% 2.16/1.00  sim_ac_normalised:                      0
% 2.16/1.00  sim_smt_subsumption:                    0
% 2.16/1.00  
%------------------------------------------------------------------------------
