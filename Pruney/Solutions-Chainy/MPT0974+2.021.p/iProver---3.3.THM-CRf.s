%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:21 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 438 expanded)
%              Number of clauses        :   84 ( 163 expanded)
%              Number of leaves         :   12 ( 100 expanded)
%              Depth                    :   18
%              Number of atoms          :  383 (2804 expanded)
%              Number of equality atoms :  190 (1192 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f27,f26])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_477,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_824,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_479,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_822,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47)
    | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_821,plain,
    ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X4_47,X5_47) = k5_relat_1(X4_47,X5_47)
    | m1_subset_1(X5_47,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(X4_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X5_47) != iProver_top
    | v1_funct_1(X4_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_2674,plain,
    ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_821])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2841,plain,
    ( v1_funct_1(X2_47) != iProver_top
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2674,c_28])).

cnf(c_2842,plain,
    ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2841])).

cnf(c_2851,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_824,c_2842])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2902,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2851,c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | m1_subset_1(k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X4_47,X2_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_819,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X4_47,X2_47))) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X3_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_2907,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2902,c_819])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3678,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2907,c_25,c_27,c_28,c_30])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_818,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_3687,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_3678,c_818])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ v1_relat_1(X1_47)
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_813,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_1746,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_813])).

cnf(c_980,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47)
    | ~ v1_relat_1(k2_zfmisc_1(X1_47,X2_47)) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_1179,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1178])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_491,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1725,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_1726,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1725])).

cnf(c_1858,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1746,c_30,c_1179,c_1726])).

cnf(c_1747,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_824,c_813])).

cnf(c_1181,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_1182,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1181])).

cnf(c_1728,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_1729,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1728])).

cnf(c_1878,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1747,c_27,c_1182,c_1729])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_489,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | k2_relat_1(k5_relat_1(X0_47,X1_47)) = k9_relat_1(X1_47,k2_relat_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_816,plain,
    ( k2_relat_1(k5_relat_1(X0_47,X1_47)) = k9_relat_1(X1_47,k2_relat_1(X0_47))
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_1883,plain,
    ( k2_relat_1(k5_relat_1(sK3,X0_47)) = k9_relat_1(X0_47,k2_relat_1(sK3))
    | v1_relat_1(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_816])).

cnf(c_1767,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_824,c_818])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_480,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1769,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1767,c_480])).

cnf(c_1890,plain,
    ( k2_relat_1(k5_relat_1(sK3,X0_47)) = k9_relat_1(X0_47,sK1)
    | v1_relat_1(X0_47) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1883,c_1769])).

cnf(c_1918,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1858,c_1890])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_490,plain,
    ( ~ v1_relat_1(X0_47)
    | k9_relat_1(X0_47,k1_relat_1(X0_47)) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_815,plain,
    ( k9_relat_1(X0_47,k1_relat_1(X0_47)) = k2_relat_1(X0_47)
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_1864,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1858,c_815])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_817,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_1279,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_822,c_817])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK1 != X1
    | sK2 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_313,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_315,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_19,c_16])).

cnf(c_471,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_1284,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1279,c_471])).

cnf(c_1766,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_822,c_818])).

cnf(c_17,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_481,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1772,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1766,c_481])).

cnf(c_1866,plain,
    ( k9_relat_1(sK4,sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1864,c_1284,c_1772])).

cnf(c_1923,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1918,c_1866])).

cnf(c_3692,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3687,c_1923])).

cnf(c_15,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_483,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2905,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2 ),
    inference(demodulation,[status(thm)],[c_2902,c_483])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3692,c_2905])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.17/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.01  
% 3.17/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/1.01  
% 3.17/1.01  ------  iProver source info
% 3.17/1.01  
% 3.17/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.17/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/1.01  git: non_committed_changes: false
% 3.17/1.01  git: last_make_outside_of_git: false
% 3.17/1.01  
% 3.17/1.01  ------ 
% 3.17/1.01  
% 3.17/1.01  ------ Input Options
% 3.17/1.01  
% 3.17/1.01  --out_options                           all
% 3.17/1.01  --tptp_safe_out                         true
% 3.17/1.01  --problem_path                          ""
% 3.17/1.01  --include_path                          ""
% 3.17/1.01  --clausifier                            res/vclausify_rel
% 3.17/1.01  --clausifier_options                    --mode clausify
% 3.17/1.01  --stdin                                 false
% 3.17/1.01  --stats_out                             all
% 3.17/1.01  
% 3.17/1.01  ------ General Options
% 3.17/1.01  
% 3.17/1.01  --fof                                   false
% 3.17/1.01  --time_out_real                         305.
% 3.17/1.01  --time_out_virtual                      -1.
% 3.17/1.01  --symbol_type_check                     false
% 3.17/1.01  --clausify_out                          false
% 3.17/1.01  --sig_cnt_out                           false
% 3.17/1.01  --trig_cnt_out                          false
% 3.17/1.01  --trig_cnt_out_tolerance                1.
% 3.17/1.01  --trig_cnt_out_sk_spl                   false
% 3.17/1.01  --abstr_cl_out                          false
% 3.17/1.01  
% 3.17/1.01  ------ Global Options
% 3.17/1.01  
% 3.17/1.01  --schedule                              default
% 3.17/1.01  --add_important_lit                     false
% 3.17/1.01  --prop_solver_per_cl                    1000
% 3.17/1.01  --min_unsat_core                        false
% 3.17/1.01  --soft_assumptions                      false
% 3.17/1.01  --soft_lemma_size                       3
% 3.17/1.01  --prop_impl_unit_size                   0
% 3.17/1.01  --prop_impl_unit                        []
% 3.17/1.01  --share_sel_clauses                     true
% 3.17/1.01  --reset_solvers                         false
% 3.17/1.01  --bc_imp_inh                            [conj_cone]
% 3.17/1.01  --conj_cone_tolerance                   3.
% 3.17/1.01  --extra_neg_conj                        none
% 3.17/1.01  --large_theory_mode                     true
% 3.17/1.01  --prolific_symb_bound                   200
% 3.17/1.01  --lt_threshold                          2000
% 3.17/1.01  --clause_weak_htbl                      true
% 3.17/1.01  --gc_record_bc_elim                     false
% 3.17/1.01  
% 3.17/1.01  ------ Preprocessing Options
% 3.17/1.01  
% 3.17/1.01  --preprocessing_flag                    true
% 3.17/1.01  --time_out_prep_mult                    0.1
% 3.17/1.01  --splitting_mode                        input
% 3.17/1.01  --splitting_grd                         true
% 3.17/1.01  --splitting_cvd                         false
% 3.17/1.01  --splitting_cvd_svl                     false
% 3.17/1.01  --splitting_nvd                         32
% 3.17/1.01  --sub_typing                            true
% 3.17/1.01  --prep_gs_sim                           true
% 3.17/1.01  --prep_unflatten                        true
% 3.17/1.01  --prep_res_sim                          true
% 3.17/1.01  --prep_upred                            true
% 3.17/1.01  --prep_sem_filter                       exhaustive
% 3.17/1.01  --prep_sem_filter_out                   false
% 3.17/1.01  --pred_elim                             true
% 3.17/1.01  --res_sim_input                         true
% 3.17/1.01  --eq_ax_congr_red                       true
% 3.17/1.01  --pure_diseq_elim                       true
% 3.17/1.01  --brand_transform                       false
% 3.17/1.01  --non_eq_to_eq                          false
% 3.17/1.01  --prep_def_merge                        true
% 3.17/1.01  --prep_def_merge_prop_impl              false
% 3.17/1.01  --prep_def_merge_mbd                    true
% 3.17/1.01  --prep_def_merge_tr_red                 false
% 3.17/1.01  --prep_def_merge_tr_cl                  false
% 3.17/1.01  --smt_preprocessing                     true
% 3.17/1.01  --smt_ac_axioms                         fast
% 3.17/1.01  --preprocessed_out                      false
% 3.17/1.01  --preprocessed_stats                    false
% 3.17/1.01  
% 3.17/1.01  ------ Abstraction refinement Options
% 3.17/1.01  
% 3.17/1.01  --abstr_ref                             []
% 3.17/1.01  --abstr_ref_prep                        false
% 3.17/1.01  --abstr_ref_until_sat                   false
% 3.17/1.01  --abstr_ref_sig_restrict                funpre
% 3.17/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/1.01  --abstr_ref_under                       []
% 3.17/1.01  
% 3.17/1.01  ------ SAT Options
% 3.17/1.01  
% 3.17/1.01  --sat_mode                              false
% 3.17/1.01  --sat_fm_restart_options                ""
% 3.17/1.01  --sat_gr_def                            false
% 3.17/1.01  --sat_epr_types                         true
% 3.17/1.01  --sat_non_cyclic_types                  false
% 3.17/1.01  --sat_finite_models                     false
% 3.17/1.01  --sat_fm_lemmas                         false
% 3.17/1.01  --sat_fm_prep                           false
% 3.17/1.01  --sat_fm_uc_incr                        true
% 3.17/1.01  --sat_out_model                         small
% 3.17/1.01  --sat_out_clauses                       false
% 3.17/1.01  
% 3.17/1.01  ------ QBF Options
% 3.17/1.01  
% 3.17/1.01  --qbf_mode                              false
% 3.17/1.01  --qbf_elim_univ                         false
% 3.17/1.01  --qbf_dom_inst                          none
% 3.17/1.01  --qbf_dom_pre_inst                      false
% 3.17/1.01  --qbf_sk_in                             false
% 3.17/1.01  --qbf_pred_elim                         true
% 3.17/1.01  --qbf_split                             512
% 3.17/1.01  
% 3.17/1.01  ------ BMC1 Options
% 3.17/1.01  
% 3.17/1.01  --bmc1_incremental                      false
% 3.17/1.01  --bmc1_axioms                           reachable_all
% 3.17/1.01  --bmc1_min_bound                        0
% 3.17/1.01  --bmc1_max_bound                        -1
% 3.17/1.01  --bmc1_max_bound_default                -1
% 3.17/1.01  --bmc1_symbol_reachability              true
% 3.17/1.01  --bmc1_property_lemmas                  false
% 3.17/1.01  --bmc1_k_induction                      false
% 3.17/1.01  --bmc1_non_equiv_states                 false
% 3.17/1.01  --bmc1_deadlock                         false
% 3.17/1.01  --bmc1_ucm                              false
% 3.17/1.01  --bmc1_add_unsat_core                   none
% 3.17/1.01  --bmc1_unsat_core_children              false
% 3.17/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/1.01  --bmc1_out_stat                         full
% 3.17/1.01  --bmc1_ground_init                      false
% 3.17/1.01  --bmc1_pre_inst_next_state              false
% 3.17/1.01  --bmc1_pre_inst_state                   false
% 3.17/1.01  --bmc1_pre_inst_reach_state             false
% 3.17/1.01  --bmc1_out_unsat_core                   false
% 3.17/1.01  --bmc1_aig_witness_out                  false
% 3.17/1.01  --bmc1_verbose                          false
% 3.17/1.01  --bmc1_dump_clauses_tptp                false
% 3.17/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.17/1.01  --bmc1_dump_file                        -
% 3.17/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.17/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.17/1.01  --bmc1_ucm_extend_mode                  1
% 3.17/1.01  --bmc1_ucm_init_mode                    2
% 3.17/1.01  --bmc1_ucm_cone_mode                    none
% 3.17/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.17/1.01  --bmc1_ucm_relax_model                  4
% 3.17/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.17/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/1.01  --bmc1_ucm_layered_model                none
% 3.17/1.01  --bmc1_ucm_max_lemma_size               10
% 3.17/1.01  
% 3.17/1.01  ------ AIG Options
% 3.17/1.01  
% 3.17/1.01  --aig_mode                              false
% 3.17/1.01  
% 3.17/1.01  ------ Instantiation Options
% 3.17/1.01  
% 3.17/1.01  --instantiation_flag                    true
% 3.17/1.01  --inst_sos_flag                         false
% 3.17/1.01  --inst_sos_phase                        true
% 3.17/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/1.01  --inst_lit_sel_side                     num_symb
% 3.17/1.01  --inst_solver_per_active                1400
% 3.17/1.01  --inst_solver_calls_frac                1.
% 3.17/1.01  --inst_passive_queue_type               priority_queues
% 3.17/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/1.01  --inst_passive_queues_freq              [25;2]
% 3.17/1.01  --inst_dismatching                      true
% 3.17/1.01  --inst_eager_unprocessed_to_passive     true
% 3.17/1.01  --inst_prop_sim_given                   true
% 3.17/1.01  --inst_prop_sim_new                     false
% 3.17/1.01  --inst_subs_new                         false
% 3.17/1.01  --inst_eq_res_simp                      false
% 3.17/1.01  --inst_subs_given                       false
% 3.17/1.01  --inst_orphan_elimination               true
% 3.17/1.01  --inst_learning_loop_flag               true
% 3.17/1.01  --inst_learning_start                   3000
% 3.17/1.01  --inst_learning_factor                  2
% 3.17/1.01  --inst_start_prop_sim_after_learn       3
% 3.17/1.01  --inst_sel_renew                        solver
% 3.17/1.01  --inst_lit_activity_flag                true
% 3.17/1.01  --inst_restr_to_given                   false
% 3.17/1.01  --inst_activity_threshold               500
% 3.17/1.01  --inst_out_proof                        true
% 3.17/1.01  
% 3.17/1.01  ------ Resolution Options
% 3.17/1.01  
% 3.17/1.01  --resolution_flag                       true
% 3.17/1.01  --res_lit_sel                           adaptive
% 3.17/1.01  --res_lit_sel_side                      none
% 3.17/1.01  --res_ordering                          kbo
% 3.17/1.01  --res_to_prop_solver                    active
% 3.17/1.01  --res_prop_simpl_new                    false
% 3.17/1.01  --res_prop_simpl_given                  true
% 3.17/1.01  --res_passive_queue_type                priority_queues
% 3.17/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/1.01  --res_passive_queues_freq               [15;5]
% 3.17/1.01  --res_forward_subs                      full
% 3.17/1.01  --res_backward_subs                     full
% 3.17/1.01  --res_forward_subs_resolution           true
% 3.17/1.01  --res_backward_subs_resolution          true
% 3.17/1.01  --res_orphan_elimination                true
% 3.17/1.01  --res_time_limit                        2.
% 3.17/1.01  --res_out_proof                         true
% 3.17/1.01  
% 3.17/1.01  ------ Superposition Options
% 3.17/1.01  
% 3.17/1.01  --superposition_flag                    true
% 3.17/1.01  --sup_passive_queue_type                priority_queues
% 3.17/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.17/1.01  --demod_completeness_check              fast
% 3.17/1.01  --demod_use_ground                      true
% 3.17/1.01  --sup_to_prop_solver                    passive
% 3.17/1.01  --sup_prop_simpl_new                    true
% 3.17/1.01  --sup_prop_simpl_given                  true
% 3.17/1.01  --sup_fun_splitting                     false
% 3.17/1.01  --sup_smt_interval                      50000
% 3.17/1.01  
% 3.17/1.01  ------ Superposition Simplification Setup
% 3.17/1.01  
% 3.17/1.01  --sup_indices_passive                   []
% 3.17/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.01  --sup_full_bw                           [BwDemod]
% 3.17/1.01  --sup_immed_triv                        [TrivRules]
% 3.17/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.01  --sup_immed_bw_main                     []
% 3.17/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.01  
% 3.17/1.01  ------ Combination Options
% 3.17/1.01  
% 3.17/1.01  --comb_res_mult                         3
% 3.17/1.01  --comb_sup_mult                         2
% 3.17/1.01  --comb_inst_mult                        10
% 3.17/1.01  
% 3.17/1.01  ------ Debug Options
% 3.17/1.01  
% 3.17/1.01  --dbg_backtrace                         false
% 3.17/1.01  --dbg_dump_prop_clauses                 false
% 3.17/1.01  --dbg_dump_prop_clauses_file            -
% 3.17/1.01  --dbg_out_stat                          false
% 3.17/1.01  ------ Parsing...
% 3.17/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/1.01  
% 3.17/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.17/1.01  
% 3.17/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/1.01  
% 3.17/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.17/1.01  ------ Proving...
% 3.17/1.01  ------ Problem Properties 
% 3.17/1.01  
% 3.17/1.01  
% 3.17/1.01  clauses                                 23
% 3.17/1.01  conjectures                             8
% 3.17/1.01  EPR                                     3
% 3.17/1.01  Horn                                    20
% 3.17/1.01  unary                                   10
% 3.17/1.01  binary                                  4
% 3.17/1.01  lits                                    53
% 3.17/1.01  lits eq                                 22
% 3.17/1.01  fd_pure                                 0
% 3.17/1.01  fd_pseudo                               0
% 3.17/1.01  fd_cond                                 0
% 3.17/1.01  fd_pseudo_cond                          0
% 3.17/1.01  AC symbols                              0
% 3.17/1.01  
% 3.17/1.01  ------ Schedule dynamic 5 is on 
% 3.17/1.01  
% 3.17/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.17/1.01  
% 3.17/1.01  
% 3.17/1.01  ------ 
% 3.17/1.01  Current options:
% 3.17/1.01  ------ 
% 3.17/1.01  
% 3.17/1.01  ------ Input Options
% 3.17/1.01  
% 3.17/1.01  --out_options                           all
% 3.17/1.01  --tptp_safe_out                         true
% 3.17/1.01  --problem_path                          ""
% 3.17/1.01  --include_path                          ""
% 3.17/1.01  --clausifier                            res/vclausify_rel
% 3.17/1.01  --clausifier_options                    --mode clausify
% 3.17/1.01  --stdin                                 false
% 3.17/1.01  --stats_out                             all
% 3.17/1.01  
% 3.17/1.01  ------ General Options
% 3.17/1.01  
% 3.17/1.01  --fof                                   false
% 3.17/1.01  --time_out_real                         305.
% 3.17/1.01  --time_out_virtual                      -1.
% 3.17/1.01  --symbol_type_check                     false
% 3.17/1.01  --clausify_out                          false
% 3.17/1.01  --sig_cnt_out                           false
% 3.17/1.01  --trig_cnt_out                          false
% 3.17/1.01  --trig_cnt_out_tolerance                1.
% 3.17/1.01  --trig_cnt_out_sk_spl                   false
% 3.17/1.01  --abstr_cl_out                          false
% 3.17/1.01  
% 3.17/1.01  ------ Global Options
% 3.17/1.01  
% 3.17/1.01  --schedule                              default
% 3.17/1.01  --add_important_lit                     false
% 3.17/1.01  --prop_solver_per_cl                    1000
% 3.17/1.01  --min_unsat_core                        false
% 3.17/1.01  --soft_assumptions                      false
% 3.17/1.01  --soft_lemma_size                       3
% 3.17/1.01  --prop_impl_unit_size                   0
% 3.17/1.01  --prop_impl_unit                        []
% 3.17/1.01  --share_sel_clauses                     true
% 3.17/1.01  --reset_solvers                         false
% 3.17/1.01  --bc_imp_inh                            [conj_cone]
% 3.17/1.01  --conj_cone_tolerance                   3.
% 3.17/1.01  --extra_neg_conj                        none
% 3.17/1.01  --large_theory_mode                     true
% 3.17/1.01  --prolific_symb_bound                   200
% 3.17/1.01  --lt_threshold                          2000
% 3.17/1.01  --clause_weak_htbl                      true
% 3.17/1.01  --gc_record_bc_elim                     false
% 3.17/1.01  
% 3.17/1.01  ------ Preprocessing Options
% 3.17/1.01  
% 3.17/1.01  --preprocessing_flag                    true
% 3.17/1.01  --time_out_prep_mult                    0.1
% 3.17/1.01  --splitting_mode                        input
% 3.17/1.01  --splitting_grd                         true
% 3.17/1.01  --splitting_cvd                         false
% 3.17/1.01  --splitting_cvd_svl                     false
% 3.17/1.01  --splitting_nvd                         32
% 3.17/1.01  --sub_typing                            true
% 3.17/1.01  --prep_gs_sim                           true
% 3.17/1.01  --prep_unflatten                        true
% 3.17/1.01  --prep_res_sim                          true
% 3.17/1.01  --prep_upred                            true
% 3.17/1.01  --prep_sem_filter                       exhaustive
% 3.17/1.01  --prep_sem_filter_out                   false
% 3.17/1.01  --pred_elim                             true
% 3.17/1.01  --res_sim_input                         true
% 3.17/1.01  --eq_ax_congr_red                       true
% 3.17/1.01  --pure_diseq_elim                       true
% 3.17/1.01  --brand_transform                       false
% 3.17/1.01  --non_eq_to_eq                          false
% 3.17/1.01  --prep_def_merge                        true
% 3.17/1.01  --prep_def_merge_prop_impl              false
% 3.17/1.01  --prep_def_merge_mbd                    true
% 3.17/1.01  --prep_def_merge_tr_red                 false
% 3.17/1.01  --prep_def_merge_tr_cl                  false
% 3.17/1.01  --smt_preprocessing                     true
% 3.17/1.01  --smt_ac_axioms                         fast
% 3.17/1.01  --preprocessed_out                      false
% 3.17/1.01  --preprocessed_stats                    false
% 3.17/1.01  
% 3.17/1.01  ------ Abstraction refinement Options
% 3.17/1.01  
% 3.17/1.01  --abstr_ref                             []
% 3.17/1.01  --abstr_ref_prep                        false
% 3.17/1.01  --abstr_ref_until_sat                   false
% 3.17/1.01  --abstr_ref_sig_restrict                funpre
% 3.17/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/1.01  --abstr_ref_under                       []
% 3.17/1.01  
% 3.17/1.01  ------ SAT Options
% 3.17/1.01  
% 3.17/1.01  --sat_mode                              false
% 3.17/1.01  --sat_fm_restart_options                ""
% 3.17/1.01  --sat_gr_def                            false
% 3.17/1.01  --sat_epr_types                         true
% 3.17/1.01  --sat_non_cyclic_types                  false
% 3.17/1.01  --sat_finite_models                     false
% 3.17/1.01  --sat_fm_lemmas                         false
% 3.17/1.01  --sat_fm_prep                           false
% 3.17/1.01  --sat_fm_uc_incr                        true
% 3.17/1.01  --sat_out_model                         small
% 3.17/1.01  --sat_out_clauses                       false
% 3.17/1.01  
% 3.17/1.01  ------ QBF Options
% 3.17/1.01  
% 3.17/1.01  --qbf_mode                              false
% 3.17/1.01  --qbf_elim_univ                         false
% 3.17/1.01  --qbf_dom_inst                          none
% 3.17/1.01  --qbf_dom_pre_inst                      false
% 3.17/1.01  --qbf_sk_in                             false
% 3.17/1.01  --qbf_pred_elim                         true
% 3.17/1.01  --qbf_split                             512
% 3.17/1.01  
% 3.17/1.01  ------ BMC1 Options
% 3.17/1.01  
% 3.17/1.01  --bmc1_incremental                      false
% 3.17/1.01  --bmc1_axioms                           reachable_all
% 3.17/1.01  --bmc1_min_bound                        0
% 3.17/1.01  --bmc1_max_bound                        -1
% 3.17/1.01  --bmc1_max_bound_default                -1
% 3.17/1.01  --bmc1_symbol_reachability              true
% 3.17/1.01  --bmc1_property_lemmas                  false
% 3.17/1.01  --bmc1_k_induction                      false
% 3.17/1.01  --bmc1_non_equiv_states                 false
% 3.17/1.01  --bmc1_deadlock                         false
% 3.17/1.01  --bmc1_ucm                              false
% 3.17/1.01  --bmc1_add_unsat_core                   none
% 3.17/1.01  --bmc1_unsat_core_children              false
% 3.17/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/1.01  --bmc1_out_stat                         full
% 3.17/1.01  --bmc1_ground_init                      false
% 3.17/1.01  --bmc1_pre_inst_next_state              false
% 3.17/1.01  --bmc1_pre_inst_state                   false
% 3.17/1.01  --bmc1_pre_inst_reach_state             false
% 3.17/1.01  --bmc1_out_unsat_core                   false
% 3.17/1.01  --bmc1_aig_witness_out                  false
% 3.17/1.01  --bmc1_verbose                          false
% 3.17/1.01  --bmc1_dump_clauses_tptp                false
% 3.17/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.17/1.01  --bmc1_dump_file                        -
% 3.17/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.17/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.17/1.01  --bmc1_ucm_extend_mode                  1
% 3.17/1.01  --bmc1_ucm_init_mode                    2
% 3.17/1.01  --bmc1_ucm_cone_mode                    none
% 3.17/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.17/1.01  --bmc1_ucm_relax_model                  4
% 3.17/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.17/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/1.01  --bmc1_ucm_layered_model                none
% 3.17/1.01  --bmc1_ucm_max_lemma_size               10
% 3.17/1.01  
% 3.17/1.01  ------ AIG Options
% 3.17/1.01  
% 3.17/1.01  --aig_mode                              false
% 3.17/1.01  
% 3.17/1.01  ------ Instantiation Options
% 3.17/1.01  
% 3.17/1.01  --instantiation_flag                    true
% 3.17/1.01  --inst_sos_flag                         false
% 3.17/1.01  --inst_sos_phase                        true
% 3.17/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/1.01  --inst_lit_sel_side                     none
% 3.17/1.01  --inst_solver_per_active                1400
% 3.17/1.01  --inst_solver_calls_frac                1.
% 3.17/1.01  --inst_passive_queue_type               priority_queues
% 3.17/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/1.01  --inst_passive_queues_freq              [25;2]
% 3.17/1.01  --inst_dismatching                      true
% 3.17/1.01  --inst_eager_unprocessed_to_passive     true
% 3.17/1.01  --inst_prop_sim_given                   true
% 3.17/1.01  --inst_prop_sim_new                     false
% 3.17/1.01  --inst_subs_new                         false
% 3.17/1.01  --inst_eq_res_simp                      false
% 3.17/1.01  --inst_subs_given                       false
% 3.17/1.01  --inst_orphan_elimination               true
% 3.17/1.01  --inst_learning_loop_flag               true
% 3.17/1.01  --inst_learning_start                   3000
% 3.17/1.01  --inst_learning_factor                  2
% 3.17/1.01  --inst_start_prop_sim_after_learn       3
% 3.17/1.01  --inst_sel_renew                        solver
% 3.17/1.01  --inst_lit_activity_flag                true
% 3.17/1.01  --inst_restr_to_given                   false
% 3.17/1.01  --inst_activity_threshold               500
% 3.17/1.01  --inst_out_proof                        true
% 3.17/1.01  
% 3.17/1.01  ------ Resolution Options
% 3.17/1.01  
% 3.17/1.01  --resolution_flag                       false
% 3.17/1.01  --res_lit_sel                           adaptive
% 3.17/1.01  --res_lit_sel_side                      none
% 3.17/1.01  --res_ordering                          kbo
% 3.17/1.01  --res_to_prop_solver                    active
% 3.17/1.01  --res_prop_simpl_new                    false
% 3.17/1.01  --res_prop_simpl_given                  true
% 3.17/1.01  --res_passive_queue_type                priority_queues
% 3.17/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/1.01  --res_passive_queues_freq               [15;5]
% 3.17/1.01  --res_forward_subs                      full
% 3.17/1.01  --res_backward_subs                     full
% 3.17/1.01  --res_forward_subs_resolution           true
% 3.17/1.01  --res_backward_subs_resolution          true
% 3.17/1.01  --res_orphan_elimination                true
% 3.17/1.01  --res_time_limit                        2.
% 3.17/1.01  --res_out_proof                         true
% 3.17/1.01  
% 3.17/1.01  ------ Superposition Options
% 3.17/1.01  
% 3.17/1.01  --superposition_flag                    true
% 3.17/1.01  --sup_passive_queue_type                priority_queues
% 3.17/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.17/1.01  --demod_completeness_check              fast
% 3.17/1.01  --demod_use_ground                      true
% 3.17/1.01  --sup_to_prop_solver                    passive
% 3.17/1.01  --sup_prop_simpl_new                    true
% 3.17/1.01  --sup_prop_simpl_given                  true
% 3.17/1.01  --sup_fun_splitting                     false
% 3.17/1.01  --sup_smt_interval                      50000
% 3.17/1.01  
% 3.17/1.01  ------ Superposition Simplification Setup
% 3.17/1.01  
% 3.17/1.01  --sup_indices_passive                   []
% 3.17/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.01  --sup_full_bw                           [BwDemod]
% 3.17/1.01  --sup_immed_triv                        [TrivRules]
% 3.17/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.01  --sup_immed_bw_main                     []
% 3.17/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.01  
% 3.17/1.01  ------ Combination Options
% 3.17/1.01  
% 3.17/1.01  --comb_res_mult                         3
% 3.17/1.01  --comb_sup_mult                         2
% 3.17/1.01  --comb_inst_mult                        10
% 3.17/1.01  
% 3.17/1.01  ------ Debug Options
% 3.17/1.01  
% 3.17/1.01  --dbg_backtrace                         false
% 3.17/1.01  --dbg_dump_prop_clauses                 false
% 3.17/1.01  --dbg_dump_prop_clauses_file            -
% 3.17/1.01  --dbg_out_stat                          false
% 3.17/1.01  
% 3.17/1.01  
% 3.17/1.01  
% 3.17/1.01  
% 3.17/1.01  ------ Proving...
% 3.17/1.01  
% 3.17/1.01  
% 3.17/1.01  % SZS status Theorem for theBenchmark.p
% 3.17/1.01  
% 3.17/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/1.01  
% 3.17/1.01  fof(f10,conjecture,(
% 3.17/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f11,negated_conjecture,(
% 3.17/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 3.17/1.01    inference(negated_conjecture,[],[f10])).
% 3.17/1.01  
% 3.17/1.01  fof(f23,plain,(
% 3.17/1.01    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2) & (k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.17/1.01    inference(ennf_transformation,[],[f11])).
% 3.17/1.01  
% 3.17/1.01  fof(f24,plain,(
% 3.17/1.01    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.17/1.01    inference(flattening,[],[f23])).
% 3.17/1.01  
% 3.17/1.01  fof(f27,plain,(
% 3.17/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,sK4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.17/1.01    introduced(choice_axiom,[])).
% 3.17/1.01  
% 3.17/1.01  fof(f26,plain,(
% 3.17/1.01    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) != sK2 & k1_xboole_0 != sK2 & k2_relset_1(sK1,sK2,X4) = sK2 & k2_relset_1(sK0,sK1,sK3) = sK1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.17/1.01    introduced(choice_axiom,[])).
% 3.17/1.01  
% 3.17/1.01  fof(f28,plain,(
% 3.17/1.01    (k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 & k1_xboole_0 != sK2 & k2_relset_1(sK1,sK2,sK4) = sK2 & k2_relset_1(sK0,sK1,sK3) = sK1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.17/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f27,f26])).
% 3.17/1.01  
% 3.17/1.01  fof(f46,plain,(
% 3.17/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  fof(f49,plain,(
% 3.17/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  fof(f9,axiom,(
% 3.17/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f21,plain,(
% 3.17/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.17/1.01    inference(ennf_transformation,[],[f9])).
% 3.17/1.01  
% 3.17/1.01  fof(f22,plain,(
% 3.17/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.17/1.01    inference(flattening,[],[f21])).
% 3.17/1.01  
% 3.17/1.01  fof(f43,plain,(
% 3.17/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.17/1.01    inference(cnf_transformation,[],[f22])).
% 3.17/1.01  
% 3.17/1.01  fof(f47,plain,(
% 3.17/1.01    v1_funct_1(sK4)),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  fof(f44,plain,(
% 3.17/1.01    v1_funct_1(sK3)),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  fof(f8,axiom,(
% 3.17/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f19,plain,(
% 3.17/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.17/1.01    inference(ennf_transformation,[],[f8])).
% 3.17/1.01  
% 3.17/1.01  fof(f20,plain,(
% 3.17/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.17/1.01    inference(flattening,[],[f19])).
% 3.17/1.01  
% 3.17/1.01  fof(f42,plain,(
% 3.17/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.17/1.01    inference(cnf_transformation,[],[f20])).
% 3.17/1.01  
% 3.17/1.01  fof(f6,axiom,(
% 3.17/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f16,plain,(
% 3.17/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.01    inference(ennf_transformation,[],[f6])).
% 3.17/1.01  
% 3.17/1.01  fof(f34,plain,(
% 3.17/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.01    inference(cnf_transformation,[],[f16])).
% 3.17/1.01  
% 3.17/1.01  fof(f1,axiom,(
% 3.17/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f12,plain,(
% 3.17/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.17/1.01    inference(ennf_transformation,[],[f1])).
% 3.17/1.01  
% 3.17/1.01  fof(f29,plain,(
% 3.17/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.17/1.01    inference(cnf_transformation,[],[f12])).
% 3.17/1.01  
% 3.17/1.01  fof(f2,axiom,(
% 3.17/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f30,plain,(
% 3.17/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.17/1.01    inference(cnf_transformation,[],[f2])).
% 3.17/1.01  
% 3.17/1.01  fof(f4,axiom,(
% 3.17/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f14,plain,(
% 3.17/1.01    ! [X0] : (! [X1] : (k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.17/1.01    inference(ennf_transformation,[],[f4])).
% 3.17/1.01  
% 3.17/1.01  fof(f32,plain,(
% 3.17/1.01    ( ! [X0,X1] : (k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.17/1.01    inference(cnf_transformation,[],[f14])).
% 3.17/1.01  
% 3.17/1.01  fof(f50,plain,(
% 3.17/1.01    k2_relset_1(sK0,sK1,sK3) = sK1),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  fof(f3,axiom,(
% 3.17/1.01    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f13,plain,(
% 3.17/1.01    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.17/1.01    inference(ennf_transformation,[],[f3])).
% 3.17/1.01  
% 3.17/1.01  fof(f31,plain,(
% 3.17/1.01    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.17/1.01    inference(cnf_transformation,[],[f13])).
% 3.17/1.01  
% 3.17/1.01  fof(f5,axiom,(
% 3.17/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f15,plain,(
% 3.17/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.01    inference(ennf_transformation,[],[f5])).
% 3.17/1.01  
% 3.17/1.01  fof(f33,plain,(
% 3.17/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.01    inference(cnf_transformation,[],[f15])).
% 3.17/1.01  
% 3.17/1.01  fof(f7,axiom,(
% 3.17/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.17/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.01  
% 3.17/1.01  fof(f17,plain,(
% 3.17/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.01    inference(ennf_transformation,[],[f7])).
% 3.17/1.01  
% 3.17/1.01  fof(f18,plain,(
% 3.17/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.01    inference(flattening,[],[f17])).
% 3.17/1.01  
% 3.17/1.01  fof(f25,plain,(
% 3.17/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.01    inference(nnf_transformation,[],[f18])).
% 3.17/1.01  
% 3.17/1.01  fof(f35,plain,(
% 3.17/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.01    inference(cnf_transformation,[],[f25])).
% 3.17/1.01  
% 3.17/1.01  fof(f48,plain,(
% 3.17/1.01    v1_funct_2(sK4,sK1,sK2)),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  fof(f52,plain,(
% 3.17/1.01    k1_xboole_0 != sK2),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  fof(f51,plain,(
% 3.17/1.01    k2_relset_1(sK1,sK2,sK4) = sK2),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  fof(f53,plain,(
% 3.17/1.01    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2),
% 3.17/1.01    inference(cnf_transformation,[],[f28])).
% 3.17/1.01  
% 3.17/1.01  cnf(c_22,negated_conjecture,
% 3.17/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.17/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_477,negated_conjecture,
% 3.17/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_824,plain,
% 3.17/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_19,negated_conjecture,
% 3.17/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.17/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_479,negated_conjecture,
% 3.17/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_822,plain,
% 3.17/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_14,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.17/1.01      | ~ v1_funct_1(X0)
% 3.17/1.01      | ~ v1_funct_1(X3)
% 3.17/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.17/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_484,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.17/1.01      | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
% 3.17/1.01      | ~ v1_funct_1(X0_47)
% 3.17/1.01      | ~ v1_funct_1(X3_47)
% 3.17/1.01      | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_821,plain,
% 3.17/1.01      ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X4_47,X5_47) = k5_relat_1(X4_47,X5_47)
% 3.17/1.01      | m1_subset_1(X5_47,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
% 3.17/1.01      | m1_subset_1(X4_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.17/1.01      | v1_funct_1(X5_47) != iProver_top
% 3.17/1.01      | v1_funct_1(X4_47) != iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_2674,plain,
% 3.17/1.01      ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
% 3.17/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.17/1.01      | v1_funct_1(X2_47) != iProver_top
% 3.17/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_822,c_821]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_21,negated_conjecture,
% 3.17/1.01      ( v1_funct_1(sK4) ),
% 3.17/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_28,plain,
% 3.17/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_2841,plain,
% 3.17/1.01      ( v1_funct_1(X2_47) != iProver_top
% 3.17/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.17/1.01      | k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4) ),
% 3.17/1.01      inference(global_propositional_subsumption,
% 3.17/1.01                [status(thm)],
% 3.17/1.01                [c_2674,c_28]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_2842,plain,
% 3.17/1.01      ( k1_partfun1(X0_47,X1_47,sK1,sK2,X2_47,sK4) = k5_relat_1(X2_47,sK4)
% 3.17/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.17/1.01      | v1_funct_1(X2_47) != iProver_top ),
% 3.17/1.01      inference(renaming,[status(thm)],[c_2841]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_2851,plain,
% 3.17/1.01      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.17/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_824,c_2842]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_24,negated_conjecture,
% 3.17/1.01      ( v1_funct_1(sK3) ),
% 3.17/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_25,plain,
% 3.17/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_2902,plain,
% 3.17/1.01      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.17/1.01      inference(global_propositional_subsumption,
% 3.17/1.01                [status(thm)],
% 3.17/1.01                [c_2851,c_25]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_12,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.17/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.17/1.01      | ~ v1_funct_1(X0)
% 3.17/1.01      | ~ v1_funct_1(X3) ),
% 3.17/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_486,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.17/1.01      | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
% 3.17/1.01      | m1_subset_1(k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X4_47,X2_47)))
% 3.17/1.01      | ~ v1_funct_1(X0_47)
% 3.17/1.01      | ~ v1_funct_1(X3_47) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_819,plain,
% 3.17/1.01      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
% 3.17/1.01      | m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47))) != iProver_top
% 3.17/1.01      | m1_subset_1(k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X4_47,X2_47))) = iProver_top
% 3.17/1.01      | v1_funct_1(X0_47) != iProver_top
% 3.17/1.01      | v1_funct_1(X3_47) != iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_2907,plain,
% 3.17/1.01      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.17/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.17/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.17/1.01      | v1_funct_1(sK4) != iProver_top
% 3.17/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_2902,c_819]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_27,plain,
% 3.17/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_30,plain,
% 3.17/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_3678,plain,
% 3.17/1.01      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.17/1.01      inference(global_propositional_subsumption,
% 3.17/1.01                [status(thm)],
% 3.17/1.01                [c_2907,c_25,c_27,c_28,c_30]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_5,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.17/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_487,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.17/1.01      | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_818,plain,
% 3.17/1.01      ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
% 3.17/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_3687,plain,
% 3.17/1.01      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_3678,c_818]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_0,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.17/1.01      | ~ v1_relat_1(X1)
% 3.17/1.01      | v1_relat_1(X0) ),
% 3.17/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_492,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 3.17/1.01      | ~ v1_relat_1(X1_47)
% 3.17/1.01      | v1_relat_1(X0_47) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_813,plain,
% 3.17/1.01      ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
% 3.17/1.01      | v1_relat_1(X1_47) != iProver_top
% 3.17/1.01      | v1_relat_1(X0_47) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1746,plain,
% 3.17/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.17/1.01      | v1_relat_1(sK4) = iProver_top ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_822,c_813]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_980,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.17/1.01      | v1_relat_1(X0_47)
% 3.17/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1_47,X2_47)) ),
% 3.17/1.01      inference(instantiation,[status(thm)],[c_492]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1178,plain,
% 3.17/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.17/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 3.17/1.01      | v1_relat_1(sK4) ),
% 3.17/1.01      inference(instantiation,[status(thm)],[c_980]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1179,plain,
% 3.17/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.17/1.01      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.17/1.01      | v1_relat_1(sK4) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1178]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1,plain,
% 3.17/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.17/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_491,plain,
% 3.17/1.01      ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1725,plain,
% 3.17/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.17/1.01      inference(instantiation,[status(thm)],[c_491]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1726,plain,
% 3.17/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1725]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1858,plain,
% 3.17/1.01      ( v1_relat_1(sK4) = iProver_top ),
% 3.17/1.01      inference(global_propositional_subsumption,
% 3.17/1.01                [status(thm)],
% 3.17/1.01                [c_1746,c_30,c_1179,c_1726]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1747,plain,
% 3.17/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.17/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_824,c_813]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1181,plain,
% 3.17/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.17/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.17/1.01      | v1_relat_1(sK3) ),
% 3.17/1.01      inference(instantiation,[status(thm)],[c_980]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1182,plain,
% 3.17/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.17/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.17/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1181]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1728,plain,
% 3.17/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.17/1.01      inference(instantiation,[status(thm)],[c_491]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1729,plain,
% 3.17/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1728]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1878,plain,
% 3.17/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 3.17/1.01      inference(global_propositional_subsumption,
% 3.17/1.01                [status(thm)],
% 3.17/1.01                [c_1747,c_27,c_1182,c_1729]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_3,plain,
% 3.17/1.01      ( ~ v1_relat_1(X0)
% 3.17/1.01      | ~ v1_relat_1(X1)
% 3.17/1.01      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ),
% 3.17/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_489,plain,
% 3.17/1.01      ( ~ v1_relat_1(X0_47)
% 3.17/1.01      | ~ v1_relat_1(X1_47)
% 3.17/1.01      | k2_relat_1(k5_relat_1(X0_47,X1_47)) = k9_relat_1(X1_47,k2_relat_1(X0_47)) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_816,plain,
% 3.17/1.01      ( k2_relat_1(k5_relat_1(X0_47,X1_47)) = k9_relat_1(X1_47,k2_relat_1(X0_47))
% 3.17/1.01      | v1_relat_1(X0_47) != iProver_top
% 3.17/1.01      | v1_relat_1(X1_47) != iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1883,plain,
% 3.17/1.01      ( k2_relat_1(k5_relat_1(sK3,X0_47)) = k9_relat_1(X0_47,k2_relat_1(sK3))
% 3.17/1.01      | v1_relat_1(X0_47) != iProver_top ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_1878,c_816]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1767,plain,
% 3.17/1.01      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_824,c_818]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_18,negated_conjecture,
% 3.17/1.01      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 3.17/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_480,negated_conjecture,
% 3.17/1.01      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1769,plain,
% 3.17/1.01      ( k2_relat_1(sK3) = sK1 ),
% 3.17/1.01      inference(light_normalisation,[status(thm)],[c_1767,c_480]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1890,plain,
% 3.17/1.01      ( k2_relat_1(k5_relat_1(sK3,X0_47)) = k9_relat_1(X0_47,sK1)
% 3.17/1.01      | v1_relat_1(X0_47) != iProver_top ),
% 3.17/1.01      inference(light_normalisation,[status(thm)],[c_1883,c_1769]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1918,plain,
% 3.17/1.01      ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_1858,c_1890]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_2,plain,
% 3.17/1.01      ( ~ v1_relat_1(X0)
% 3.17/1.01      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.17/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_490,plain,
% 3.17/1.01      ( ~ v1_relat_1(X0_47)
% 3.17/1.01      | k9_relat_1(X0_47,k1_relat_1(X0_47)) = k2_relat_1(X0_47) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_815,plain,
% 3.17/1.01      ( k9_relat_1(X0_47,k1_relat_1(X0_47)) = k2_relat_1(X0_47)
% 3.17/1.01      | v1_relat_1(X0_47) != iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1864,plain,
% 3.17/1.01      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_1858,c_815]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_4,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.17/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_488,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.17/1.01      | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_817,plain,
% 3.17/1.01      ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
% 3.17/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.17/1.01      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1279,plain,
% 3.17/1.01      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_822,c_817]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_11,plain,
% 3.17/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.17/1.01      | k1_xboole_0 = X2 ),
% 3.17/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_20,negated_conjecture,
% 3.17/1.01      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.17/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_312,plain,
% 3.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.17/1.01      | sK4 != X0
% 3.17/1.01      | sK1 != X1
% 3.17/1.01      | sK2 != X2
% 3.17/1.01      | k1_xboole_0 = X2 ),
% 3.17/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_313,plain,
% 3.17/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.17/1.01      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.17/1.01      | k1_xboole_0 = sK2 ),
% 3.17/1.01      inference(unflattening,[status(thm)],[c_312]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_16,negated_conjecture,
% 3.17/1.01      ( k1_xboole_0 != sK2 ),
% 3.17/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_315,plain,
% 3.17/1.01      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.17/1.01      inference(global_propositional_subsumption,
% 3.17/1.01                [status(thm)],
% 3.17/1.01                [c_313,c_19,c_16]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_471,plain,
% 3.17/1.01      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_315]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1284,plain,
% 3.17/1.01      ( k1_relat_1(sK4) = sK1 ),
% 3.17/1.01      inference(light_normalisation,[status(thm)],[c_1279,c_471]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1766,plain,
% 3.17/1.01      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.17/1.01      inference(superposition,[status(thm)],[c_822,c_818]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_17,negated_conjecture,
% 3.17/1.01      ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
% 3.17/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_481,negated_conjecture,
% 3.17/1.01      ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1772,plain,
% 3.17/1.01      ( k2_relat_1(sK4) = sK2 ),
% 3.17/1.01      inference(light_normalisation,[status(thm)],[c_1766,c_481]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1866,plain,
% 3.17/1.01      ( k9_relat_1(sK4,sK1) = sK2 ),
% 3.17/1.01      inference(light_normalisation,[status(thm)],[c_1864,c_1284,c_1772]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_1923,plain,
% 3.17/1.01      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.17/1.01      inference(light_normalisation,[status(thm)],[c_1918,c_1866]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_3692,plain,
% 3.17/1.01      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 3.17/1.01      inference(light_normalisation,[status(thm)],[c_3687,c_1923]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_15,negated_conjecture,
% 3.17/1.01      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
% 3.17/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_483,negated_conjecture,
% 3.17/1.01      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
% 3.17/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(c_2905,plain,
% 3.17/1.01      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2 ),
% 3.17/1.01      inference(demodulation,[status(thm)],[c_2902,c_483]) ).
% 3.17/1.01  
% 3.17/1.01  cnf(contradiction,plain,
% 3.17/1.01      ( $false ),
% 3.17/1.01      inference(minisat,[status(thm)],[c_3692,c_2905]) ).
% 3.17/1.01  
% 3.17/1.01  
% 3.17/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/1.01  
% 3.17/1.01  ------                               Statistics
% 3.17/1.01  
% 3.17/1.01  ------ General
% 3.17/1.01  
% 3.17/1.01  abstr_ref_over_cycles:                  0
% 3.17/1.01  abstr_ref_under_cycles:                 0
% 3.17/1.01  gc_basic_clause_elim:                   0
% 3.17/1.01  forced_gc_time:                         0
% 3.17/1.01  parsing_time:                           0.015
% 3.17/1.01  unif_index_cands_time:                  0.
% 3.17/1.01  unif_index_add_time:                    0.
% 3.17/1.01  orderings_time:                         0.
% 3.17/1.01  out_proof_time:                         0.01
% 3.17/1.01  total_time:                             0.21
% 3.17/1.01  num_of_symbols:                         52
% 3.17/1.01  num_of_terms:                           5864
% 3.17/1.01  
% 3.17/1.01  ------ Preprocessing
% 3.17/1.01  
% 3.17/1.01  num_of_splits:                          0
% 3.17/1.01  num_of_split_atoms:                     0
% 3.17/1.01  num_of_reused_defs:                     0
% 3.17/1.01  num_eq_ax_congr_red:                    14
% 3.17/1.01  num_of_sem_filtered_clauses:            1
% 3.17/1.01  num_of_subtypes:                        2
% 3.17/1.01  monotx_restored_types:                  0
% 3.17/1.01  sat_num_of_epr_types:                   0
% 3.17/1.01  sat_num_of_non_cyclic_types:            0
% 3.17/1.01  sat_guarded_non_collapsed_types:        0
% 3.17/1.01  num_pure_diseq_elim:                    0
% 3.17/1.01  simp_replaced_by:                       0
% 3.17/1.01  res_preprocessed:                       121
% 3.17/1.01  prep_upred:                             0
% 3.17/1.01  prep_unflattend:                        34
% 3.17/1.01  smt_new_axioms:                         0
% 3.17/1.01  pred_elim_cands:                        3
% 3.17/1.01  pred_elim:                              1
% 3.17/1.01  pred_elim_cl:                           2
% 3.17/1.01  pred_elim_cycles:                       3
% 3.17/1.01  merged_defs:                            0
% 3.17/1.01  merged_defs_ncl:                        0
% 3.17/1.01  bin_hyper_res:                          0
% 3.17/1.01  prep_cycles:                            4
% 3.17/1.01  pred_elim_time:                         0.003
% 3.17/1.01  splitting_time:                         0.
% 3.17/1.01  sem_filter_time:                        0.
% 3.17/1.01  monotx_time:                            0.
% 3.17/1.01  subtype_inf_time:                       0.
% 3.17/1.01  
% 3.17/1.01  ------ Problem properties
% 3.17/1.01  
% 3.17/1.01  clauses:                                23
% 3.17/1.01  conjectures:                            8
% 3.17/1.01  epr:                                    3
% 3.17/1.01  horn:                                   20
% 3.17/1.01  ground:                                 14
% 3.17/1.01  unary:                                  10
% 3.17/1.01  binary:                                 4
% 3.17/1.01  lits:                                   53
% 3.17/1.01  lits_eq:                                22
% 3.17/1.01  fd_pure:                                0
% 3.17/1.01  fd_pseudo:                              0
% 3.17/1.01  fd_cond:                                0
% 3.17/1.01  fd_pseudo_cond:                         0
% 3.17/1.01  ac_symbols:                             0
% 3.17/1.01  
% 3.17/1.01  ------ Propositional Solver
% 3.17/1.01  
% 3.17/1.01  prop_solver_calls:                      25
% 3.17/1.01  prop_fast_solver_calls:                 788
% 3.17/1.01  smt_solver_calls:                       0
% 3.17/1.01  smt_fast_solver_calls:                  0
% 3.17/1.01  prop_num_of_clauses:                    1586
% 3.17/1.01  prop_preprocess_simplified:             4430
% 3.17/1.01  prop_fo_subsumed:                       40
% 3.17/1.01  prop_solver_time:                       0.
% 3.17/1.01  smt_solver_time:                        0.
% 3.17/1.01  smt_fast_solver_time:                   0.
% 3.17/1.01  prop_fast_solver_time:                  0.
% 3.17/1.01  prop_unsat_core_time:                   0.
% 3.17/1.01  
% 3.17/1.01  ------ QBF
% 3.17/1.01  
% 3.17/1.01  qbf_q_res:                              0
% 3.17/1.01  qbf_num_tautologies:                    0
% 3.17/1.01  qbf_prep_cycles:                        0
% 3.17/1.01  
% 3.17/1.01  ------ BMC1
% 3.17/1.01  
% 3.17/1.01  bmc1_current_bound:                     -1
% 3.17/1.01  bmc1_last_solved_bound:                 -1
% 3.17/1.01  bmc1_unsat_core_size:                   -1
% 3.17/1.01  bmc1_unsat_core_parents_size:           -1
% 3.17/1.01  bmc1_merge_next_fun:                    0
% 3.17/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.17/1.01  
% 3.17/1.01  ------ Instantiation
% 3.17/1.01  
% 3.17/1.01  inst_num_of_clauses:                    403
% 3.17/1.01  inst_num_in_passive:                    11
% 3.17/1.01  inst_num_in_active:                     321
% 3.17/1.01  inst_num_in_unprocessed:                71
% 3.17/1.01  inst_num_of_loops:                      360
% 3.17/1.01  inst_num_of_learning_restarts:          0
% 3.17/1.01  inst_num_moves_active_passive:          36
% 3.17/1.01  inst_lit_activity:                      0
% 3.17/1.01  inst_lit_activity_moves:                0
% 3.17/1.01  inst_num_tautologies:                   0
% 3.17/1.01  inst_num_prop_implied:                  0
% 3.17/1.01  inst_num_existing_simplified:           0
% 3.17/1.01  inst_num_eq_res_simplified:             0
% 3.17/1.01  inst_num_child_elim:                    0
% 3.17/1.01  inst_num_of_dismatching_blockings:      119
% 3.17/1.01  inst_num_of_non_proper_insts:           279
% 3.17/1.01  inst_num_of_duplicates:                 0
% 3.17/1.01  inst_inst_num_from_inst_to_res:         0
% 3.17/1.01  inst_dismatching_checking_time:         0.
% 3.17/1.01  
% 3.17/1.01  ------ Resolution
% 3.17/1.01  
% 3.17/1.01  res_num_of_clauses:                     0
% 3.17/1.01  res_num_in_passive:                     0
% 3.17/1.01  res_num_in_active:                      0
% 3.17/1.01  res_num_of_loops:                       125
% 3.17/1.01  res_forward_subset_subsumed:            35
% 3.17/1.01  res_backward_subset_subsumed:           0
% 3.17/1.01  res_forward_subsumed:                   0
% 3.17/1.01  res_backward_subsumed:                  0
% 3.17/1.01  res_forward_subsumption_resolution:     0
% 3.17/1.01  res_backward_subsumption_resolution:    0
% 3.17/1.01  res_clause_to_clause_subsumption:       140
% 3.17/1.01  res_orphan_elimination:                 0
% 3.17/1.01  res_tautology_del:                      30
% 3.17/1.01  res_num_eq_res_simplified:              0
% 3.17/1.01  res_num_sel_changes:                    0
% 3.17/1.01  res_moves_from_active_to_pass:          0
% 3.17/1.01  
% 3.17/1.01  ------ Superposition
% 3.17/1.01  
% 3.17/1.01  sup_time_total:                         0.
% 3.17/1.01  sup_time_generating:                    0.
% 3.17/1.01  sup_time_sim_full:                      0.
% 3.17/1.01  sup_time_sim_immed:                     0.
% 3.17/1.01  
% 3.17/1.01  sup_num_of_clauses:                     102
% 3.17/1.01  sup_num_in_active:                      71
% 3.17/1.01  sup_num_in_passive:                     31
% 3.17/1.01  sup_num_of_loops:                       71
% 3.17/1.01  sup_fw_superposition:                   28
% 3.17/1.01  sup_bw_superposition:                   52
% 3.17/1.01  sup_immediate_simplified:               15
% 3.17/1.01  sup_given_eliminated:                   0
% 3.17/1.01  comparisons_done:                       0
% 3.17/1.01  comparisons_avoided:                    3
% 3.17/1.01  
% 3.17/1.01  ------ Simplifications
% 3.17/1.01  
% 3.17/1.01  
% 3.17/1.01  sim_fw_subset_subsumed:                 0
% 3.17/1.01  sim_bw_subset_subsumed:                 0
% 3.17/1.01  sim_fw_subsumed:                        0
% 3.17/1.01  sim_bw_subsumed:                        0
% 3.17/1.01  sim_fw_subsumption_res:                 0
% 3.17/1.01  sim_bw_subsumption_res:                 0
% 3.17/1.01  sim_tautology_del:                      0
% 3.17/1.01  sim_eq_tautology_del:                   0
% 3.17/1.01  sim_eq_res_simp:                        0
% 3.17/1.01  sim_fw_demodulated:                     0
% 3.17/1.01  sim_bw_demodulated:                     1
% 3.17/1.01  sim_light_normalised:                   15
% 3.17/1.01  sim_joinable_taut:                      0
% 3.17/1.01  sim_joinable_simp:                      0
% 3.17/1.01  sim_ac_normalised:                      0
% 3.17/1.01  sim_smt_subsumption:                    0
% 3.17/1.01  
%------------------------------------------------------------------------------
