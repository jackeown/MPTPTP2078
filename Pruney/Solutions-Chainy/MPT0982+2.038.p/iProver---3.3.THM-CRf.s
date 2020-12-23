%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:44 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 643 expanded)
%              Number of clauses        :   95 ( 208 expanded)
%              Number of leaves         :   16 ( 155 expanded)
%              Depth                    :   16
%              Number of atoms          :  505 (4229 expanded)
%              Number of equality atoms :  217 (1399 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X1,X3) != X1
        & k1_xboole_0 != X2
        & v2_funct_1(sK4)
        & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK1,sK3) != sK1
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_relset_1(sK0,sK1,sK3) != sK1
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f38,f37])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1283,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1285,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1288,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2289,plain,
    ( k2_relset_1(X0,X1,k4_relset_1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k4_relset_1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1288])).

cnf(c_5270,plain,
    ( k2_relset_1(X0,sK2,k4_relset_1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k4_relset_1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_2289])).

cnf(c_5368,plain,
    ( k2_relset_1(sK0,sK2,k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1283,c_5270])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1287,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3441,plain,
    ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1287])).

cnf(c_3835,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1283,c_3441])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1286,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3625,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1286])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4579,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3625,c_34])).

cnf(c_4580,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4579])).

cnf(c_4592,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_4580])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1702,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_2160,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_3312,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_5122,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4592,c_30,c_28,c_27,c_25,c_3312])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5127,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5122,c_24])).

cnf(c_5370,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5368,c_3835,c_5127])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1289,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2395,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1285,c_1289])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_476,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_478,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_25,c_22])).

cnf(c_2400,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2395,c_478])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_368,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_369,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_373,plain,
    ( ~ v1_funct_1(X0)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_27])).

cnf(c_374,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_1280,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_2818,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2400,c_1280])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1712,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1294])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_216,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_216])).

cnf(c_1573,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_2145,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_2147,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2145])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3726,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3727,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3726])).

cnf(c_6715,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2818,c_1712,c_2147,c_3727])).

cnf(c_6716,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6715])).

cnf(c_6725,plain,
    ( k2_relat_1(sK4) != sK2
    | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5370,c_6716])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1292,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5399,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5370,c_1292])).

cnf(c_2291,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1283,c_1288])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1291,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2852,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2291,c_1291])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5256,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2852,c_33])).

cnf(c_5261,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5256,c_1294])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1297,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5326,plain,
    ( k2_relat_1(sK3) = sK1
    | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5261,c_1297])).

cnf(c_2290,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1285,c_1288])).

cnf(c_2823,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2290,c_1291])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5226,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2823,c_36])).

cnf(c_5231,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5226,c_1294])).

cnf(c_5322,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5231,c_1297])).

cnf(c_3730,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3731,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3730])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2851,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_2291,c_21])).

cnf(c_2149,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_2151,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2149])).

cnf(c_1713,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1294])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6725,c_5399,c_5326,c_5322,c_3731,c_3727,c_2851,c_2151,c_2147,c_1713,c_1712,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.15/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/0.98  
% 3.15/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.15/0.98  
% 3.15/0.98  ------  iProver source info
% 3.15/0.98  
% 3.15/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.15/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.15/0.98  git: non_committed_changes: false
% 3.15/0.98  git: last_make_outside_of_git: false
% 3.15/0.98  
% 3.15/0.98  ------ 
% 3.15/0.98  
% 3.15/0.98  ------ Input Options
% 3.15/0.98  
% 3.15/0.98  --out_options                           all
% 3.15/0.98  --tptp_safe_out                         true
% 3.15/0.98  --problem_path                          ""
% 3.15/0.98  --include_path                          ""
% 3.15/0.98  --clausifier                            res/vclausify_rel
% 3.15/0.98  --clausifier_options                    --mode clausify
% 3.15/0.98  --stdin                                 false
% 3.15/0.98  --stats_out                             all
% 3.15/0.98  
% 3.15/0.98  ------ General Options
% 3.15/0.98  
% 3.15/0.98  --fof                                   false
% 3.15/0.98  --time_out_real                         305.
% 3.15/0.98  --time_out_virtual                      -1.
% 3.15/0.98  --symbol_type_check                     false
% 3.15/0.98  --clausify_out                          false
% 3.15/0.98  --sig_cnt_out                           false
% 3.15/0.98  --trig_cnt_out                          false
% 3.15/0.98  --trig_cnt_out_tolerance                1.
% 3.15/0.98  --trig_cnt_out_sk_spl                   false
% 3.15/0.98  --abstr_cl_out                          false
% 3.15/0.98  
% 3.15/0.98  ------ Global Options
% 3.15/0.98  
% 3.15/0.98  --schedule                              default
% 3.15/0.98  --add_important_lit                     false
% 3.15/0.98  --prop_solver_per_cl                    1000
% 3.15/0.98  --min_unsat_core                        false
% 3.15/0.98  --soft_assumptions                      false
% 3.15/0.98  --soft_lemma_size                       3
% 3.15/0.98  --prop_impl_unit_size                   0
% 3.15/0.98  --prop_impl_unit                        []
% 3.15/0.98  --share_sel_clauses                     true
% 3.15/0.98  --reset_solvers                         false
% 3.15/0.98  --bc_imp_inh                            [conj_cone]
% 3.15/0.98  --conj_cone_tolerance                   3.
% 3.15/0.98  --extra_neg_conj                        none
% 3.15/0.98  --large_theory_mode                     true
% 3.15/0.98  --prolific_symb_bound                   200
% 3.15/0.98  --lt_threshold                          2000
% 3.15/0.98  --clause_weak_htbl                      true
% 3.15/0.98  --gc_record_bc_elim                     false
% 3.15/0.98  
% 3.15/0.98  ------ Preprocessing Options
% 3.15/0.98  
% 3.15/0.98  --preprocessing_flag                    true
% 3.15/0.98  --time_out_prep_mult                    0.1
% 3.15/0.98  --splitting_mode                        input
% 3.15/0.98  --splitting_grd                         true
% 3.15/0.98  --splitting_cvd                         false
% 3.15/0.98  --splitting_cvd_svl                     false
% 3.15/0.98  --splitting_nvd                         32
% 3.15/0.98  --sub_typing                            true
% 3.15/0.98  --prep_gs_sim                           true
% 3.15/0.98  --prep_unflatten                        true
% 3.15/0.98  --prep_res_sim                          true
% 3.15/0.98  --prep_upred                            true
% 3.15/0.98  --prep_sem_filter                       exhaustive
% 3.15/0.98  --prep_sem_filter_out                   false
% 3.15/0.98  --pred_elim                             true
% 3.15/0.98  --res_sim_input                         true
% 3.15/0.98  --eq_ax_congr_red                       true
% 3.15/0.98  --pure_diseq_elim                       true
% 3.15/0.98  --brand_transform                       false
% 3.15/0.98  --non_eq_to_eq                          false
% 3.15/0.98  --prep_def_merge                        true
% 3.15/0.98  --prep_def_merge_prop_impl              false
% 3.15/0.98  --prep_def_merge_mbd                    true
% 3.15/0.98  --prep_def_merge_tr_red                 false
% 3.15/0.98  --prep_def_merge_tr_cl                  false
% 3.15/0.98  --smt_preprocessing                     true
% 3.15/0.98  --smt_ac_axioms                         fast
% 3.15/0.98  --preprocessed_out                      false
% 3.15/0.98  --preprocessed_stats                    false
% 3.15/0.98  
% 3.15/0.98  ------ Abstraction refinement Options
% 3.15/0.98  
% 3.15/0.98  --abstr_ref                             []
% 3.15/0.98  --abstr_ref_prep                        false
% 3.15/0.98  --abstr_ref_until_sat                   false
% 3.15/0.98  --abstr_ref_sig_restrict                funpre
% 3.15/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/0.98  --abstr_ref_under                       []
% 3.15/0.98  
% 3.15/0.98  ------ SAT Options
% 3.15/0.98  
% 3.15/0.98  --sat_mode                              false
% 3.15/0.98  --sat_fm_restart_options                ""
% 3.15/0.98  --sat_gr_def                            false
% 3.15/0.98  --sat_epr_types                         true
% 3.15/0.98  --sat_non_cyclic_types                  false
% 3.15/0.98  --sat_finite_models                     false
% 3.15/0.98  --sat_fm_lemmas                         false
% 3.15/0.98  --sat_fm_prep                           false
% 3.15/0.98  --sat_fm_uc_incr                        true
% 3.15/0.98  --sat_out_model                         small
% 3.15/0.98  --sat_out_clauses                       false
% 3.15/0.98  
% 3.15/0.98  ------ QBF Options
% 3.15/0.98  
% 3.15/0.98  --qbf_mode                              false
% 3.15/0.98  --qbf_elim_univ                         false
% 3.15/0.98  --qbf_dom_inst                          none
% 3.15/0.98  --qbf_dom_pre_inst                      false
% 3.15/0.98  --qbf_sk_in                             false
% 3.15/0.98  --qbf_pred_elim                         true
% 3.15/0.98  --qbf_split                             512
% 3.15/0.98  
% 3.15/0.98  ------ BMC1 Options
% 3.15/0.98  
% 3.15/0.98  --bmc1_incremental                      false
% 3.15/0.98  --bmc1_axioms                           reachable_all
% 3.15/0.98  --bmc1_min_bound                        0
% 3.15/0.98  --bmc1_max_bound                        -1
% 3.15/0.98  --bmc1_max_bound_default                -1
% 3.15/0.98  --bmc1_symbol_reachability              true
% 3.15/0.98  --bmc1_property_lemmas                  false
% 3.15/0.98  --bmc1_k_induction                      false
% 3.15/0.98  --bmc1_non_equiv_states                 false
% 3.15/0.98  --bmc1_deadlock                         false
% 3.15/0.98  --bmc1_ucm                              false
% 3.15/0.98  --bmc1_add_unsat_core                   none
% 3.15/0.98  --bmc1_unsat_core_children              false
% 3.15/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/0.98  --bmc1_out_stat                         full
% 3.15/0.98  --bmc1_ground_init                      false
% 3.15/0.98  --bmc1_pre_inst_next_state              false
% 3.15/0.98  --bmc1_pre_inst_state                   false
% 3.15/0.98  --bmc1_pre_inst_reach_state             false
% 3.15/0.98  --bmc1_out_unsat_core                   false
% 3.15/0.98  --bmc1_aig_witness_out                  false
% 3.15/0.98  --bmc1_verbose                          false
% 3.15/0.98  --bmc1_dump_clauses_tptp                false
% 3.15/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.15/0.98  --bmc1_dump_file                        -
% 3.15/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.15/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.15/0.98  --bmc1_ucm_extend_mode                  1
% 3.15/0.98  --bmc1_ucm_init_mode                    2
% 3.15/0.98  --bmc1_ucm_cone_mode                    none
% 3.15/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.15/0.98  --bmc1_ucm_relax_model                  4
% 3.15/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.15/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/0.98  --bmc1_ucm_layered_model                none
% 3.15/0.98  --bmc1_ucm_max_lemma_size               10
% 3.15/0.98  
% 3.15/0.98  ------ AIG Options
% 3.15/0.98  
% 3.15/0.98  --aig_mode                              false
% 3.15/0.98  
% 3.15/0.98  ------ Instantiation Options
% 3.15/0.98  
% 3.15/0.98  --instantiation_flag                    true
% 3.15/0.98  --inst_sos_flag                         false
% 3.15/0.98  --inst_sos_phase                        true
% 3.15/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/0.98  --inst_lit_sel_side                     num_symb
% 3.15/0.98  --inst_solver_per_active                1400
% 3.15/0.98  --inst_solver_calls_frac                1.
% 3.15/0.98  --inst_passive_queue_type               priority_queues
% 3.15/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/0.98  --inst_passive_queues_freq              [25;2]
% 3.15/0.98  --inst_dismatching                      true
% 3.15/0.98  --inst_eager_unprocessed_to_passive     true
% 3.15/0.98  --inst_prop_sim_given                   true
% 3.15/0.98  --inst_prop_sim_new                     false
% 3.15/0.98  --inst_subs_new                         false
% 3.15/0.98  --inst_eq_res_simp                      false
% 3.15/0.98  --inst_subs_given                       false
% 3.15/0.98  --inst_orphan_elimination               true
% 3.15/0.98  --inst_learning_loop_flag               true
% 3.15/0.98  --inst_learning_start                   3000
% 3.15/0.98  --inst_learning_factor                  2
% 3.15/0.98  --inst_start_prop_sim_after_learn       3
% 3.15/0.98  --inst_sel_renew                        solver
% 3.15/0.98  --inst_lit_activity_flag                true
% 3.15/0.98  --inst_restr_to_given                   false
% 3.15/0.98  --inst_activity_threshold               500
% 3.15/0.98  --inst_out_proof                        true
% 3.15/0.98  
% 3.15/0.98  ------ Resolution Options
% 3.15/0.98  
% 3.15/0.98  --resolution_flag                       true
% 3.15/0.98  --res_lit_sel                           adaptive
% 3.15/0.98  --res_lit_sel_side                      none
% 3.15/0.98  --res_ordering                          kbo
% 3.15/0.98  --res_to_prop_solver                    active
% 3.15/0.98  --res_prop_simpl_new                    false
% 3.15/0.98  --res_prop_simpl_given                  true
% 3.15/0.98  --res_passive_queue_type                priority_queues
% 3.15/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/0.98  --res_passive_queues_freq               [15;5]
% 3.15/0.98  --res_forward_subs                      full
% 3.15/0.98  --res_backward_subs                     full
% 3.15/0.98  --res_forward_subs_resolution           true
% 3.15/0.98  --res_backward_subs_resolution          true
% 3.15/0.98  --res_orphan_elimination                true
% 3.15/0.98  --res_time_limit                        2.
% 3.15/0.98  --res_out_proof                         true
% 3.15/0.98  
% 3.15/0.98  ------ Superposition Options
% 3.15/0.98  
% 3.15/0.98  --superposition_flag                    true
% 3.15/0.98  --sup_passive_queue_type                priority_queues
% 3.15/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.15/0.98  --demod_completeness_check              fast
% 3.15/0.98  --demod_use_ground                      true
% 3.15/0.98  --sup_to_prop_solver                    passive
% 3.15/0.98  --sup_prop_simpl_new                    true
% 3.15/0.98  --sup_prop_simpl_given                  true
% 3.15/0.98  --sup_fun_splitting                     false
% 3.15/0.98  --sup_smt_interval                      50000
% 3.15/0.98  
% 3.15/0.98  ------ Superposition Simplification Setup
% 3.15/0.98  
% 3.15/0.98  --sup_indices_passive                   []
% 3.15/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.98  --sup_full_bw                           [BwDemod]
% 3.15/0.98  --sup_immed_triv                        [TrivRules]
% 3.15/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.98  --sup_immed_bw_main                     []
% 3.15/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/0.98  
% 3.15/0.98  ------ Combination Options
% 3.15/0.98  
% 3.15/0.98  --comb_res_mult                         3
% 3.15/0.98  --comb_sup_mult                         2
% 3.15/0.98  --comb_inst_mult                        10
% 3.15/0.98  
% 3.15/0.98  ------ Debug Options
% 3.15/0.98  
% 3.15/0.98  --dbg_backtrace                         false
% 3.15/0.98  --dbg_dump_prop_clauses                 false
% 3.15/0.98  --dbg_dump_prop_clauses_file            -
% 3.15/0.98  --dbg_out_stat                          false
% 3.15/0.98  ------ Parsing...
% 3.15/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.15/0.98  
% 3.15/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.15/0.98  
% 3.15/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.15/0.98  
% 3.15/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.15/0.98  ------ Proving...
% 3.15/0.98  ------ Problem Properties 
% 3.15/0.98  
% 3.15/0.98  
% 3.15/0.98  clauses                                 27
% 3.15/0.98  conjectures                             7
% 3.15/0.99  EPR                                     6
% 3.15/0.99  Horn                                    24
% 3.15/0.99  unary                                   10
% 3.15/0.99  binary                                  6
% 3.15/0.99  lits                                    61
% 3.15/0.99  lits eq                                 22
% 3.15/0.99  fd_pure                                 0
% 3.15/0.99  fd_pseudo                               0
% 3.15/0.99  fd_cond                                 0
% 3.15/0.99  fd_pseudo_cond                          1
% 3.15/0.99  AC symbols                              0
% 3.15/0.99  
% 3.15/0.99  ------ Schedule dynamic 5 is on 
% 3.15/0.99  
% 3.15/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  ------ 
% 3.15/0.99  Current options:
% 3.15/0.99  ------ 
% 3.15/0.99  
% 3.15/0.99  ------ Input Options
% 3.15/0.99  
% 3.15/0.99  --out_options                           all
% 3.15/0.99  --tptp_safe_out                         true
% 3.15/0.99  --problem_path                          ""
% 3.15/0.99  --include_path                          ""
% 3.15/0.99  --clausifier                            res/vclausify_rel
% 3.15/0.99  --clausifier_options                    --mode clausify
% 3.15/0.99  --stdin                                 false
% 3.15/0.99  --stats_out                             all
% 3.15/0.99  
% 3.15/0.99  ------ General Options
% 3.15/0.99  
% 3.15/0.99  --fof                                   false
% 3.15/0.99  --time_out_real                         305.
% 3.15/0.99  --time_out_virtual                      -1.
% 3.15/0.99  --symbol_type_check                     false
% 3.15/0.99  --clausify_out                          false
% 3.15/0.99  --sig_cnt_out                           false
% 3.15/0.99  --trig_cnt_out                          false
% 3.15/0.99  --trig_cnt_out_tolerance                1.
% 3.15/0.99  --trig_cnt_out_sk_spl                   false
% 3.15/0.99  --abstr_cl_out                          false
% 3.15/0.99  
% 3.15/0.99  ------ Global Options
% 3.15/0.99  
% 3.15/0.99  --schedule                              default
% 3.15/0.99  --add_important_lit                     false
% 3.15/0.99  --prop_solver_per_cl                    1000
% 3.15/0.99  --min_unsat_core                        false
% 3.15/0.99  --soft_assumptions                      false
% 3.15/0.99  --soft_lemma_size                       3
% 3.15/0.99  --prop_impl_unit_size                   0
% 3.15/0.99  --prop_impl_unit                        []
% 3.15/0.99  --share_sel_clauses                     true
% 3.15/0.99  --reset_solvers                         false
% 3.15/0.99  --bc_imp_inh                            [conj_cone]
% 3.15/0.99  --conj_cone_tolerance                   3.
% 3.15/0.99  --extra_neg_conj                        none
% 3.15/0.99  --large_theory_mode                     true
% 3.15/0.99  --prolific_symb_bound                   200
% 3.15/0.99  --lt_threshold                          2000
% 3.15/0.99  --clause_weak_htbl                      true
% 3.15/0.99  --gc_record_bc_elim                     false
% 3.15/0.99  
% 3.15/0.99  ------ Preprocessing Options
% 3.15/0.99  
% 3.15/0.99  --preprocessing_flag                    true
% 3.15/0.99  --time_out_prep_mult                    0.1
% 3.15/0.99  --splitting_mode                        input
% 3.15/0.99  --splitting_grd                         true
% 3.15/0.99  --splitting_cvd                         false
% 3.15/0.99  --splitting_cvd_svl                     false
% 3.15/0.99  --splitting_nvd                         32
% 3.15/0.99  --sub_typing                            true
% 3.15/0.99  --prep_gs_sim                           true
% 3.15/0.99  --prep_unflatten                        true
% 3.15/0.99  --prep_res_sim                          true
% 3.15/0.99  --prep_upred                            true
% 3.15/0.99  --prep_sem_filter                       exhaustive
% 3.15/0.99  --prep_sem_filter_out                   false
% 3.15/0.99  --pred_elim                             true
% 3.15/0.99  --res_sim_input                         true
% 3.15/0.99  --eq_ax_congr_red                       true
% 3.15/0.99  --pure_diseq_elim                       true
% 3.15/0.99  --brand_transform                       false
% 3.15/0.99  --non_eq_to_eq                          false
% 3.15/0.99  --prep_def_merge                        true
% 3.15/0.99  --prep_def_merge_prop_impl              false
% 3.15/0.99  --prep_def_merge_mbd                    true
% 3.15/0.99  --prep_def_merge_tr_red                 false
% 3.15/0.99  --prep_def_merge_tr_cl                  false
% 3.15/0.99  --smt_preprocessing                     true
% 3.15/0.99  --smt_ac_axioms                         fast
% 3.15/0.99  --preprocessed_out                      false
% 3.15/0.99  --preprocessed_stats                    false
% 3.15/0.99  
% 3.15/0.99  ------ Abstraction refinement Options
% 3.15/0.99  
% 3.15/0.99  --abstr_ref                             []
% 3.15/0.99  --abstr_ref_prep                        false
% 3.15/0.99  --abstr_ref_until_sat                   false
% 3.15/0.99  --abstr_ref_sig_restrict                funpre
% 3.15/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/0.99  --abstr_ref_under                       []
% 3.15/0.99  
% 3.15/0.99  ------ SAT Options
% 3.15/0.99  
% 3.15/0.99  --sat_mode                              false
% 3.15/0.99  --sat_fm_restart_options                ""
% 3.15/0.99  --sat_gr_def                            false
% 3.15/0.99  --sat_epr_types                         true
% 3.15/0.99  --sat_non_cyclic_types                  false
% 3.15/0.99  --sat_finite_models                     false
% 3.15/0.99  --sat_fm_lemmas                         false
% 3.15/0.99  --sat_fm_prep                           false
% 3.15/0.99  --sat_fm_uc_incr                        true
% 3.15/0.99  --sat_out_model                         small
% 3.15/0.99  --sat_out_clauses                       false
% 3.15/0.99  
% 3.15/0.99  ------ QBF Options
% 3.15/0.99  
% 3.15/0.99  --qbf_mode                              false
% 3.15/0.99  --qbf_elim_univ                         false
% 3.15/0.99  --qbf_dom_inst                          none
% 3.15/0.99  --qbf_dom_pre_inst                      false
% 3.15/0.99  --qbf_sk_in                             false
% 3.15/0.99  --qbf_pred_elim                         true
% 3.15/0.99  --qbf_split                             512
% 3.15/0.99  
% 3.15/0.99  ------ BMC1 Options
% 3.15/0.99  
% 3.15/0.99  --bmc1_incremental                      false
% 3.15/0.99  --bmc1_axioms                           reachable_all
% 3.15/0.99  --bmc1_min_bound                        0
% 3.15/0.99  --bmc1_max_bound                        -1
% 3.15/0.99  --bmc1_max_bound_default                -1
% 3.15/0.99  --bmc1_symbol_reachability              true
% 3.15/0.99  --bmc1_property_lemmas                  false
% 3.15/0.99  --bmc1_k_induction                      false
% 3.15/0.99  --bmc1_non_equiv_states                 false
% 3.15/0.99  --bmc1_deadlock                         false
% 3.15/0.99  --bmc1_ucm                              false
% 3.15/0.99  --bmc1_add_unsat_core                   none
% 3.15/0.99  --bmc1_unsat_core_children              false
% 3.15/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/0.99  --bmc1_out_stat                         full
% 3.15/0.99  --bmc1_ground_init                      false
% 3.15/0.99  --bmc1_pre_inst_next_state              false
% 3.15/0.99  --bmc1_pre_inst_state                   false
% 3.15/0.99  --bmc1_pre_inst_reach_state             false
% 3.15/0.99  --bmc1_out_unsat_core                   false
% 3.15/0.99  --bmc1_aig_witness_out                  false
% 3.15/0.99  --bmc1_verbose                          false
% 3.15/0.99  --bmc1_dump_clauses_tptp                false
% 3.15/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.15/0.99  --bmc1_dump_file                        -
% 3.15/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.15/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.15/0.99  --bmc1_ucm_extend_mode                  1
% 3.15/0.99  --bmc1_ucm_init_mode                    2
% 3.15/0.99  --bmc1_ucm_cone_mode                    none
% 3.15/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.15/0.99  --bmc1_ucm_relax_model                  4
% 3.15/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.15/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/0.99  --bmc1_ucm_layered_model                none
% 3.15/0.99  --bmc1_ucm_max_lemma_size               10
% 3.15/0.99  
% 3.15/0.99  ------ AIG Options
% 3.15/0.99  
% 3.15/0.99  --aig_mode                              false
% 3.15/0.99  
% 3.15/0.99  ------ Instantiation Options
% 3.15/0.99  
% 3.15/0.99  --instantiation_flag                    true
% 3.15/0.99  --inst_sos_flag                         false
% 3.15/0.99  --inst_sos_phase                        true
% 3.15/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/0.99  --inst_lit_sel_side                     none
% 3.15/0.99  --inst_solver_per_active                1400
% 3.15/0.99  --inst_solver_calls_frac                1.
% 3.15/0.99  --inst_passive_queue_type               priority_queues
% 3.15/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/0.99  --inst_passive_queues_freq              [25;2]
% 3.15/0.99  --inst_dismatching                      true
% 3.15/0.99  --inst_eager_unprocessed_to_passive     true
% 3.15/0.99  --inst_prop_sim_given                   true
% 3.15/0.99  --inst_prop_sim_new                     false
% 3.15/0.99  --inst_subs_new                         false
% 3.15/0.99  --inst_eq_res_simp                      false
% 3.15/0.99  --inst_subs_given                       false
% 3.15/0.99  --inst_orphan_elimination               true
% 3.15/0.99  --inst_learning_loop_flag               true
% 3.15/0.99  --inst_learning_start                   3000
% 3.15/0.99  --inst_learning_factor                  2
% 3.15/0.99  --inst_start_prop_sim_after_learn       3
% 3.15/0.99  --inst_sel_renew                        solver
% 3.15/0.99  --inst_lit_activity_flag                true
% 3.15/0.99  --inst_restr_to_given                   false
% 3.15/0.99  --inst_activity_threshold               500
% 3.15/0.99  --inst_out_proof                        true
% 3.15/0.99  
% 3.15/0.99  ------ Resolution Options
% 3.15/0.99  
% 3.15/0.99  --resolution_flag                       false
% 3.15/0.99  --res_lit_sel                           adaptive
% 3.15/0.99  --res_lit_sel_side                      none
% 3.15/0.99  --res_ordering                          kbo
% 3.15/0.99  --res_to_prop_solver                    active
% 3.15/0.99  --res_prop_simpl_new                    false
% 3.15/0.99  --res_prop_simpl_given                  true
% 3.15/0.99  --res_passive_queue_type                priority_queues
% 3.15/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/0.99  --res_passive_queues_freq               [15;5]
% 3.15/0.99  --res_forward_subs                      full
% 3.15/0.99  --res_backward_subs                     full
% 3.15/0.99  --res_forward_subs_resolution           true
% 3.15/0.99  --res_backward_subs_resolution          true
% 3.15/0.99  --res_orphan_elimination                true
% 3.15/0.99  --res_time_limit                        2.
% 3.15/0.99  --res_out_proof                         true
% 3.15/0.99  
% 3.15/0.99  ------ Superposition Options
% 3.15/0.99  
% 3.15/0.99  --superposition_flag                    true
% 3.15/0.99  --sup_passive_queue_type                priority_queues
% 3.15/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.15/0.99  --demod_completeness_check              fast
% 3.15/0.99  --demod_use_ground                      true
% 3.15/0.99  --sup_to_prop_solver                    passive
% 3.15/0.99  --sup_prop_simpl_new                    true
% 3.15/0.99  --sup_prop_simpl_given                  true
% 3.15/0.99  --sup_fun_splitting                     false
% 3.15/0.99  --sup_smt_interval                      50000
% 3.15/0.99  
% 3.15/0.99  ------ Superposition Simplification Setup
% 3.15/0.99  
% 3.15/0.99  --sup_indices_passive                   []
% 3.15/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_full_bw                           [BwDemod]
% 3.15/0.99  --sup_immed_triv                        [TrivRules]
% 3.15/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_immed_bw_main                     []
% 3.15/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/0.99  
% 3.15/0.99  ------ Combination Options
% 3.15/0.99  
% 3.15/0.99  --comb_res_mult                         3
% 3.15/0.99  --comb_sup_mult                         2
% 3.15/0.99  --comb_inst_mult                        10
% 3.15/0.99  
% 3.15/0.99  ------ Debug Options
% 3.15/0.99  
% 3.15/0.99  --dbg_backtrace                         false
% 3.15/0.99  --dbg_dump_prop_clauses                 false
% 3.15/0.99  --dbg_dump_prop_clauses_file            -
% 3.15/0.99  --dbg_out_stat                          false
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  ------ Proving...
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  % SZS status Theorem for theBenchmark.p
% 3.15/0.99  
% 3.15/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.15/0.99  
% 3.15/0.99  fof(f14,conjecture,(
% 3.15/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f15,negated_conjecture,(
% 3.15/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.15/0.99    inference(negated_conjecture,[],[f14])).
% 3.15/0.99  
% 3.15/0.99  fof(f31,plain,(
% 3.15/0.99    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.15/0.99    inference(ennf_transformation,[],[f15])).
% 3.15/0.99  
% 3.15/0.99  fof(f32,plain,(
% 3.15/0.99    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.15/0.99    inference(flattening,[],[f31])).
% 3.15/0.99  
% 3.15/0.99  fof(f38,plain,(
% 3.15/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.15/0.99    introduced(choice_axiom,[])).
% 3.15/0.99  
% 3.15/0.99  fof(f37,plain,(
% 3.15/0.99    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.15/0.99    introduced(choice_axiom,[])).
% 3.15/0.99  
% 3.15/0.99  fof(f39,plain,(
% 3.15/0.99    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.15/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f38,f37])).
% 3.15/0.99  
% 3.15/0.99  fof(f63,plain,(
% 3.15/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f66,plain,(
% 3.15/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f8,axiom,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f21,plain,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.15/0.99    inference(ennf_transformation,[],[f8])).
% 3.15/0.99  
% 3.15/0.99  fof(f22,plain,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(flattening,[],[f21])).
% 3.15/0.99  
% 3.15/0.99  fof(f50,plain,(
% 3.15/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f22])).
% 3.15/0.99  
% 3.15/0.99  fof(f10,axiom,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f24,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(ennf_transformation,[],[f10])).
% 3.15/0.99  
% 3.15/0.99  fof(f52,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f24])).
% 3.15/0.99  
% 3.15/0.99  fof(f11,axiom,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f25,plain,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.15/0.99    inference(ennf_transformation,[],[f11])).
% 3.15/0.99  
% 3.15/0.99  fof(f26,plain,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(flattening,[],[f25])).
% 3.15/0.99  
% 3.15/0.99  fof(f53,plain,(
% 3.15/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f26])).
% 3.15/0.99  
% 3.15/0.99  fof(f13,axiom,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f29,plain,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.15/0.99    inference(ennf_transformation,[],[f13])).
% 3.15/0.99  
% 3.15/0.99  fof(f30,plain,(
% 3.15/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.15/0.99    inference(flattening,[],[f29])).
% 3.15/0.99  
% 3.15/0.99  fof(f60,plain,(
% 3.15/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f30])).
% 3.15/0.99  
% 3.15/0.99  fof(f64,plain,(
% 3.15/0.99    v1_funct_1(sK4)),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f61,plain,(
% 3.15/0.99    v1_funct_1(sK3)),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f67,plain,(
% 3.15/0.99    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f9,axiom,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f23,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(ennf_transformation,[],[f9])).
% 3.15/0.99  
% 3.15/0.99  fof(f51,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f23])).
% 3.15/0.99  
% 3.15/0.99  fof(f12,axiom,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f27,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(ennf_transformation,[],[f12])).
% 3.15/0.99  
% 3.15/0.99  fof(f28,plain,(
% 3.15/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(flattening,[],[f27])).
% 3.15/0.99  
% 3.15/0.99  fof(f36,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(nnf_transformation,[],[f28])).
% 3.15/0.99  
% 3.15/0.99  fof(f54,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f36])).
% 3.15/0.99  
% 3.15/0.99  fof(f65,plain,(
% 3.15/0.99    v1_funct_2(sK4,sK1,sK2)),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f69,plain,(
% 3.15/0.99    k1_xboole_0 != sK2),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f6,axiom,(
% 3.15/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f18,plain,(
% 3.15/0.99    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/0.99    inference(ennf_transformation,[],[f6])).
% 3.15/0.99  
% 3.15/0.99  fof(f19,plain,(
% 3.15/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/0.99    inference(flattening,[],[f18])).
% 3.15/0.99  
% 3.15/0.99  fof(f48,plain,(
% 3.15/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f19])).
% 3.15/0.99  
% 3.15/0.99  fof(f68,plain,(
% 3.15/0.99    v2_funct_1(sK4)),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f2,axiom,(
% 3.15/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f35,plain,(
% 3.15/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.15/0.99    inference(nnf_transformation,[],[f2])).
% 3.15/0.99  
% 3.15/0.99  fof(f43,plain,(
% 3.15/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f35])).
% 3.15/0.99  
% 3.15/0.99  fof(f3,axiom,(
% 3.15/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f16,plain,(
% 3.15/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.15/0.99    inference(ennf_transformation,[],[f3])).
% 3.15/0.99  
% 3.15/0.99  fof(f45,plain,(
% 3.15/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f16])).
% 3.15/0.99  
% 3.15/0.99  fof(f44,plain,(
% 3.15/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f35])).
% 3.15/0.99  
% 3.15/0.99  fof(f4,axiom,(
% 3.15/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f46,plain,(
% 3.15/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f4])).
% 3.15/0.99  
% 3.15/0.99  fof(f5,axiom,(
% 3.15/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f17,plain,(
% 3.15/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.15/0.99    inference(ennf_transformation,[],[f5])).
% 3.15/0.99  
% 3.15/0.99  fof(f47,plain,(
% 3.15/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f17])).
% 3.15/0.99  
% 3.15/0.99  fof(f7,axiom,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f20,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(ennf_transformation,[],[f7])).
% 3.15/0.99  
% 3.15/0.99  fof(f49,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f20])).
% 3.15/0.99  
% 3.15/0.99  fof(f1,axiom,(
% 3.15/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.15/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f33,plain,(
% 3.15/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.15/0.99    inference(nnf_transformation,[],[f1])).
% 3.15/0.99  
% 3.15/0.99  fof(f34,plain,(
% 3.15/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.15/0.99    inference(flattening,[],[f33])).
% 3.15/0.99  
% 3.15/0.99  fof(f42,plain,(
% 3.15/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f34])).
% 3.15/0.99  
% 3.15/0.99  fof(f70,plain,(
% 3.15/0.99    k2_relset_1(sK0,sK1,sK3) != sK1),
% 3.15/0.99    inference(cnf_transformation,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  cnf(c_28,negated_conjecture,
% 3.15/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.15/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1283,plain,
% 3.15/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_25,negated_conjecture,
% 3.15/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.15/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1285,plain,
% 3.15/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_10,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.15/0.99      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.15/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1290,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.15/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.15/0.99      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_12,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1288,plain,
% 3.15/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2289,plain,
% 3.15/0.99      ( k2_relset_1(X0,X1,k4_relset_1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k4_relset_1(X0,X2,X3,X1,X4,X5))
% 3.15/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.15/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1290,c_1288]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5270,plain,
% 3.15/0.99      ( k2_relset_1(X0,sK2,k4_relset_1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k4_relset_1(X0,X1,sK1,sK2,X2,sK4))
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1285,c_2289]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5368,plain,
% 3.15/0.99      ( k2_relset_1(sK0,sK2,k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1283,c_5270]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_13,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.15/0.99      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1287,plain,
% 3.15/0.99      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.15/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.15/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3441,plain,
% 3.15/0.99      ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1285,c_1287]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3835,plain,
% 3.15/0.99      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1283,c_3441]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_20,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X3)
% 3.15/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1286,plain,
% 3.15/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.15/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.15/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.15/0.99      | v1_funct_1(X5) != iProver_top
% 3.15/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3625,plain,
% 3.15/0.99      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.15/0.99      | v1_funct_1(X2) != iProver_top
% 3.15/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1285,c_1286]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_27,negated_conjecture,
% 3.15/0.99      ( v1_funct_1(sK4) ),
% 3.15/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_34,plain,
% 3.15/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_4579,plain,
% 3.15/0.99      ( v1_funct_1(X2) != iProver_top
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.15/0.99      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_3625,c_34]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_4580,plain,
% 3.15/0.99      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.15/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.15/0.99      inference(renaming,[status(thm)],[c_4579]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_4592,plain,
% 3.15/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.15/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1283,c_4580]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_30,negated_conjecture,
% 3.15/0.99      ( v1_funct_1(sK3) ),
% 3.15/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1563,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | ~ v1_funct_1(sK4)
% 3.15/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1702,plain,
% 3.15/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.15/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.15/0.99      | ~ v1_funct_1(sK4)
% 3.15/0.99      | ~ v1_funct_1(sK3)
% 3.15/0.99      | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_1563]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2160,plain,
% 3.15/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.15/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.15/0.99      | ~ v1_funct_1(sK4)
% 3.15/0.99      | ~ v1_funct_1(sK3)
% 3.15/0.99      | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_1702]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3312,plain,
% 3.15/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.15/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.15/0.99      | ~ v1_funct_1(sK4)
% 3.15/0.99      | ~ v1_funct_1(sK3)
% 3.15/0.99      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_2160]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5122,plain,
% 3.15/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_4592,c_30,c_28,c_27,c_25,c_3312]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_24,negated_conjecture,
% 3.15/0.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.15/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5127,plain,
% 3.15/0.99      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_5122,c_24]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5370,plain,
% 3.15/0.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.15/0.99      inference(light_normalisation,[status(thm)],[c_5368,c_3835,c_5127]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_11,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1289,plain,
% 3.15/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2395,plain,
% 3.15/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1285,c_1289]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_19,plain,
% 3.15/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.15/0.99      | k1_xboole_0 = X2 ),
% 3.15/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_26,negated_conjecture,
% 3.15/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.15/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_475,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.15/0.99      | sK4 != X0
% 3.15/0.99      | sK2 != X2
% 3.15/0.99      | sK1 != X1
% 3.15/0.99      | k1_xboole_0 = X2 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_476,plain,
% 3.15/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.15/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.15/0.99      | k1_xboole_0 = sK2 ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_475]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_22,negated_conjecture,
% 3.15/0.99      ( k1_xboole_0 != sK2 ),
% 3.15/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_478,plain,
% 3.15/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_476,c_25,c_22]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2400,plain,
% 3.15/0.99      ( k1_relat_1(sK4) = sK1 ),
% 3.15/0.99      inference(light_normalisation,[status(thm)],[c_2395,c_478]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_8,plain,
% 3.15/0.99      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 3.15/0.99      | ~ v1_funct_1(X1)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | ~ v2_funct_1(X0)
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_relat_1(X1)
% 3.15/0.99      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_23,negated_conjecture,
% 3.15/0.99      ( v2_funct_1(sK4) ),
% 3.15/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_368,plain,
% 3.15/0.99      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 3.15/0.99      | ~ v1_funct_1(X1)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_relat_1(X1)
% 3.15/0.99      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
% 3.15/0.99      | sK4 != X0 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_369,plain,
% 3.15/0.99      ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | ~ v1_funct_1(sK4)
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_relat_1(sK4)
% 3.15/0.99      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_373,plain,
% 3.15/0.99      ( ~ v1_funct_1(X0)
% 3.15/0.99      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_relat_1(sK4)
% 3.15/0.99      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_369,c_27]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_374,plain,
% 3.15/0.99      ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_relat_1(sK4)
% 3.15/0.99      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 3.15/0.99      inference(renaming,[status(thm)],[c_373]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1280,plain,
% 3.15/0.99      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 3.15/0.99      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 3.15/0.99      | v1_funct_1(X0) != iProver_top
% 3.15/0.99      | v1_relat_1(X0) != iProver_top
% 3.15/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2818,plain,
% 3.15/0.99      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 3.15/0.99      | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
% 3.15/0.99      | v1_funct_1(X0) != iProver_top
% 3.15/0.99      | v1_relat_1(X0) != iProver_top
% 3.15/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_2400,c_1280]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_4,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.15/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1294,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.15/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1712,plain,
% 3.15/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1285,c_1294]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.15/0.99      | ~ v1_relat_1(X1)
% 3.15/0.99      | v1_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.15/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_215,plain,
% 3.15/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.15/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_216,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.15/0.99      inference(renaming,[status(thm)],[c_215]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_271,plain,
% 3.15/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.15/0.99      inference(bin_hyper_res,[status(thm)],[c_5,c_216]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1573,plain,
% 3.15/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.15/0.99      | v1_relat_1(X0)
% 3.15/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_271]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2145,plain,
% 3.15/0.99      ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
% 3.15/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 3.15/0.99      | v1_relat_1(sK4) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_1573]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2147,plain,
% 3.15/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.15/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.15/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_2145]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6,plain,
% 3.15/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.15/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3726,plain,
% 3.15/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3727,plain,
% 3.15/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_3726]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6715,plain,
% 3.15/0.99      ( v1_relat_1(X0) != iProver_top
% 3.15/0.99      | v1_funct_1(X0) != iProver_top
% 3.15/0.99      | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
% 3.15/0.99      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_2818,c_1712,c_2147,c_3727]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6716,plain,
% 3.15/0.99      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 3.15/0.99      | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
% 3.15/0.99      | v1_funct_1(X0) != iProver_top
% 3.15/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.15/0.99      inference(renaming,[status(thm)],[c_6715]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6725,plain,
% 3.15/0.99      ( k2_relat_1(sK4) != sK2
% 3.15/0.99      | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top
% 3.15/0.99      | v1_funct_1(sK3) != iProver_top
% 3.15/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_5370,c_6716]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_7,plain,
% 3.15/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_relat_1(X1) ),
% 3.15/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1292,plain,
% 3.15/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.15/0.99      | v1_relat_1(X0) != iProver_top
% 3.15/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5399,plain,
% 3.15/0.99      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 3.15/0.99      | v1_relat_1(sK4) != iProver_top
% 3.15/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_5370,c_1292]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2291,plain,
% 3.15/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1283,c_1288]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_9,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.15/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1291,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.15/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2852,plain,
% 3.15/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 3.15/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_2291,c_1291]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_33,plain,
% 3.15/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5256,plain,
% 3.15/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_2852,c_33]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5261,plain,
% 3.15/0.99      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_5256,c_1294]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_0,plain,
% 3.15/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.15/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1297,plain,
% 3.15/0.99      ( X0 = X1
% 3.15/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.15/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5326,plain,
% 3.15/0.99      ( k2_relat_1(sK3) = sK1
% 3.15/0.99      | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_5261,c_1297]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2290,plain,
% 3.15/0.99      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1285,c_1288]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2823,plain,
% 3.15/0.99      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 3.15/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_2290,c_1291]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_36,plain,
% 3.15/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5226,plain,
% 3.15/0.99      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_2823,c_36]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5231,plain,
% 3.15/0.99      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_5226,c_1294]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5322,plain,
% 3.15/0.99      ( k2_relat_1(sK4) = sK2
% 3.15/0.99      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_5231,c_1297]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3730,plain,
% 3.15/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3731,plain,
% 3.15/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_3730]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_21,negated_conjecture,
% 3.15/0.99      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.15/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2851,plain,
% 3.15/0.99      ( k2_relat_1(sK3) != sK1 ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_2291,c_21]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2149,plain,
% 3.15/0.99      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 3.15/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.15/0.99      | v1_relat_1(sK3) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_1573]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2151,plain,
% 3.15/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.15/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.15/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_2149]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1713,plain,
% 3.15/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1283,c_1294]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_31,plain,
% 3.15/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(contradiction,plain,
% 3.15/0.99      ( $false ),
% 3.15/0.99      inference(minisat,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_6725,c_5399,c_5326,c_5322,c_3731,c_3727,c_2851,c_2151,
% 3.15/0.99                 c_2147,c_1713,c_1712,c_31]) ).
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.15/0.99  
% 3.15/0.99  ------                               Statistics
% 3.15/0.99  
% 3.15/0.99  ------ General
% 3.15/0.99  
% 3.15/0.99  abstr_ref_over_cycles:                  0
% 3.15/0.99  abstr_ref_under_cycles:                 0
% 3.15/0.99  gc_basic_clause_elim:                   0
% 3.15/0.99  forced_gc_time:                         0
% 3.15/0.99  parsing_time:                           0.01
% 3.15/0.99  unif_index_cands_time:                  0.
% 3.15/0.99  unif_index_add_time:                    0.
% 3.15/0.99  orderings_time:                         0.
% 3.15/0.99  out_proof_time:                         0.01
% 3.15/0.99  total_time:                             0.225
% 3.15/0.99  num_of_symbols:                         52
% 3.15/0.99  num_of_terms:                           6799
% 3.15/0.99  
% 3.15/0.99  ------ Preprocessing
% 3.15/0.99  
% 3.15/0.99  num_of_splits:                          0
% 3.15/0.99  num_of_split_atoms:                     0
% 3.15/0.99  num_of_reused_defs:                     0
% 3.15/0.99  num_eq_ax_congr_red:                    25
% 3.15/0.99  num_of_sem_filtered_clauses:            1
% 3.15/0.99  num_of_subtypes:                        0
% 3.15/0.99  monotx_restored_types:                  0
% 3.15/0.99  sat_num_of_epr_types:                   0
% 3.15/0.99  sat_num_of_non_cyclic_types:            0
% 3.15/0.99  sat_guarded_non_collapsed_types:        0
% 3.15/0.99  num_pure_diseq_elim:                    0
% 3.15/0.99  simp_replaced_by:                       0
% 3.15/0.99  res_preprocessed:                       140
% 3.15/0.99  prep_upred:                             0
% 3.15/0.99  prep_unflattend:                        35
% 3.15/0.99  smt_new_axioms:                         0
% 3.15/0.99  pred_elim_cands:                        4
% 3.15/0.99  pred_elim:                              2
% 3.15/0.99  pred_elim_cl:                           3
% 3.15/0.99  pred_elim_cycles:                       4
% 3.15/0.99  merged_defs:                            8
% 3.15/0.99  merged_defs_ncl:                        0
% 3.15/0.99  bin_hyper_res:                          9
% 3.15/0.99  prep_cycles:                            4
% 3.15/0.99  pred_elim_time:                         0.004
% 3.15/0.99  splitting_time:                         0.
% 3.15/0.99  sem_filter_time:                        0.
% 3.15/0.99  monotx_time:                            0.001
% 3.15/0.99  subtype_inf_time:                       0.
% 3.15/0.99  
% 3.15/0.99  ------ Problem properties
% 3.15/0.99  
% 3.15/0.99  clauses:                                27
% 3.15/0.99  conjectures:                            7
% 3.15/0.99  epr:                                    6
% 3.15/0.99  horn:                                   24
% 3.15/0.99  ground:                                 13
% 3.15/0.99  unary:                                  10
% 3.15/0.99  binary:                                 6
% 3.15/0.99  lits:                                   61
% 3.15/0.99  lits_eq:                                22
% 3.15/0.99  fd_pure:                                0
% 3.15/0.99  fd_pseudo:                              0
% 3.15/0.99  fd_cond:                                0
% 3.15/0.99  fd_pseudo_cond:                         1
% 3.15/0.99  ac_symbols:                             0
% 3.15/0.99  
% 3.15/0.99  ------ Propositional Solver
% 3.15/0.99  
% 3.15/0.99  prop_solver_calls:                      28
% 3.15/0.99  prop_fast_solver_calls:                 950
% 3.15/0.99  smt_solver_calls:                       0
% 3.15/0.99  smt_fast_solver_calls:                  0
% 3.15/0.99  prop_num_of_clauses:                    2608
% 3.15/0.99  prop_preprocess_simplified:             6780
% 3.15/0.99  prop_fo_subsumed:                       27
% 3.15/0.99  prop_solver_time:                       0.
% 3.15/0.99  smt_solver_time:                        0.
% 3.15/0.99  smt_fast_solver_time:                   0.
% 3.15/0.99  prop_fast_solver_time:                  0.
% 3.15/0.99  prop_unsat_core_time:                   0.
% 3.15/0.99  
% 3.15/0.99  ------ QBF
% 3.15/0.99  
% 3.15/0.99  qbf_q_res:                              0
% 3.15/0.99  qbf_num_tautologies:                    0
% 3.15/0.99  qbf_prep_cycles:                        0
% 3.15/0.99  
% 3.15/0.99  ------ BMC1
% 3.15/0.99  
% 3.15/0.99  bmc1_current_bound:                     -1
% 3.15/0.99  bmc1_last_solved_bound:                 -1
% 3.15/0.99  bmc1_unsat_core_size:                   -1
% 3.15/0.99  bmc1_unsat_core_parents_size:           -1
% 3.15/0.99  bmc1_merge_next_fun:                    0
% 3.15/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.15/0.99  
% 3.15/0.99  ------ Instantiation
% 3.15/0.99  
% 3.15/0.99  inst_num_of_clauses:                    776
% 3.15/0.99  inst_num_in_passive:                    202
% 3.15/0.99  inst_num_in_active:                     510
% 3.15/0.99  inst_num_in_unprocessed:                64
% 3.15/0.99  inst_num_of_loops:                      550
% 3.15/0.99  inst_num_of_learning_restarts:          0
% 3.15/0.99  inst_num_moves_active_passive:          38
% 3.15/0.99  inst_lit_activity:                      0
% 3.15/0.99  inst_lit_activity_moves:                1
% 3.15/0.99  inst_num_tautologies:                   0
% 3.15/0.99  inst_num_prop_implied:                  0
% 3.15/0.99  inst_num_existing_simplified:           0
% 3.15/0.99  inst_num_eq_res_simplified:             0
% 3.15/0.99  inst_num_child_elim:                    0
% 3.15/0.99  inst_num_of_dismatching_blockings:      215
% 3.15/0.99  inst_num_of_non_proper_insts:           574
% 3.15/0.99  inst_num_of_duplicates:                 0
% 3.15/0.99  inst_inst_num_from_inst_to_res:         0
% 3.15/0.99  inst_dismatching_checking_time:         0.
% 3.15/0.99  
% 3.15/0.99  ------ Resolution
% 3.15/0.99  
% 3.15/0.99  res_num_of_clauses:                     0
% 3.15/0.99  res_num_in_passive:                     0
% 3.15/0.99  res_num_in_active:                      0
% 3.15/0.99  res_num_of_loops:                       144
% 3.15/0.99  res_forward_subset_subsumed:            30
% 3.15/0.99  res_backward_subset_subsumed:           0
% 3.15/0.99  res_forward_subsumed:                   0
% 3.15/0.99  res_backward_subsumed:                  0
% 3.15/0.99  res_forward_subsumption_resolution:     0
% 3.15/0.99  res_backward_subsumption_resolution:    0
% 3.15/0.99  res_clause_to_clause_subsumption:       577
% 3.15/0.99  res_orphan_elimination:                 0
% 3.15/0.99  res_tautology_del:                      33
% 3.15/0.99  res_num_eq_res_simplified:              0
% 3.15/0.99  res_num_sel_changes:                    0
% 3.15/0.99  res_moves_from_active_to_pass:          0
% 3.15/0.99  
% 3.15/0.99  ------ Superposition
% 3.15/0.99  
% 3.15/0.99  sup_time_total:                         0.
% 3.15/0.99  sup_time_generating:                    0.
% 3.15/0.99  sup_time_sim_full:                      0.
% 3.15/0.99  sup_time_sim_immed:                     0.
% 3.15/0.99  
% 3.15/0.99  sup_num_of_clauses:                     221
% 3.15/0.99  sup_num_in_active:                      103
% 3.15/0.99  sup_num_in_passive:                     118
% 3.15/0.99  sup_num_of_loops:                       109
% 3.15/0.99  sup_fw_superposition:                   122
% 3.15/0.99  sup_bw_superposition:                   118
% 3.15/0.99  sup_immediate_simplified:               29
% 3.15/0.99  sup_given_eliminated:                   1
% 3.15/0.99  comparisons_done:                       0
% 3.15/0.99  comparisons_avoided:                    3
% 3.15/0.99  
% 3.15/0.99  ------ Simplifications
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  sim_fw_subset_subsumed:                 3
% 3.15/0.99  sim_bw_subset_subsumed:                 2
% 3.15/0.99  sim_fw_subsumed:                        2
% 3.15/0.99  sim_bw_subsumed:                        0
% 3.15/0.99  sim_fw_subsumption_res:                 0
% 3.15/0.99  sim_bw_subsumption_res:                 0
% 3.15/0.99  sim_tautology_del:                      2
% 3.15/0.99  sim_eq_tautology_del:                   1
% 3.15/0.99  sim_eq_res_simp:                        0
% 3.15/0.99  sim_fw_demodulated:                     0
% 3.15/0.99  sim_bw_demodulated:                     9
% 3.15/0.99  sim_light_normalised:                   21
% 3.15/0.99  sim_joinable_taut:                      0
% 3.15/0.99  sim_joinable_simp:                      0
% 3.15/0.99  sim_ac_normalised:                      0
% 3.15/0.99  sim_smt_subsumption:                    0
% 3.15/0.99  
%------------------------------------------------------------------------------
