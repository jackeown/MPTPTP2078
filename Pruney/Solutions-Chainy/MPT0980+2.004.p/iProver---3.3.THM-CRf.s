%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:37 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  167 (1835 expanded)
%              Number of clauses        :  116 ( 666 expanded)
%              Number of leaves         :   14 ( 426 expanded)
%              Depth                    :   25
%              Number of atoms          :  563 (12423 expanded)
%              Number of equality atoms :  281 (3351 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f26,plain,(
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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
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
           => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
             => ( v2_funct_1(X3)
                | ( k1_xboole_0 != X1
                  & k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( ~ v2_funct_1(X3)
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X2 )
        & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK4))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ v2_funct_1(X3)
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v2_funct_1(sK3)
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ v2_funct_1(sK3)
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f28,f27])).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f48,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f38])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_363,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_365,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_20])).

cnf(c_511,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_365])).

cnf(c_519,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_866,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_859,plain,
    ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_1246,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_866,c_859])).

cnf(c_1339,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_511,c_1246])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k5_relat_1(X3,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k1_relat_1(X2) != X1
    | k2_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_243,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_517,plain,
    ( ~ m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k5_relat_1(X0_48,X1_48))
    | ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_243])).

cnf(c_868,plain,
    ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X1_48))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,X1_48)) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_2140,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK3)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_868])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,negated_conjecture,
    ( ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,plain,
    ( v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48)
    | ~ v1_relat_1(k2_zfmisc_1(X1_48,X2_48)) ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_1198,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1199,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1198])).

cnf(c_534,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1041,plain,
    ( sK1 != X0_48
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0_48 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_1210,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_532,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1211,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_529,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1296,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_1297,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_521,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_864,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48) = k5_relat_1(X3_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_861,plain,
    ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X4_48,X5_48) = k5_relat_1(X4_48,X5_48)
    | m1_subset_1(X5_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X5_48) != iProver_top
    | v1_funct_1(X4_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1544,plain,
    ( k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_864,c_861])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1723,plain,
    ( v1_funct_1(X2_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1544,c_26])).

cnf(c_1724,plain,
    ( k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_1723])).

cnf(c_1733,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_1724])).

cnf(c_1080,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_48,X4_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1_48,X2_48,X3_48,X4_48,X0_48,sK4) = k5_relat_1(X0_48,sK4) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_1143,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2_48,X3_48,X0_48,X1_48,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_1172,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0_48,X1_48,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_1321,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_1875,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1733,c_22,c_20,c_19,c_17,c_1321])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_522,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_863,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_1878,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1875,c_863])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK4 != X0
    | sK2 != k1_xboole_0
    | sK1 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_290,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_516,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_869,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_552,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_523,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1335,plain,
    ( sK2 != X0_48
    | k1_xboole_0 != X0_48
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_1336,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_2165,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_552,c_523,c_1336])).

cnf(c_2166,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(renaming,[status(thm)],[c_2165])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_860,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_1255,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_866,c_860])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_858,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_1471,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_858])).

cnf(c_1673,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1471,c_25])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_352,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_354,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_17])).

cnf(c_512,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_1245,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_864,c_859])).

cnf(c_1319,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_512,c_1245])).

cnf(c_2043,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_868])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1195,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1196,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1195])).

cnf(c_1293,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_1294,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_2239,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | sK2 = k1_xboole_0
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2043,c_26,c_28,c_1196,c_1294])).

cnf(c_2240,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_2239])).

cnf(c_2251,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1673,c_2240])).

cnf(c_2254,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2140,c_23,c_25,c_30,c_1199,c_1210,c_1211,c_1297,c_1878,c_2166,c_2251])).

cnf(c_2270,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2254,c_1673])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK4 != X0
    | sK2 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_326,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_326])).

cnf(c_871,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_2272,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2254,c_871])).

cnf(c_2298,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2272])).

cnf(c_2276,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2254,c_1245])).

cnf(c_2299,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2298,c_2276])).

cnf(c_2280,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2254,c_864])).

cnf(c_2302,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2299,c_2280])).

cnf(c_2601,plain,
    ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2302,c_868])).

cnf(c_4256,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2601,c_26,c_28,c_1196,c_1294])).

cnf(c_4257,plain,
    ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4256])).

cnf(c_4267,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2270,c_4257])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4267,c_1878,c_1297,c_1199,c_30,c_25,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.55/1.08  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.08  
% 2.55/1.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.55/1.08  
% 2.55/1.08  ------  iProver source info
% 2.55/1.08  
% 2.55/1.08  git: date: 2020-06-30 10:37:57 +0100
% 2.55/1.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.55/1.08  git: non_committed_changes: false
% 2.55/1.08  git: last_make_outside_of_git: false
% 2.55/1.08  
% 2.55/1.08  ------ 
% 2.55/1.08  
% 2.55/1.08  ------ Input Options
% 2.55/1.08  
% 2.55/1.08  --out_options                           all
% 2.55/1.08  --tptp_safe_out                         true
% 2.55/1.08  --problem_path                          ""
% 2.55/1.08  --include_path                          ""
% 2.55/1.08  --clausifier                            res/vclausify_rel
% 2.55/1.08  --clausifier_options                    --mode clausify
% 2.55/1.08  --stdin                                 false
% 2.55/1.08  --stats_out                             all
% 2.55/1.08  
% 2.55/1.08  ------ General Options
% 2.55/1.08  
% 2.55/1.08  --fof                                   false
% 2.55/1.08  --time_out_real                         305.
% 2.55/1.08  --time_out_virtual                      -1.
% 2.55/1.08  --symbol_type_check                     false
% 2.55/1.08  --clausify_out                          false
% 2.55/1.08  --sig_cnt_out                           false
% 2.55/1.08  --trig_cnt_out                          false
% 2.55/1.08  --trig_cnt_out_tolerance                1.
% 2.55/1.08  --trig_cnt_out_sk_spl                   false
% 2.55/1.08  --abstr_cl_out                          false
% 2.55/1.08  
% 2.55/1.08  ------ Global Options
% 2.55/1.08  
% 2.55/1.08  --schedule                              default
% 2.55/1.08  --add_important_lit                     false
% 2.55/1.08  --prop_solver_per_cl                    1000
% 2.55/1.08  --min_unsat_core                        false
% 2.55/1.08  --soft_assumptions                      false
% 2.55/1.08  --soft_lemma_size                       3
% 2.55/1.08  --prop_impl_unit_size                   0
% 2.55/1.08  --prop_impl_unit                        []
% 2.55/1.08  --share_sel_clauses                     true
% 2.55/1.08  --reset_solvers                         false
% 2.55/1.08  --bc_imp_inh                            [conj_cone]
% 2.55/1.08  --conj_cone_tolerance                   3.
% 2.55/1.08  --extra_neg_conj                        none
% 2.55/1.08  --large_theory_mode                     true
% 2.55/1.08  --prolific_symb_bound                   200
% 2.55/1.08  --lt_threshold                          2000
% 2.55/1.08  --clause_weak_htbl                      true
% 2.55/1.08  --gc_record_bc_elim                     false
% 2.55/1.08  
% 2.55/1.08  ------ Preprocessing Options
% 2.55/1.08  
% 2.55/1.08  --preprocessing_flag                    true
% 2.55/1.08  --time_out_prep_mult                    0.1
% 2.55/1.08  --splitting_mode                        input
% 2.55/1.08  --splitting_grd                         true
% 2.55/1.08  --splitting_cvd                         false
% 2.55/1.08  --splitting_cvd_svl                     false
% 2.55/1.08  --splitting_nvd                         32
% 2.55/1.08  --sub_typing                            true
% 2.55/1.08  --prep_gs_sim                           true
% 2.55/1.08  --prep_unflatten                        true
% 2.55/1.08  --prep_res_sim                          true
% 2.55/1.08  --prep_upred                            true
% 2.55/1.08  --prep_sem_filter                       exhaustive
% 2.55/1.08  --prep_sem_filter_out                   false
% 2.55/1.08  --pred_elim                             true
% 2.55/1.08  --res_sim_input                         true
% 2.55/1.08  --eq_ax_congr_red                       true
% 2.55/1.08  --pure_diseq_elim                       true
% 2.55/1.08  --brand_transform                       false
% 2.55/1.08  --non_eq_to_eq                          false
% 2.55/1.08  --prep_def_merge                        true
% 2.55/1.08  --prep_def_merge_prop_impl              false
% 2.55/1.08  --prep_def_merge_mbd                    true
% 2.55/1.08  --prep_def_merge_tr_red                 false
% 2.55/1.08  --prep_def_merge_tr_cl                  false
% 2.55/1.08  --smt_preprocessing                     true
% 2.55/1.08  --smt_ac_axioms                         fast
% 2.55/1.08  --preprocessed_out                      false
% 2.55/1.08  --preprocessed_stats                    false
% 2.55/1.08  
% 2.55/1.08  ------ Abstraction refinement Options
% 2.55/1.08  
% 2.55/1.08  --abstr_ref                             []
% 2.55/1.08  --abstr_ref_prep                        false
% 2.55/1.08  --abstr_ref_until_sat                   false
% 2.55/1.08  --abstr_ref_sig_restrict                funpre
% 2.55/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/1.08  --abstr_ref_under                       []
% 2.55/1.08  
% 2.55/1.08  ------ SAT Options
% 2.55/1.08  
% 2.55/1.08  --sat_mode                              false
% 2.55/1.08  --sat_fm_restart_options                ""
% 2.55/1.08  --sat_gr_def                            false
% 2.55/1.08  --sat_epr_types                         true
% 2.55/1.08  --sat_non_cyclic_types                  false
% 2.55/1.08  --sat_finite_models                     false
% 2.55/1.08  --sat_fm_lemmas                         false
% 2.55/1.08  --sat_fm_prep                           false
% 2.55/1.08  --sat_fm_uc_incr                        true
% 2.55/1.08  --sat_out_model                         small
% 2.55/1.08  --sat_out_clauses                       false
% 2.55/1.08  
% 2.55/1.08  ------ QBF Options
% 2.55/1.08  
% 2.55/1.08  --qbf_mode                              false
% 2.55/1.08  --qbf_elim_univ                         false
% 2.55/1.08  --qbf_dom_inst                          none
% 2.55/1.08  --qbf_dom_pre_inst                      false
% 2.55/1.08  --qbf_sk_in                             false
% 2.55/1.08  --qbf_pred_elim                         true
% 2.55/1.08  --qbf_split                             512
% 2.55/1.08  
% 2.55/1.08  ------ BMC1 Options
% 2.55/1.08  
% 2.55/1.08  --bmc1_incremental                      false
% 2.55/1.08  --bmc1_axioms                           reachable_all
% 2.55/1.08  --bmc1_min_bound                        0
% 2.55/1.08  --bmc1_max_bound                        -1
% 2.55/1.08  --bmc1_max_bound_default                -1
% 2.55/1.08  --bmc1_symbol_reachability              true
% 2.55/1.08  --bmc1_property_lemmas                  false
% 2.55/1.08  --bmc1_k_induction                      false
% 2.55/1.08  --bmc1_non_equiv_states                 false
% 2.55/1.08  --bmc1_deadlock                         false
% 2.55/1.08  --bmc1_ucm                              false
% 2.55/1.08  --bmc1_add_unsat_core                   none
% 2.55/1.08  --bmc1_unsat_core_children              false
% 2.55/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/1.08  --bmc1_out_stat                         full
% 2.55/1.08  --bmc1_ground_init                      false
% 2.55/1.08  --bmc1_pre_inst_next_state              false
% 2.55/1.08  --bmc1_pre_inst_state                   false
% 2.55/1.08  --bmc1_pre_inst_reach_state             false
% 2.55/1.08  --bmc1_out_unsat_core                   false
% 2.55/1.08  --bmc1_aig_witness_out                  false
% 2.55/1.08  --bmc1_verbose                          false
% 2.55/1.08  --bmc1_dump_clauses_tptp                false
% 2.55/1.08  --bmc1_dump_unsat_core_tptp             false
% 2.55/1.08  --bmc1_dump_file                        -
% 2.55/1.08  --bmc1_ucm_expand_uc_limit              128
% 2.55/1.08  --bmc1_ucm_n_expand_iterations          6
% 2.55/1.08  --bmc1_ucm_extend_mode                  1
% 2.55/1.08  --bmc1_ucm_init_mode                    2
% 2.55/1.08  --bmc1_ucm_cone_mode                    none
% 2.55/1.08  --bmc1_ucm_reduced_relation_type        0
% 2.55/1.08  --bmc1_ucm_relax_model                  4
% 2.55/1.08  --bmc1_ucm_full_tr_after_sat            true
% 2.55/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/1.08  --bmc1_ucm_layered_model                none
% 2.55/1.08  --bmc1_ucm_max_lemma_size               10
% 2.55/1.08  
% 2.55/1.08  ------ AIG Options
% 2.55/1.08  
% 2.55/1.08  --aig_mode                              false
% 2.55/1.08  
% 2.55/1.08  ------ Instantiation Options
% 2.55/1.08  
% 2.55/1.08  --instantiation_flag                    true
% 2.55/1.08  --inst_sos_flag                         false
% 2.55/1.08  --inst_sos_phase                        true
% 2.55/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/1.08  --inst_lit_sel_side                     num_symb
% 2.55/1.08  --inst_solver_per_active                1400
% 2.55/1.08  --inst_solver_calls_frac                1.
% 2.55/1.08  --inst_passive_queue_type               priority_queues
% 2.55/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/1.08  --inst_passive_queues_freq              [25;2]
% 2.55/1.08  --inst_dismatching                      true
% 2.55/1.08  --inst_eager_unprocessed_to_passive     true
% 2.55/1.08  --inst_prop_sim_given                   true
% 2.55/1.08  --inst_prop_sim_new                     false
% 2.55/1.08  --inst_subs_new                         false
% 2.55/1.08  --inst_eq_res_simp                      false
% 2.55/1.08  --inst_subs_given                       false
% 2.55/1.08  --inst_orphan_elimination               true
% 2.55/1.08  --inst_learning_loop_flag               true
% 2.55/1.08  --inst_learning_start                   3000
% 2.55/1.08  --inst_learning_factor                  2
% 2.55/1.08  --inst_start_prop_sim_after_learn       3
% 2.55/1.08  --inst_sel_renew                        solver
% 2.55/1.08  --inst_lit_activity_flag                true
% 2.55/1.08  --inst_restr_to_given                   false
% 2.55/1.08  --inst_activity_threshold               500
% 2.55/1.08  --inst_out_proof                        true
% 2.55/1.08  
% 2.55/1.08  ------ Resolution Options
% 2.55/1.08  
% 2.55/1.08  --resolution_flag                       true
% 2.55/1.08  --res_lit_sel                           adaptive
% 2.55/1.08  --res_lit_sel_side                      none
% 2.55/1.08  --res_ordering                          kbo
% 2.55/1.08  --res_to_prop_solver                    active
% 2.55/1.08  --res_prop_simpl_new                    false
% 2.55/1.08  --res_prop_simpl_given                  true
% 2.55/1.08  --res_passive_queue_type                priority_queues
% 2.55/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/1.08  --res_passive_queues_freq               [15;5]
% 2.55/1.08  --res_forward_subs                      full
% 2.55/1.08  --res_backward_subs                     full
% 2.55/1.08  --res_forward_subs_resolution           true
% 2.55/1.08  --res_backward_subs_resolution          true
% 2.55/1.08  --res_orphan_elimination                true
% 2.55/1.08  --res_time_limit                        2.
% 2.55/1.08  --res_out_proof                         true
% 2.55/1.08  
% 2.55/1.08  ------ Superposition Options
% 2.55/1.08  
% 2.55/1.08  --superposition_flag                    true
% 2.55/1.08  --sup_passive_queue_type                priority_queues
% 2.55/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/1.08  --sup_passive_queues_freq               [8;1;4]
% 2.55/1.08  --demod_completeness_check              fast
% 2.55/1.08  --demod_use_ground                      true
% 2.55/1.08  --sup_to_prop_solver                    passive
% 2.55/1.08  --sup_prop_simpl_new                    true
% 2.55/1.08  --sup_prop_simpl_given                  true
% 2.55/1.08  --sup_fun_splitting                     false
% 2.55/1.08  --sup_smt_interval                      50000
% 2.55/1.08  
% 2.55/1.08  ------ Superposition Simplification Setup
% 2.55/1.08  
% 2.55/1.08  --sup_indices_passive                   []
% 2.55/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.08  --sup_full_bw                           [BwDemod]
% 2.55/1.08  --sup_immed_triv                        [TrivRules]
% 2.55/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.08  --sup_immed_bw_main                     []
% 2.55/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.08  
% 2.55/1.08  ------ Combination Options
% 2.55/1.08  
% 2.55/1.08  --comb_res_mult                         3
% 2.55/1.08  --comb_sup_mult                         2
% 2.55/1.08  --comb_inst_mult                        10
% 2.55/1.08  
% 2.55/1.08  ------ Debug Options
% 2.55/1.08  
% 2.55/1.08  --dbg_backtrace                         false
% 2.55/1.08  --dbg_dump_prop_clauses                 false
% 2.55/1.08  --dbg_dump_prop_clauses_file            -
% 2.55/1.08  --dbg_out_stat                          false
% 2.55/1.08  ------ Parsing...
% 2.55/1.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.55/1.08  
% 2.55/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.55/1.08  
% 2.55/1.08  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.55/1.08  
% 2.55/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.55/1.08  ------ Proving...
% 2.55/1.08  ------ Problem Properties 
% 2.55/1.08  
% 2.55/1.08  
% 2.55/1.08  clauses                                 20
% 2.55/1.08  conjectures                             7
% 2.55/1.08  EPR                                     4
% 2.55/1.08  Horn                                    16
% 2.55/1.08  unary                                   7
% 2.55/1.08  binary                                  6
% 2.55/1.08  lits                                    48
% 2.55/1.08  lits eq                                 19
% 2.55/1.08  fd_pure                                 0
% 2.55/1.08  fd_pseudo                               0
% 2.55/1.08  fd_cond                                 0
% 2.55/1.08  fd_pseudo_cond                          0
% 2.55/1.08  AC symbols                              0
% 2.55/1.08  
% 2.55/1.08  ------ Schedule dynamic 5 is on 
% 2.55/1.08  
% 2.55/1.08  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.55/1.08  
% 2.55/1.08  
% 2.55/1.08  ------ 
% 2.55/1.08  Current options:
% 2.55/1.08  ------ 
% 2.55/1.08  
% 2.55/1.08  ------ Input Options
% 2.55/1.08  
% 2.55/1.08  --out_options                           all
% 2.55/1.08  --tptp_safe_out                         true
% 2.55/1.08  --problem_path                          ""
% 2.55/1.08  --include_path                          ""
% 2.55/1.08  --clausifier                            res/vclausify_rel
% 2.55/1.08  --clausifier_options                    --mode clausify
% 2.55/1.08  --stdin                                 false
% 2.55/1.08  --stats_out                             all
% 2.55/1.08  
% 2.55/1.08  ------ General Options
% 2.55/1.08  
% 2.55/1.08  --fof                                   false
% 2.55/1.08  --time_out_real                         305.
% 2.55/1.08  --time_out_virtual                      -1.
% 2.55/1.08  --symbol_type_check                     false
% 2.55/1.08  --clausify_out                          false
% 2.55/1.08  --sig_cnt_out                           false
% 2.55/1.08  --trig_cnt_out                          false
% 2.55/1.08  --trig_cnt_out_tolerance                1.
% 2.55/1.08  --trig_cnt_out_sk_spl                   false
% 2.55/1.08  --abstr_cl_out                          false
% 2.55/1.08  
% 2.55/1.08  ------ Global Options
% 2.55/1.08  
% 2.55/1.08  --schedule                              default
% 2.55/1.08  --add_important_lit                     false
% 2.55/1.08  --prop_solver_per_cl                    1000
% 2.55/1.08  --min_unsat_core                        false
% 2.55/1.08  --soft_assumptions                      false
% 2.55/1.08  --soft_lemma_size                       3
% 2.55/1.08  --prop_impl_unit_size                   0
% 2.55/1.08  --prop_impl_unit                        []
% 2.55/1.08  --share_sel_clauses                     true
% 2.55/1.08  --reset_solvers                         false
% 2.55/1.08  --bc_imp_inh                            [conj_cone]
% 2.55/1.08  --conj_cone_tolerance                   3.
% 2.55/1.08  --extra_neg_conj                        none
% 2.55/1.08  --large_theory_mode                     true
% 2.55/1.08  --prolific_symb_bound                   200
% 2.55/1.08  --lt_threshold                          2000
% 2.55/1.08  --clause_weak_htbl                      true
% 2.55/1.08  --gc_record_bc_elim                     false
% 2.55/1.08  
% 2.55/1.08  ------ Preprocessing Options
% 2.55/1.08  
% 2.55/1.08  --preprocessing_flag                    true
% 2.55/1.08  --time_out_prep_mult                    0.1
% 2.55/1.08  --splitting_mode                        input
% 2.55/1.08  --splitting_grd                         true
% 2.55/1.08  --splitting_cvd                         false
% 2.55/1.08  --splitting_cvd_svl                     false
% 2.55/1.08  --splitting_nvd                         32
% 2.55/1.08  --sub_typing                            true
% 2.55/1.08  --prep_gs_sim                           true
% 2.55/1.08  --prep_unflatten                        true
% 2.55/1.08  --prep_res_sim                          true
% 2.55/1.08  --prep_upred                            true
% 2.55/1.08  --prep_sem_filter                       exhaustive
% 2.55/1.08  --prep_sem_filter_out                   false
% 2.55/1.08  --pred_elim                             true
% 2.55/1.08  --res_sim_input                         true
% 2.55/1.08  --eq_ax_congr_red                       true
% 2.55/1.08  --pure_diseq_elim                       true
% 2.55/1.08  --brand_transform                       false
% 2.55/1.08  --non_eq_to_eq                          false
% 2.55/1.08  --prep_def_merge                        true
% 2.55/1.08  --prep_def_merge_prop_impl              false
% 2.55/1.08  --prep_def_merge_mbd                    true
% 2.55/1.08  --prep_def_merge_tr_red                 false
% 2.55/1.08  --prep_def_merge_tr_cl                  false
% 2.55/1.08  --smt_preprocessing                     true
% 2.55/1.08  --smt_ac_axioms                         fast
% 2.55/1.08  --preprocessed_out                      false
% 2.55/1.08  --preprocessed_stats                    false
% 2.55/1.08  
% 2.55/1.08  ------ Abstraction refinement Options
% 2.55/1.08  
% 2.55/1.08  --abstr_ref                             []
% 2.55/1.08  --abstr_ref_prep                        false
% 2.55/1.08  --abstr_ref_until_sat                   false
% 2.55/1.08  --abstr_ref_sig_restrict                funpre
% 2.55/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/1.08  --abstr_ref_under                       []
% 2.55/1.08  
% 2.55/1.08  ------ SAT Options
% 2.55/1.08  
% 2.55/1.08  --sat_mode                              false
% 2.55/1.08  --sat_fm_restart_options                ""
% 2.55/1.08  --sat_gr_def                            false
% 2.55/1.08  --sat_epr_types                         true
% 2.55/1.08  --sat_non_cyclic_types                  false
% 2.55/1.08  --sat_finite_models                     false
% 2.55/1.08  --sat_fm_lemmas                         false
% 2.55/1.08  --sat_fm_prep                           false
% 2.55/1.08  --sat_fm_uc_incr                        true
% 2.55/1.08  --sat_out_model                         small
% 2.55/1.08  --sat_out_clauses                       false
% 2.55/1.08  
% 2.55/1.08  ------ QBF Options
% 2.55/1.08  
% 2.55/1.08  --qbf_mode                              false
% 2.55/1.08  --qbf_elim_univ                         false
% 2.55/1.08  --qbf_dom_inst                          none
% 2.55/1.08  --qbf_dom_pre_inst                      false
% 2.55/1.08  --qbf_sk_in                             false
% 2.55/1.08  --qbf_pred_elim                         true
% 2.55/1.08  --qbf_split                             512
% 2.55/1.08  
% 2.55/1.08  ------ BMC1 Options
% 2.55/1.08  
% 2.55/1.08  --bmc1_incremental                      false
% 2.55/1.08  --bmc1_axioms                           reachable_all
% 2.55/1.08  --bmc1_min_bound                        0
% 2.55/1.08  --bmc1_max_bound                        -1
% 2.55/1.08  --bmc1_max_bound_default                -1
% 2.55/1.08  --bmc1_symbol_reachability              true
% 2.55/1.08  --bmc1_property_lemmas                  false
% 2.55/1.08  --bmc1_k_induction                      false
% 2.55/1.08  --bmc1_non_equiv_states                 false
% 2.55/1.08  --bmc1_deadlock                         false
% 2.55/1.08  --bmc1_ucm                              false
% 2.55/1.08  --bmc1_add_unsat_core                   none
% 2.55/1.08  --bmc1_unsat_core_children              false
% 2.55/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/1.08  --bmc1_out_stat                         full
% 2.55/1.08  --bmc1_ground_init                      false
% 2.55/1.08  --bmc1_pre_inst_next_state              false
% 2.55/1.08  --bmc1_pre_inst_state                   false
% 2.55/1.08  --bmc1_pre_inst_reach_state             false
% 2.55/1.08  --bmc1_out_unsat_core                   false
% 2.55/1.08  --bmc1_aig_witness_out                  false
% 2.55/1.08  --bmc1_verbose                          false
% 2.55/1.08  --bmc1_dump_clauses_tptp                false
% 2.55/1.08  --bmc1_dump_unsat_core_tptp             false
% 2.55/1.08  --bmc1_dump_file                        -
% 2.55/1.08  --bmc1_ucm_expand_uc_limit              128
% 2.55/1.08  --bmc1_ucm_n_expand_iterations          6
% 2.55/1.08  --bmc1_ucm_extend_mode                  1
% 2.55/1.08  --bmc1_ucm_init_mode                    2
% 2.55/1.08  --bmc1_ucm_cone_mode                    none
% 2.55/1.08  --bmc1_ucm_reduced_relation_type        0
% 2.55/1.08  --bmc1_ucm_relax_model                  4
% 2.55/1.08  --bmc1_ucm_full_tr_after_sat            true
% 2.55/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/1.08  --bmc1_ucm_layered_model                none
% 2.55/1.08  --bmc1_ucm_max_lemma_size               10
% 2.55/1.08  
% 2.55/1.08  ------ AIG Options
% 2.55/1.08  
% 2.55/1.08  --aig_mode                              false
% 2.55/1.08  
% 2.55/1.08  ------ Instantiation Options
% 2.55/1.08  
% 2.55/1.08  --instantiation_flag                    true
% 2.55/1.08  --inst_sos_flag                         false
% 2.55/1.08  --inst_sos_phase                        true
% 2.55/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/1.08  --inst_lit_sel_side                     none
% 2.55/1.08  --inst_solver_per_active                1400
% 2.55/1.08  --inst_solver_calls_frac                1.
% 2.55/1.08  --inst_passive_queue_type               priority_queues
% 2.55/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/1.08  --inst_passive_queues_freq              [25;2]
% 2.55/1.08  --inst_dismatching                      true
% 2.55/1.08  --inst_eager_unprocessed_to_passive     true
% 2.55/1.08  --inst_prop_sim_given                   true
% 2.55/1.08  --inst_prop_sim_new                     false
% 2.55/1.08  --inst_subs_new                         false
% 2.55/1.08  --inst_eq_res_simp                      false
% 2.55/1.08  --inst_subs_given                       false
% 2.55/1.08  --inst_orphan_elimination               true
% 2.55/1.08  --inst_learning_loop_flag               true
% 2.55/1.08  --inst_learning_start                   3000
% 2.55/1.08  --inst_learning_factor                  2
% 2.55/1.08  --inst_start_prop_sim_after_learn       3
% 2.55/1.08  --inst_sel_renew                        solver
% 2.55/1.08  --inst_lit_activity_flag                true
% 2.55/1.08  --inst_restr_to_given                   false
% 2.55/1.08  --inst_activity_threshold               500
% 2.55/1.08  --inst_out_proof                        true
% 2.55/1.08  
% 2.55/1.08  ------ Resolution Options
% 2.55/1.08  
% 2.55/1.08  --resolution_flag                       false
% 2.55/1.08  --res_lit_sel                           adaptive
% 2.55/1.08  --res_lit_sel_side                      none
% 2.55/1.08  --res_ordering                          kbo
% 2.55/1.08  --res_to_prop_solver                    active
% 2.55/1.08  --res_prop_simpl_new                    false
% 2.55/1.08  --res_prop_simpl_given                  true
% 2.55/1.08  --res_passive_queue_type                priority_queues
% 2.55/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/1.08  --res_passive_queues_freq               [15;5]
% 2.55/1.08  --res_forward_subs                      full
% 2.55/1.08  --res_backward_subs                     full
% 2.55/1.08  --res_forward_subs_resolution           true
% 2.55/1.08  --res_backward_subs_resolution          true
% 2.55/1.08  --res_orphan_elimination                true
% 2.55/1.08  --res_time_limit                        2.
% 2.55/1.08  --res_out_proof                         true
% 2.55/1.08  
% 2.55/1.08  ------ Superposition Options
% 2.55/1.08  
% 2.55/1.08  --superposition_flag                    true
% 2.55/1.08  --sup_passive_queue_type                priority_queues
% 2.55/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/1.08  --sup_passive_queues_freq               [8;1;4]
% 2.55/1.08  --demod_completeness_check              fast
% 2.55/1.08  --demod_use_ground                      true
% 2.55/1.08  --sup_to_prop_solver                    passive
% 2.55/1.08  --sup_prop_simpl_new                    true
% 2.55/1.08  --sup_prop_simpl_given                  true
% 2.55/1.08  --sup_fun_splitting                     false
% 2.55/1.08  --sup_smt_interval                      50000
% 2.55/1.08  
% 2.55/1.08  ------ Superposition Simplification Setup
% 2.55/1.08  
% 2.55/1.08  --sup_indices_passive                   []
% 2.55/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.08  --sup_full_bw                           [BwDemod]
% 2.55/1.08  --sup_immed_triv                        [TrivRules]
% 2.55/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.09  --sup_immed_bw_main                     []
% 2.55/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.09  
% 2.55/1.09  ------ Combination Options
% 2.55/1.09  
% 2.55/1.09  --comb_res_mult                         3
% 2.55/1.09  --comb_sup_mult                         2
% 2.55/1.09  --comb_inst_mult                        10
% 2.55/1.09  
% 2.55/1.09  ------ Debug Options
% 2.55/1.09  
% 2.55/1.09  --dbg_backtrace                         false
% 2.55/1.09  --dbg_dump_prop_clauses                 false
% 2.55/1.09  --dbg_dump_prop_clauses_file            -
% 2.55/1.09  --dbg_out_stat                          false
% 2.55/1.09  
% 2.55/1.09  
% 2.55/1.09  
% 2.55/1.09  
% 2.55/1.09  ------ Proving...
% 2.55/1.09  
% 2.55/1.09  
% 2.55/1.09  % SZS status Theorem for theBenchmark.p
% 2.55/1.09  
% 2.55/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 2.55/1.09  
% 2.55/1.09  fof(f8,axiom,(
% 2.55/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f20,plain,(
% 2.55/1.09    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.09    inference(ennf_transformation,[],[f8])).
% 2.55/1.09  
% 2.55/1.09  fof(f21,plain,(
% 2.55/1.09    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.09    inference(flattening,[],[f20])).
% 2.55/1.09  
% 2.55/1.09  fof(f26,plain,(
% 2.55/1.09    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.09    inference(nnf_transformation,[],[f21])).
% 2.55/1.09  
% 2.55/1.09  fof(f37,plain,(
% 2.55/1.09    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.09    inference(cnf_transformation,[],[f26])).
% 2.55/1.09  
% 2.55/1.09  fof(f10,conjecture,(
% 2.55/1.09    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f11,negated_conjecture,(
% 2.55/1.09    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.55/1.09    inference(negated_conjecture,[],[f10])).
% 2.55/1.09  
% 2.55/1.09  fof(f24,plain,(
% 2.55/1.09    ? [X0,X1,X2,X3] : (? [X4] : (((~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.55/1.09    inference(ennf_transformation,[],[f11])).
% 2.55/1.09  
% 2.55/1.09  fof(f25,plain,(
% 2.55/1.09    ? [X0,X1,X2,X3] : (? [X4] : (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.55/1.09    inference(flattening,[],[f24])).
% 2.55/1.09  
% 2.55/1.09  fof(f28,plain,(
% 2.55/1.09    ( ! [X2,X0,X3,X1] : (? [X4] : (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 2.55/1.09    introduced(choice_axiom,[])).
% 2.55/1.09  
% 2.55/1.09  fof(f27,plain,(
% 2.55/1.09    ? [X0,X1,X2,X3] : (? [X4] : (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~v2_funct_1(sK3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.55/1.09    introduced(choice_axiom,[])).
% 2.55/1.09  
% 2.55/1.09  fof(f29,plain,(
% 2.55/1.09    (~v2_funct_1(sK3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.55/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f28,f27])).
% 2.55/1.09  
% 2.55/1.09  fof(f45,plain,(
% 2.55/1.09    v1_funct_2(sK3,sK0,sK1)),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f46,plain,(
% 2.55/1.09    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f6,axiom,(
% 2.55/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f18,plain,(
% 2.55/1.09    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.09    inference(ennf_transformation,[],[f6])).
% 2.55/1.09  
% 2.55/1.09  fof(f35,plain,(
% 2.55/1.09    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.09    inference(cnf_transformation,[],[f18])).
% 2.55/1.09  
% 2.55/1.09  fof(f1,axiom,(
% 2.55/1.09    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f12,plain,(
% 2.55/1.09    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.55/1.09    inference(unused_predicate_definition_removal,[],[f1])).
% 2.55/1.09  
% 2.55/1.09  fof(f13,plain,(
% 2.55/1.09    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.55/1.09    inference(ennf_transformation,[],[f12])).
% 2.55/1.09  
% 2.55/1.09  fof(f30,plain,(
% 2.55/1.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.55/1.09    inference(cnf_transformation,[],[f13])).
% 2.55/1.09  
% 2.55/1.09  fof(f4,axiom,(
% 2.55/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f15,plain,(
% 2.55/1.09    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.55/1.09    inference(ennf_transformation,[],[f4])).
% 2.55/1.09  
% 2.55/1.09  fof(f16,plain,(
% 2.55/1.09    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.55/1.09    inference(flattening,[],[f15])).
% 2.55/1.09  
% 2.55/1.09  fof(f33,plain,(
% 2.55/1.09    ( ! [X0,X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.55/1.09    inference(cnf_transformation,[],[f16])).
% 2.55/1.09  
% 2.55/1.09  fof(f44,plain,(
% 2.55/1.09    v1_funct_1(sK3)),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f52,plain,(
% 2.55/1.09    ~v2_funct_1(sK3)),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f2,axiom,(
% 2.55/1.09    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f14,plain,(
% 2.55/1.09    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.55/1.09    inference(ennf_transformation,[],[f2])).
% 2.55/1.09  
% 2.55/1.09  fof(f31,plain,(
% 2.55/1.09    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.55/1.09    inference(cnf_transformation,[],[f14])).
% 2.55/1.09  
% 2.55/1.09  fof(f3,axiom,(
% 2.55/1.09    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f32,plain,(
% 2.55/1.09    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.55/1.09    inference(cnf_transformation,[],[f3])).
% 2.55/1.09  
% 2.55/1.09  fof(f49,plain,(
% 2.55/1.09    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f9,axiom,(
% 2.55/1.09    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f22,plain,(
% 2.55/1.09    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.55/1.09    inference(ennf_transformation,[],[f9])).
% 2.55/1.09  
% 2.55/1.09  fof(f23,plain,(
% 2.55/1.09    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.55/1.09    inference(flattening,[],[f22])).
% 2.55/1.09  
% 2.55/1.09  fof(f43,plain,(
% 2.55/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.55/1.09    inference(cnf_transformation,[],[f23])).
% 2.55/1.09  
% 2.55/1.09  fof(f47,plain,(
% 2.55/1.09    v1_funct_1(sK4)),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f50,plain,(
% 2.55/1.09    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f41,plain,(
% 2.55/1.09    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.09    inference(cnf_transformation,[],[f26])).
% 2.55/1.09  
% 2.55/1.09  fof(f55,plain,(
% 2.55/1.09    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.55/1.09    inference(equality_resolution,[],[f41])).
% 2.55/1.09  
% 2.55/1.09  fof(f48,plain,(
% 2.55/1.09    v1_funct_2(sK4,sK1,sK2)),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f51,plain,(
% 2.55/1.09    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.55/1.09    inference(cnf_transformation,[],[f29])).
% 2.55/1.09  
% 2.55/1.09  fof(f7,axiom,(
% 2.55/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f19,plain,(
% 2.55/1.09    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.09    inference(ennf_transformation,[],[f7])).
% 2.55/1.09  
% 2.55/1.09  fof(f36,plain,(
% 2.55/1.09    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.09    inference(cnf_transformation,[],[f19])).
% 2.55/1.09  
% 2.55/1.09  fof(f5,axiom,(
% 2.55/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.55/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.09  
% 2.55/1.09  fof(f17,plain,(
% 2.55/1.09    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.09    inference(ennf_transformation,[],[f5])).
% 2.55/1.09  
% 2.55/1.09  fof(f34,plain,(
% 2.55/1.09    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.09    inference(cnf_transformation,[],[f17])).
% 2.55/1.09  
% 2.55/1.09  fof(f38,plain,(
% 2.55/1.09    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.09    inference(cnf_transformation,[],[f26])).
% 2.55/1.09  
% 2.55/1.09  fof(f57,plain,(
% 2.55/1.09    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.55/1.09    inference(equality_resolution,[],[f38])).
% 2.55/1.09  
% 2.55/1.09  cnf(c_12,plain,
% 2.55/1.09      ( ~ v1_funct_2(X0,X1,X2)
% 2.55/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.09      | k1_relset_1(X1,X2,X0) = X1
% 2.55/1.09      | k1_xboole_0 = X2 ),
% 2.55/1.09      inference(cnf_transformation,[],[f37]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_21,negated_conjecture,
% 2.55/1.09      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.55/1.09      inference(cnf_transformation,[],[f45]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_362,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.09      | k1_relset_1(X1,X2,X0) = X1
% 2.55/1.09      | sK0 != X1
% 2.55/1.09      | sK1 != X2
% 2.55/1.09      | sK3 != X0
% 2.55/1.09      | k1_xboole_0 = X2 ),
% 2.55/1.09      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_363,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.55/1.09      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.55/1.09      | k1_xboole_0 = sK1 ),
% 2.55/1.09      inference(unflattening,[status(thm)],[c_362]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_20,negated_conjecture,
% 2.55/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.55/1.09      inference(cnf_transformation,[],[f46]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_365,plain,
% 2.55/1.09      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_363,c_20]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_511,plain,
% 2.55/1.09      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_365]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_519,negated_conjecture,
% 2.55/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_20]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_866,plain,
% 2.55/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_5,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.09      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.55/1.09      inference(cnf_transformation,[],[f35]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_527,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.55/1.09      | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_5]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_859,plain,
% 2.55/1.09      ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
% 2.55/1.09      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1246,plain,
% 2.55/1.09      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_866,c_859]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1339,plain,
% 2.55/1.09      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_511,c_1246]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_0,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.55/1.09      inference(cnf_transformation,[],[f30]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_3,plain,
% 2.55/1.09      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.55/1.09      | ~ v1_funct_1(X0)
% 2.55/1.09      | ~ v1_funct_1(X1)
% 2.55/1.09      | v2_funct_1(X0)
% 2.55/1.09      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.55/1.09      | ~ v1_relat_1(X1)
% 2.55/1.09      | ~ v1_relat_1(X0) ),
% 2.55/1.09      inference(cnf_transformation,[],[f33]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_242,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.55/1.09      | ~ v1_funct_1(X2)
% 2.55/1.09      | ~ v1_funct_1(X3)
% 2.55/1.09      | v2_funct_1(X3)
% 2.55/1.09      | ~ v2_funct_1(k5_relat_1(X3,X2))
% 2.55/1.09      | ~ v1_relat_1(X2)
% 2.55/1.09      | ~ v1_relat_1(X3)
% 2.55/1.09      | k1_relat_1(X2) != X1
% 2.55/1.09      | k2_relat_1(X3) != X0 ),
% 2.55/1.09      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_243,plain,
% 2.55/1.09      ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
% 2.55/1.09      | ~ v1_funct_1(X0)
% 2.55/1.09      | ~ v1_funct_1(X1)
% 2.55/1.09      | v2_funct_1(X0)
% 2.55/1.09      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.55/1.09      | ~ v1_relat_1(X0)
% 2.55/1.09      | ~ v1_relat_1(X1) ),
% 2.55/1.09      inference(unflattening,[status(thm)],[c_242]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_517,plain,
% 2.55/1.09      ( ~ m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X1_48)))
% 2.55/1.09      | ~ v1_funct_1(X0_48)
% 2.55/1.09      | ~ v1_funct_1(X1_48)
% 2.55/1.09      | v2_funct_1(X0_48)
% 2.55/1.09      | ~ v2_funct_1(k5_relat_1(X0_48,X1_48))
% 2.55/1.09      | ~ v1_relat_1(X0_48)
% 2.55/1.09      | ~ v1_relat_1(X1_48) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_243]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_868,plain,
% 2.55/1.09      ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X1_48))) != iProver_top
% 2.55/1.09      | v1_funct_1(X0_48) != iProver_top
% 2.55/1.09      | v1_funct_1(X1_48) != iProver_top
% 2.55/1.09      | v2_funct_1(X0_48) = iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(X0_48,X1_48)) != iProver_top
% 2.55/1.09      | v1_relat_1(X1_48) != iProver_top
% 2.55/1.09      | v1_relat_1(X0_48) != iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2140,plain,
% 2.55/1.09      ( sK1 = k1_xboole_0
% 2.55/1.09      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK0)) != iProver_top
% 2.55/1.09      | v1_funct_1(X0_48) != iProver_top
% 2.55/1.09      | v1_funct_1(sK3) != iProver_top
% 2.55/1.09      | v2_funct_1(X0_48) = iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(X0_48,sK3)) != iProver_top
% 2.55/1.09      | v1_relat_1(X0_48) != iProver_top
% 2.55/1.09      | v1_relat_1(sK3) != iProver_top ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_1339,c_868]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_22,negated_conjecture,
% 2.55/1.09      ( v1_funct_1(sK3) ),
% 2.55/1.09      inference(cnf_transformation,[],[f44]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_23,plain,
% 2.55/1.09      ( v1_funct_1(sK3) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_25,plain,
% 2.55/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_14,negated_conjecture,
% 2.55/1.09      ( ~ v2_funct_1(sK3) ),
% 2.55/1.09      inference(cnf_transformation,[],[f52]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_30,plain,
% 2.55/1.09      ( v2_funct_1(sK3) != iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.55/1.09      | ~ v1_relat_1(X1)
% 2.55/1.09      | v1_relat_1(X0) ),
% 2.55/1.09      inference(cnf_transformation,[],[f31]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_530,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 2.55/1.09      | ~ v1_relat_1(X1_48)
% 2.55/1.09      | v1_relat_1(X0_48) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_1]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1011,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.55/1.09      | v1_relat_1(X0_48)
% 2.55/1.09      | ~ v1_relat_1(k2_zfmisc_1(X1_48,X2_48)) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_530]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1198,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.55/1.09      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.55/1.09      | v1_relat_1(sK3) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_1011]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1199,plain,
% 2.55/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.55/1.09      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.55/1.09      | v1_relat_1(sK3) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_1198]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_534,plain,
% 2.55/1.09      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.55/1.09      theory(equality) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1041,plain,
% 2.55/1.09      ( sK1 != X0_48 | sK1 = k1_xboole_0 | k1_xboole_0 != X0_48 ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_534]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1210,plain,
% 2.55/1.09      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_1041]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_532,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1211,plain,
% 2.55/1.09      ( sK1 = sK1 ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_532]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2,plain,
% 2.55/1.09      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.55/1.09      inference(cnf_transformation,[],[f32]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_529,plain,
% 2.55/1.09      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_2]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1296,plain,
% 2.55/1.09      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_529]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1297,plain,
% 2.55/1.09      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_17,negated_conjecture,
% 2.55/1.09      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.55/1.09      inference(cnf_transformation,[],[f49]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_521,negated_conjecture,
% 2.55/1.09      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_17]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_864,plain,
% 2.55/1.09      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_13,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.55/1.09      | ~ v1_funct_1(X0)
% 2.55/1.09      | ~ v1_funct_1(X3)
% 2.55/1.09      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.55/1.09      inference(cnf_transformation,[],[f43]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_525,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.55/1.09      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 2.55/1.09      | ~ v1_funct_1(X0_48)
% 2.55/1.09      | ~ v1_funct_1(X3_48)
% 2.55/1.09      | k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48) = k5_relat_1(X3_48,X0_48) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_13]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_861,plain,
% 2.55/1.09      ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X4_48,X5_48) = k5_relat_1(X4_48,X5_48)
% 2.55/1.09      | m1_subset_1(X5_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 2.55/1.09      | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.55/1.09      | v1_funct_1(X5_48) != iProver_top
% 2.55/1.09      | v1_funct_1(X4_48) != iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1544,plain,
% 2.55/1.09      ( k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4)
% 2.55/1.09      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.55/1.09      | v1_funct_1(X2_48) != iProver_top
% 2.55/1.09      | v1_funct_1(sK4) != iProver_top ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_864,c_861]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_19,negated_conjecture,
% 2.55/1.09      ( v1_funct_1(sK4) ),
% 2.55/1.09      inference(cnf_transformation,[],[f47]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_26,plain,
% 2.55/1.09      ( v1_funct_1(sK4) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1723,plain,
% 2.55/1.09      ( v1_funct_1(X2_48) != iProver_top
% 2.55/1.09      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.55/1.09      | k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4) ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_1544,c_26]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1724,plain,
% 2.55/1.09      ( k1_partfun1(X0_48,X1_48,sK1,sK2,X2_48,sK4) = k5_relat_1(X2_48,sK4)
% 2.55/1.09      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.55/1.09      | v1_funct_1(X2_48) != iProver_top ),
% 2.55/1.09      inference(renaming,[status(thm)],[c_1723]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1733,plain,
% 2.55/1.09      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 2.55/1.09      | v1_funct_1(sK3) != iProver_top ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_866,c_1724]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1080,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.55/1.09      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_48,X4_48)))
% 2.55/1.09      | ~ v1_funct_1(X0_48)
% 2.55/1.09      | ~ v1_funct_1(sK4)
% 2.55/1.09      | k1_partfun1(X1_48,X2_48,X3_48,X4_48,X0_48,sK4) = k5_relat_1(X0_48,sK4) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_525]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1143,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.55/1.09      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
% 2.55/1.09      | ~ v1_funct_1(sK4)
% 2.55/1.09      | ~ v1_funct_1(sK3)
% 2.55/1.09      | k1_partfun1(X2_48,X3_48,X0_48,X1_48,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_1080]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1172,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.09      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.55/1.09      | ~ v1_funct_1(sK4)
% 2.55/1.09      | ~ v1_funct_1(sK3)
% 2.55/1.09      | k1_partfun1(X0_48,X1_48,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_1143]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1321,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.09      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.55/1.09      | ~ v1_funct_1(sK4)
% 2.55/1.09      | ~ v1_funct_1(sK3)
% 2.55/1.09      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_1172]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1875,plain,
% 2.55/1.09      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_1733,c_22,c_20,c_19,c_17,c_1321]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_16,negated_conjecture,
% 2.55/1.09      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 2.55/1.09      inference(cnf_transformation,[],[f50]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_522,negated_conjecture,
% 2.55/1.09      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_16]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_863,plain,
% 2.55/1.09      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1878,plain,
% 2.55/1.09      ( v2_funct_1(k5_relat_1(sK3,sK4)) = iProver_top ),
% 2.55/1.09      inference(demodulation,[status(thm)],[c_1875,c_863]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_8,plain,
% 2.55/1.09      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.55/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.55/1.09      | k1_xboole_0 = X1
% 2.55/1.09      | k1_xboole_0 = X0 ),
% 2.55/1.09      inference(cnf_transformation,[],[f55]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_18,negated_conjecture,
% 2.55/1.09      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.55/1.09      inference(cnf_transformation,[],[f48]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_289,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.55/1.09      | sK4 != X0
% 2.55/1.09      | sK2 != k1_xboole_0
% 2.55/1.09      | sK1 != X1
% 2.55/1.09      | k1_xboole_0 = X0
% 2.55/1.09      | k1_xboole_0 = X1 ),
% 2.55/1.09      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_290,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.55/1.09      | sK2 != k1_xboole_0
% 2.55/1.09      | k1_xboole_0 = sK4
% 2.55/1.09      | k1_xboole_0 = sK1 ),
% 2.55/1.09      inference(unflattening,[status(thm)],[c_289]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_516,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.55/1.09      | sK2 != k1_xboole_0
% 2.55/1.09      | k1_xboole_0 = sK4
% 2.55/1.09      | k1_xboole_0 = sK1 ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_290]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_869,plain,
% 2.55/1.09      ( sK2 != k1_xboole_0
% 2.55/1.09      | k1_xboole_0 = sK4
% 2.55/1.09      | k1_xboole_0 = sK1
% 2.55/1.09      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_552,plain,
% 2.55/1.09      ( k1_xboole_0 = k1_xboole_0 ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_532]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_15,negated_conjecture,
% 2.55/1.09      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.55/1.09      inference(cnf_transformation,[],[f51]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_523,negated_conjecture,
% 2.55/1.09      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_15]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1335,plain,
% 2.55/1.09      ( sK2 != X0_48 | k1_xboole_0 != X0_48 | k1_xboole_0 = sK2 ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_534]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1336,plain,
% 2.55/1.09      ( sK2 != k1_xboole_0
% 2.55/1.09      | k1_xboole_0 = sK2
% 2.55/1.09      | k1_xboole_0 != k1_xboole_0 ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_1335]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2165,plain,
% 2.55/1.09      ( k1_xboole_0 = sK1 | sK2 != k1_xboole_0 ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_869,c_552,c_523,c_1336]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2166,plain,
% 2.55/1.09      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 2.55/1.09      inference(renaming,[status(thm)],[c_2165]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_6,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.09      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.55/1.09      inference(cnf_transformation,[],[f36]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_526,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.55/1.09      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_6]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_860,plain,
% 2.55/1.09      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.55/1.09      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1255,plain,
% 2.55/1.09      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_866,c_860]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_4,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.09      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.55/1.09      inference(cnf_transformation,[],[f34]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_528,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.55/1.09      | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_4]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_858,plain,
% 2.55/1.09      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.55/1.09      | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1471,plain,
% 2.55/1.09      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 2.55/1.09      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_1255,c_858]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1673,plain,
% 2.55/1.09      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_1471,c_25]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_351,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.09      | k1_relset_1(X1,X2,X0) = X1
% 2.55/1.09      | sK4 != X0
% 2.55/1.09      | sK2 != X2
% 2.55/1.09      | sK1 != X1
% 2.55/1.09      | k1_xboole_0 = X2 ),
% 2.55/1.09      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_352,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.09      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.55/1.09      | k1_xboole_0 = sK2 ),
% 2.55/1.09      inference(unflattening,[status(thm)],[c_351]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_354,plain,
% 2.55/1.09      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_352,c_17]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_512,plain,
% 2.55/1.09      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_354]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1245,plain,
% 2.55/1.09      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_864,c_859]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1319,plain,
% 2.55/1.09      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_512,c_1245]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2043,plain,
% 2.55/1.09      ( sK2 = k1_xboole_0
% 2.55/1.09      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
% 2.55/1.09      | v1_funct_1(X0_48) != iProver_top
% 2.55/1.09      | v1_funct_1(sK4) != iProver_top
% 2.55/1.09      | v2_funct_1(X0_48) = iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
% 2.55/1.09      | v1_relat_1(X0_48) != iProver_top
% 2.55/1.09      | v1_relat_1(sK4) != iProver_top ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_1319,c_868]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_28,plain,
% 2.55/1.09      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1195,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.09      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.55/1.09      | v1_relat_1(sK4) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_1011]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1196,plain,
% 2.55/1.09      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.55/1.09      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.55/1.09      | v1_relat_1(sK4) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_1195]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1293,plain,
% 2.55/1.09      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.55/1.09      inference(instantiation,[status(thm)],[c_529]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_1294,plain,
% 2.55/1.09      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2239,plain,
% 2.55/1.09      ( v1_relat_1(X0_48) != iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
% 2.55/1.09      | v2_funct_1(X0_48) = iProver_top
% 2.55/1.09      | sK2 = k1_xboole_0
% 2.55/1.09      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
% 2.55/1.09      | v1_funct_1(X0_48) != iProver_top ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_2043,c_26,c_28,c_1196,c_1294]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2240,plain,
% 2.55/1.09      ( sK2 = k1_xboole_0
% 2.55/1.09      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(sK1)) != iProver_top
% 2.55/1.09      | v1_funct_1(X0_48) != iProver_top
% 2.55/1.09      | v2_funct_1(X0_48) = iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
% 2.55/1.09      | v1_relat_1(X0_48) != iProver_top ),
% 2.55/1.09      inference(renaming,[status(thm)],[c_2239]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2251,plain,
% 2.55/1.09      ( sK2 = k1_xboole_0
% 2.55/1.09      | v1_funct_1(sK3) != iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 2.55/1.09      | v2_funct_1(sK3) = iProver_top
% 2.55/1.09      | v1_relat_1(sK3) != iProver_top ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_1673,c_2240]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2254,plain,
% 2.55/1.09      ( sK1 = k1_xboole_0 ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_2140,c_23,c_25,c_30,c_1199,c_1210,c_1211,c_1297,
% 2.55/1.09                 c_1878,c_2166,c_2251]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2270,plain,
% 2.55/1.09      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.55/1.09      inference(demodulation,[status(thm)],[c_2254,c_1673]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_11,plain,
% 2.55/1.09      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.55/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.55/1.09      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.55/1.09      inference(cnf_transformation,[],[f57]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_325,plain,
% 2.55/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.55/1.09      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.55/1.09      | sK4 != X0
% 2.55/1.09      | sK2 != X1
% 2.55/1.09      | sK1 != k1_xboole_0 ),
% 2.55/1.09      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_326,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.55/1.09      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.55/1.09      | sK1 != k1_xboole_0 ),
% 2.55/1.09      inference(unflattening,[status(thm)],[c_325]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_514,plain,
% 2.55/1.09      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.55/1.09      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.55/1.09      | sK1 != k1_xboole_0 ),
% 2.55/1.09      inference(subtyping,[status(esa)],[c_326]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_871,plain,
% 2.55/1.09      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.55/1.09      | sK1 != k1_xboole_0
% 2.55/1.09      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.55/1.09      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2272,plain,
% 2.55/1.09      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.55/1.09      | k1_xboole_0 != k1_xboole_0
% 2.55/1.09      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.55/1.09      inference(demodulation,[status(thm)],[c_2254,c_871]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2298,plain,
% 2.55/1.09      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.55/1.09      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.55/1.09      inference(equality_resolution_simp,[status(thm)],[c_2272]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2276,plain,
% 2.55/1.09      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
% 2.55/1.09      inference(demodulation,[status(thm)],[c_2254,c_1245]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2299,plain,
% 2.55/1.09      ( k1_relat_1(sK4) = k1_xboole_0
% 2.55/1.09      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.55/1.09      inference(demodulation,[status(thm)],[c_2298,c_2276]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2280,plain,
% 2.55/1.09      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 2.55/1.09      inference(demodulation,[status(thm)],[c_2254,c_864]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2302,plain,
% 2.55/1.09      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.55/1.09      inference(forward_subsumption_resolution,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_2299,c_2280]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_2601,plain,
% 2.55/1.09      ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.55/1.09      | v1_funct_1(X0_48) != iProver_top
% 2.55/1.09      | v1_funct_1(sK4) != iProver_top
% 2.55/1.09      | v2_funct_1(X0_48) = iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
% 2.55/1.09      | v1_relat_1(X0_48) != iProver_top
% 2.55/1.09      | v1_relat_1(sK4) != iProver_top ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_2302,c_868]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_4256,plain,
% 2.55/1.09      ( v1_relat_1(X0_48) != iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
% 2.55/1.09      | v2_funct_1(X0_48) = iProver_top
% 2.55/1.09      | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.55/1.09      | v1_funct_1(X0_48) != iProver_top ),
% 2.55/1.09      inference(global_propositional_subsumption,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_2601,c_26,c_28,c_1196,c_1294]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_4257,plain,
% 2.55/1.09      ( m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.55/1.09      | v1_funct_1(X0_48) != iProver_top
% 2.55/1.09      | v2_funct_1(X0_48) = iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(X0_48,sK4)) != iProver_top
% 2.55/1.09      | v1_relat_1(X0_48) != iProver_top ),
% 2.55/1.09      inference(renaming,[status(thm)],[c_4256]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(c_4267,plain,
% 2.55/1.09      ( v1_funct_1(sK3) != iProver_top
% 2.55/1.09      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 2.55/1.09      | v2_funct_1(sK3) = iProver_top
% 2.55/1.09      | v1_relat_1(sK3) != iProver_top ),
% 2.55/1.09      inference(superposition,[status(thm)],[c_2270,c_4257]) ).
% 2.55/1.09  
% 2.55/1.09  cnf(contradiction,plain,
% 2.55/1.09      ( $false ),
% 2.55/1.09      inference(minisat,
% 2.55/1.09                [status(thm)],
% 2.55/1.09                [c_4267,c_1878,c_1297,c_1199,c_30,c_25,c_23]) ).
% 2.55/1.09  
% 2.55/1.09  
% 2.55/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 2.55/1.09  
% 2.55/1.09  ------                               Statistics
% 2.55/1.09  
% 2.55/1.09  ------ General
% 2.55/1.09  
% 2.55/1.09  abstr_ref_over_cycles:                  0
% 2.55/1.09  abstr_ref_under_cycles:                 0
% 2.55/1.09  gc_basic_clause_elim:                   0
% 2.55/1.09  forced_gc_time:                         0
% 2.55/1.09  parsing_time:                           0.014
% 2.55/1.09  unif_index_cands_time:                  0.
% 2.55/1.09  unif_index_add_time:                    0.
% 2.55/1.09  orderings_time:                         0.
% 2.55/1.09  out_proof_time:                         0.011
% 2.55/1.09  total_time:                             0.265
% 2.55/1.09  num_of_symbols:                         53
% 2.55/1.09  num_of_terms:                           3653
% 2.55/1.09  
% 2.55/1.09  ------ Preprocessing
% 2.55/1.09  
% 2.55/1.09  num_of_splits:                          0
% 2.55/1.09  num_of_split_atoms:                     0
% 2.55/1.09  num_of_reused_defs:                     0
% 2.55/1.09  num_eq_ax_congr_red:                    23
% 2.55/1.09  num_of_sem_filtered_clauses:            1
% 2.55/1.09  num_of_subtypes:                        2
% 2.55/1.09  monotx_restored_types:                  0
% 2.55/1.09  sat_num_of_epr_types:                   0
% 2.55/1.09  sat_num_of_non_cyclic_types:            0
% 2.55/1.09  sat_guarded_non_collapsed_types:        0
% 2.55/1.09  num_pure_diseq_elim:                    0
% 2.55/1.09  simp_replaced_by:                       0
% 2.55/1.09  res_preprocessed:                       106
% 2.55/1.09  prep_upred:                             0
% 2.55/1.09  prep_unflattend:                        36
% 2.55/1.09  smt_new_axioms:                         0
% 2.55/1.09  pred_elim_cands:                        4
% 2.55/1.09  pred_elim:                              2
% 2.55/1.09  pred_elim_cl:                           3
% 2.55/1.09  pred_elim_cycles:                       4
% 2.55/1.09  merged_defs:                            0
% 2.55/1.09  merged_defs_ncl:                        0
% 2.55/1.09  bin_hyper_res:                          0
% 2.55/1.09  prep_cycles:                            4
% 2.55/1.09  pred_elim_time:                         0.015
% 2.55/1.09  splitting_time:                         0.
% 2.55/1.09  sem_filter_time:                        0.
% 2.55/1.09  monotx_time:                            0.
% 2.55/1.09  subtype_inf_time:                       0.
% 2.55/1.09  
% 2.55/1.09  ------ Problem properties
% 2.55/1.09  
% 2.55/1.09  clauses:                                20
% 2.55/1.09  conjectures:                            7
% 2.55/1.09  epr:                                    4
% 2.55/1.09  horn:                                   16
% 2.55/1.09  ground:                                 13
% 2.55/1.09  unary:                                  7
% 2.55/1.09  binary:                                 6
% 2.55/1.09  lits:                                   48
% 2.55/1.09  lits_eq:                                19
% 2.55/1.09  fd_pure:                                0
% 2.55/1.09  fd_pseudo:                              0
% 2.55/1.09  fd_cond:                                0
% 2.55/1.09  fd_pseudo_cond:                         0
% 2.55/1.09  ac_symbols:                             0
% 2.55/1.09  
% 2.55/1.09  ------ Propositional Solver
% 2.55/1.09  
% 2.55/1.09  prop_solver_calls:                      30
% 2.55/1.09  prop_fast_solver_calls:                 837
% 2.55/1.09  smt_solver_calls:                       0
% 2.55/1.09  smt_fast_solver_calls:                  0
% 2.55/1.09  prop_num_of_clauses:                    1472
% 2.55/1.09  prop_preprocess_simplified:             3847
% 2.55/1.09  prop_fo_subsumed:                       32
% 2.55/1.09  prop_solver_time:                       0.
% 2.55/1.09  smt_solver_time:                        0.
% 2.55/1.09  smt_fast_solver_time:                   0.
% 2.55/1.09  prop_fast_solver_time:                  0.
% 2.55/1.09  prop_unsat_core_time:                   0.
% 2.55/1.09  
% 2.55/1.09  ------ QBF
% 2.55/1.09  
% 2.55/1.09  qbf_q_res:                              0
% 2.55/1.09  qbf_num_tautologies:                    0
% 2.55/1.09  qbf_prep_cycles:                        0
% 2.55/1.09  
% 2.55/1.09  ------ BMC1
% 2.55/1.09  
% 2.55/1.09  bmc1_current_bound:                     -1
% 2.55/1.09  bmc1_last_solved_bound:                 -1
% 2.55/1.09  bmc1_unsat_core_size:                   -1
% 2.55/1.09  bmc1_unsat_core_parents_size:           -1
% 2.55/1.09  bmc1_merge_next_fun:                    0
% 2.55/1.09  bmc1_unsat_core_clauses_time:           0.
% 2.55/1.09  
% 2.55/1.09  ------ Instantiation
% 2.55/1.09  
% 2.55/1.09  inst_num_of_clauses:                    548
% 2.55/1.09  inst_num_in_passive:                    218
% 2.55/1.09  inst_num_in_active:                     318
% 2.55/1.09  inst_num_in_unprocessed:                12
% 2.55/1.09  inst_num_of_loops:                      460
% 2.55/1.09  inst_num_of_learning_restarts:          0
% 2.55/1.09  inst_num_moves_active_passive:          137
% 2.55/1.09  inst_lit_activity:                      0
% 2.55/1.09  inst_lit_activity_moves:                0
% 2.55/1.09  inst_num_tautologies:                   0
% 2.55/1.09  inst_num_prop_implied:                  0
% 2.55/1.09  inst_num_existing_simplified:           0
% 2.55/1.09  inst_num_eq_res_simplified:             0
% 2.55/1.09  inst_num_child_elim:                    0
% 2.55/1.09  inst_num_of_dismatching_blockings:      108
% 2.55/1.09  inst_num_of_non_proper_insts:           490
% 2.55/1.09  inst_num_of_duplicates:                 0
% 2.55/1.09  inst_inst_num_from_inst_to_res:         0
% 2.55/1.09  inst_dismatching_checking_time:         0.
% 2.55/1.09  
% 2.55/1.09  ------ Resolution
% 2.55/1.09  
% 2.55/1.09  res_num_of_clauses:                     0
% 2.55/1.09  res_num_in_passive:                     0
% 2.55/1.09  res_num_in_active:                      0
% 2.55/1.09  res_num_of_loops:                       110
% 2.55/1.09  res_forward_subset_subsumed:            64
% 2.55/1.09  res_backward_subset_subsumed:           2
% 2.55/1.09  res_forward_subsumed:                   0
% 2.55/1.09  res_backward_subsumed:                  0
% 2.55/1.09  res_forward_subsumption_resolution:     0
% 2.55/1.09  res_backward_subsumption_resolution:    0
% 2.55/1.09  res_clause_to_clause_subsumption:       259
% 2.55/1.09  res_orphan_elimination:                 0
% 2.55/1.09  res_tautology_del:                      105
% 2.55/1.09  res_num_eq_res_simplified:              0
% 2.55/1.09  res_num_sel_changes:                    0
% 2.55/1.09  res_moves_from_active_to_pass:          0
% 2.55/1.09  
% 2.55/1.09  ------ Superposition
% 2.55/1.09  
% 2.55/1.09  sup_time_total:                         0.
% 2.55/1.09  sup_time_generating:                    0.
% 2.55/1.09  sup_time_sim_full:                      0.
% 2.55/1.09  sup_time_sim_immed:                     0.
% 2.55/1.09  
% 2.55/1.09  sup_num_of_clauses:                     77
% 2.55/1.09  sup_num_in_active:                      56
% 2.55/1.09  sup_num_in_passive:                     21
% 2.55/1.09  sup_num_of_loops:                       91
% 2.55/1.09  sup_fw_superposition:                   58
% 2.55/1.09  sup_bw_superposition:                   46
% 2.55/1.09  sup_immediate_simplified:               28
% 2.55/1.09  sup_given_eliminated:                   0
% 2.55/1.09  comparisons_done:                       0
% 2.55/1.09  comparisons_avoided:                    20
% 2.55/1.09  
% 2.55/1.09  ------ Simplifications
% 2.55/1.09  
% 2.55/1.09  
% 2.55/1.09  sim_fw_subset_subsumed:                 21
% 2.55/1.09  sim_bw_subset_subsumed:                 3
% 2.55/1.09  sim_fw_subsumed:                        0
% 2.55/1.09  sim_bw_subsumed:                        0
% 2.55/1.09  sim_fw_subsumption_res:                 2
% 2.55/1.09  sim_bw_subsumption_res:                 0
% 2.55/1.09  sim_tautology_del:                      0
% 2.55/1.09  sim_eq_tautology_del:                   3
% 2.55/1.09  sim_eq_res_simp:                        2
% 2.55/1.09  sim_fw_demodulated:                     1
% 2.55/1.09  sim_bw_demodulated:                     37
% 2.55/1.09  sim_light_normalised:                   9
% 2.55/1.09  sim_joinable_taut:                      0
% 2.55/1.09  sim_joinable_simp:                      0
% 2.55/1.09  sim_ac_normalised:                      0
% 2.55/1.09  sim_smt_subsumption:                    0
% 2.55/1.09  
%------------------------------------------------------------------------------
