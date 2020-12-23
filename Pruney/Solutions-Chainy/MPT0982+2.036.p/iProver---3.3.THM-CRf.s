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
% DateTime   : Thu Dec  3 12:01:44 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 571 expanded)
%              Number of clauses        :  109 ( 212 expanded)
%              Number of leaves         :   18 ( 131 expanded)
%              Depth                    :   22
%              Number of atoms          :  514 (3662 expanded)
%              Number of equality atoms :  238 (1248 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f38,f37])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f52,plain,(
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

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_647,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1039,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_649,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1037,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | k1_partfun1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53) = k5_relat_1(X3_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1036,plain,
    ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X4_53,X5_53) = k5_relat_1(X4_53,X5_53)
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_1895,plain,
    ( k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1036])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2049,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1895,c_34])).

cnf(c_2050,plain,
    ( k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2049])).

cnf(c_2056,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_2050])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2151,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2056,c_31])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
    | m1_subset_1(k1_partfun1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1034,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_2154,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2151,c_1034])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3899,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2154,c_31,c_33,c_34,c_36])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k2_relset_1(X1_53,X2_53,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1030,plain,
    ( k2_relset_1(X0_53,X1_53,X2_53) = k2_relat_1(X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_3912,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_3899,c_1030])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_650,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2153,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2151,c_650])).

cnf(c_3915,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3912,c_2153])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_343,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_6,c_2])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_319,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_323,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_27])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X3)) = X3
    | k1_relat_1(sK4) != X2
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_343,c_323])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relat_1(sK4))))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0))) = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4))))
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_363])).

cnf(c_1041,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4)))) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_724,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4)))) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1082,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0_53))
    | ~ v1_relat_1(X0_53)
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_1104,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_1138,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_1139,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_662,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1148,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_1149,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_2328,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4)))) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_36,c_724,c_1139,c_1149])).

cnf(c_2329,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4)))) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2328])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k1_relset_1(X1_53,X2_53,X0_53) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1029,plain,
    ( k1_relset_1(X0_53,X1_53,X2_53) = k1_relat_1(X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_1278,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1037,c_1029])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_460,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_462,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_25,c_22])).

cnf(c_640,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(subtyping,[status(esa)],[c_462])).

cnf(c_1280,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1278,c_640])).

cnf(c_2334,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2329,c_1280])).

cnf(c_2338,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_2334])).

cnf(c_1027,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_1026,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_1315,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_1026])).

cnf(c_1461,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1315])).

cnf(c_1314,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1026])).

cnf(c_1456,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1314,c_36,c_1139,c_1149])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_661,plain,
    ( ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k9_relat_1(X1_53,k2_relat_1(X0_53)) = k2_relat_1(k5_relat_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1028,plain,
    ( k9_relat_1(X0_53,k2_relat_1(X1_53)) = k2_relat_1(k5_relat_1(X1_53,X0_53))
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_1645,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0_53)) = k2_relat_1(k5_relat_1(X0_53,sK4))
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1028])).

cnf(c_1957,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1461,c_1645])).

cnf(c_2340,plain,
    ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2338,c_1957])).

cnf(c_2857,plain,
    ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2340,c_1461])).

cnf(c_3930,plain,
    ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3915,c_2857])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X2_53) = k1_relset_1(X1_53,X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1032,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X1_53) = k1_relset_1(X0_53,X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_1596,plain,
    ( k8_relset_1(sK1,sK2,sK4,sK2) = k1_relset_1(sK1,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1037,c_1032])).

cnf(c_1599,plain,
    ( k8_relset_1(sK1,sK2,sK4,sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1596,c_640])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1031,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_1546,plain,
    ( k8_relset_1(sK1,sK2,sK4,X0_53) = k10_relat_1(sK4,X0_53) ),
    inference(superposition,[status(thm)],[c_1037,c_1031])).

cnf(c_1703,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_1599,c_1546])).

cnf(c_3931,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3930,c_1703])).

cnf(c_1283,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1039,c_1030])).

cnf(c_667,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_1095,plain,
    ( X0_53 != X1_53
    | sK1 != X1_53
    | sK1 = X0_53 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1117,plain,
    ( X0_53 != sK1
    | sK1 = X0_53
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1235,plain,
    ( k2_relat_1(sK3) != sK1
    | sK1 = k2_relat_1(sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_1077,plain,
    ( k2_relset_1(sK0,sK1,sK3) != X0_53
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != X0_53 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1157,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_665,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1121,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_652,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3931,c_1283,c_1235,c_1157,c_1121,c_652])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:24:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.39/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.00  
% 3.39/1.00  ------  iProver source info
% 3.39/1.00  
% 3.39/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.00  git: non_committed_changes: false
% 3.39/1.00  git: last_make_outside_of_git: false
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options
% 3.39/1.00  
% 3.39/1.00  --out_options                           all
% 3.39/1.00  --tptp_safe_out                         true
% 3.39/1.00  --problem_path                          ""
% 3.39/1.00  --include_path                          ""
% 3.39/1.00  --clausifier                            res/vclausify_rel
% 3.39/1.00  --clausifier_options                    ""
% 3.39/1.00  --stdin                                 false
% 3.39/1.00  --stats_out                             all
% 3.39/1.00  
% 3.39/1.00  ------ General Options
% 3.39/1.00  
% 3.39/1.00  --fof                                   false
% 3.39/1.00  --time_out_real                         305.
% 3.39/1.00  --time_out_virtual                      -1.
% 3.39/1.00  --symbol_type_check                     false
% 3.39/1.00  --clausify_out                          false
% 3.39/1.00  --sig_cnt_out                           false
% 3.39/1.00  --trig_cnt_out                          false
% 3.39/1.00  --trig_cnt_out_tolerance                1.
% 3.39/1.00  --trig_cnt_out_sk_spl                   false
% 3.39/1.00  --abstr_cl_out                          false
% 3.39/1.00  
% 3.39/1.00  ------ Global Options
% 3.39/1.00  
% 3.39/1.00  --schedule                              default
% 3.39/1.00  --add_important_lit                     false
% 3.39/1.00  --prop_solver_per_cl                    1000
% 3.39/1.00  --min_unsat_core                        false
% 3.39/1.00  --soft_assumptions                      false
% 3.39/1.00  --soft_lemma_size                       3
% 3.39/1.00  --prop_impl_unit_size                   0
% 3.39/1.00  --prop_impl_unit                        []
% 3.39/1.00  --share_sel_clauses                     true
% 3.39/1.00  --reset_solvers                         false
% 3.39/1.00  --bc_imp_inh                            [conj_cone]
% 3.39/1.00  --conj_cone_tolerance                   3.
% 3.39/1.00  --extra_neg_conj                        none
% 3.39/1.00  --large_theory_mode                     true
% 3.39/1.00  --prolific_symb_bound                   200
% 3.39/1.00  --lt_threshold                          2000
% 3.39/1.00  --clause_weak_htbl                      true
% 3.39/1.00  --gc_record_bc_elim                     false
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing Options
% 3.39/1.00  
% 3.39/1.00  --preprocessing_flag                    true
% 3.39/1.00  --time_out_prep_mult                    0.1
% 3.39/1.00  --splitting_mode                        input
% 3.39/1.00  --splitting_grd                         true
% 3.39/1.00  --splitting_cvd                         false
% 3.39/1.00  --splitting_cvd_svl                     false
% 3.39/1.00  --splitting_nvd                         32
% 3.39/1.00  --sub_typing                            true
% 3.39/1.00  --prep_gs_sim                           true
% 3.39/1.00  --prep_unflatten                        true
% 3.39/1.00  --prep_res_sim                          true
% 3.39/1.00  --prep_upred                            true
% 3.39/1.00  --prep_sem_filter                       exhaustive
% 3.39/1.00  --prep_sem_filter_out                   false
% 3.39/1.00  --pred_elim                             true
% 3.39/1.00  --res_sim_input                         true
% 3.39/1.00  --eq_ax_congr_red                       true
% 3.39/1.00  --pure_diseq_elim                       true
% 3.39/1.00  --brand_transform                       false
% 3.39/1.00  --non_eq_to_eq                          false
% 3.39/1.00  --prep_def_merge                        true
% 3.39/1.00  --prep_def_merge_prop_impl              false
% 3.39/1.00  --prep_def_merge_mbd                    true
% 3.39/1.00  --prep_def_merge_tr_red                 false
% 3.39/1.00  --prep_def_merge_tr_cl                  false
% 3.39/1.00  --smt_preprocessing                     true
% 3.39/1.00  --smt_ac_axioms                         fast
% 3.39/1.00  --preprocessed_out                      false
% 3.39/1.00  --preprocessed_stats                    false
% 3.39/1.00  
% 3.39/1.00  ------ Abstraction refinement Options
% 3.39/1.00  
% 3.39/1.00  --abstr_ref                             []
% 3.39/1.00  --abstr_ref_prep                        false
% 3.39/1.00  --abstr_ref_until_sat                   false
% 3.39/1.00  --abstr_ref_sig_restrict                funpre
% 3.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/1.00  --abstr_ref_under                       []
% 3.39/1.00  
% 3.39/1.00  ------ SAT Options
% 3.39/1.00  
% 3.39/1.00  --sat_mode                              false
% 3.39/1.00  --sat_fm_restart_options                ""
% 3.39/1.00  --sat_gr_def                            false
% 3.39/1.00  --sat_epr_types                         true
% 3.39/1.00  --sat_non_cyclic_types                  false
% 3.39/1.00  --sat_finite_models                     false
% 3.39/1.00  --sat_fm_lemmas                         false
% 3.39/1.00  --sat_fm_prep                           false
% 3.39/1.00  --sat_fm_uc_incr                        true
% 3.39/1.00  --sat_out_model                         small
% 3.39/1.00  --sat_out_clauses                       false
% 3.39/1.00  
% 3.39/1.00  ------ QBF Options
% 3.39/1.00  
% 3.39/1.00  --qbf_mode                              false
% 3.39/1.00  --qbf_elim_univ                         false
% 3.39/1.00  --qbf_dom_inst                          none
% 3.39/1.00  --qbf_dom_pre_inst                      false
% 3.39/1.00  --qbf_sk_in                             false
% 3.39/1.00  --qbf_pred_elim                         true
% 3.39/1.00  --qbf_split                             512
% 3.39/1.00  
% 3.39/1.00  ------ BMC1 Options
% 3.39/1.00  
% 3.39/1.00  --bmc1_incremental                      false
% 3.39/1.00  --bmc1_axioms                           reachable_all
% 3.39/1.00  --bmc1_min_bound                        0
% 3.39/1.00  --bmc1_max_bound                        -1
% 3.39/1.00  --bmc1_max_bound_default                -1
% 3.39/1.00  --bmc1_symbol_reachability              true
% 3.39/1.00  --bmc1_property_lemmas                  false
% 3.39/1.00  --bmc1_k_induction                      false
% 3.39/1.00  --bmc1_non_equiv_states                 false
% 3.39/1.00  --bmc1_deadlock                         false
% 3.39/1.00  --bmc1_ucm                              false
% 3.39/1.00  --bmc1_add_unsat_core                   none
% 3.39/1.00  --bmc1_unsat_core_children              false
% 3.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/1.00  --bmc1_out_stat                         full
% 3.39/1.00  --bmc1_ground_init                      false
% 3.39/1.00  --bmc1_pre_inst_next_state              false
% 3.39/1.00  --bmc1_pre_inst_state                   false
% 3.39/1.00  --bmc1_pre_inst_reach_state             false
% 3.39/1.00  --bmc1_out_unsat_core                   false
% 3.39/1.00  --bmc1_aig_witness_out                  false
% 3.39/1.00  --bmc1_verbose                          false
% 3.39/1.00  --bmc1_dump_clauses_tptp                false
% 3.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.39/1.00  --bmc1_dump_file                        -
% 3.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.39/1.00  --bmc1_ucm_extend_mode                  1
% 3.39/1.00  --bmc1_ucm_init_mode                    2
% 3.39/1.00  --bmc1_ucm_cone_mode                    none
% 3.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.39/1.00  --bmc1_ucm_relax_model                  4
% 3.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/1.00  --bmc1_ucm_layered_model                none
% 3.39/1.00  --bmc1_ucm_max_lemma_size               10
% 3.39/1.00  
% 3.39/1.00  ------ AIG Options
% 3.39/1.00  
% 3.39/1.00  --aig_mode                              false
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation Options
% 3.39/1.00  
% 3.39/1.00  --instantiation_flag                    true
% 3.39/1.00  --inst_sos_flag                         true
% 3.39/1.00  --inst_sos_phase                        true
% 3.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel_side                     num_symb
% 3.39/1.00  --inst_solver_per_active                1400
% 3.39/1.00  --inst_solver_calls_frac                1.
% 3.39/1.00  --inst_passive_queue_type               priority_queues
% 3.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/1.00  --inst_passive_queues_freq              [25;2]
% 3.39/1.00  --inst_dismatching                      true
% 3.39/1.00  --inst_eager_unprocessed_to_passive     true
% 3.39/1.00  --inst_prop_sim_given                   true
% 3.39/1.00  --inst_prop_sim_new                     false
% 3.39/1.00  --inst_subs_new                         false
% 3.39/1.00  --inst_eq_res_simp                      false
% 3.39/1.00  --inst_subs_given                       false
% 3.39/1.00  --inst_orphan_elimination               true
% 3.39/1.00  --inst_learning_loop_flag               true
% 3.39/1.00  --inst_learning_start                   3000
% 3.39/1.00  --inst_learning_factor                  2
% 3.39/1.00  --inst_start_prop_sim_after_learn       3
% 3.39/1.00  --inst_sel_renew                        solver
% 3.39/1.00  --inst_lit_activity_flag                true
% 3.39/1.00  --inst_restr_to_given                   false
% 3.39/1.00  --inst_activity_threshold               500
% 3.39/1.00  --inst_out_proof                        true
% 3.39/1.00  
% 3.39/1.00  ------ Resolution Options
% 3.39/1.00  
% 3.39/1.00  --resolution_flag                       true
% 3.39/1.00  --res_lit_sel                           adaptive
% 3.39/1.00  --res_lit_sel_side                      none
% 3.39/1.00  --res_ordering                          kbo
% 3.39/1.00  --res_to_prop_solver                    active
% 3.39/1.00  --res_prop_simpl_new                    false
% 3.39/1.00  --res_prop_simpl_given                  true
% 3.39/1.00  --res_passive_queue_type                priority_queues
% 3.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/1.00  --res_passive_queues_freq               [15;5]
% 3.39/1.00  --res_forward_subs                      full
% 3.39/1.00  --res_backward_subs                     full
% 3.39/1.00  --res_forward_subs_resolution           true
% 3.39/1.00  --res_backward_subs_resolution          true
% 3.39/1.00  --res_orphan_elimination                true
% 3.39/1.00  --res_time_limit                        2.
% 3.39/1.00  --res_out_proof                         true
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Options
% 3.39/1.00  
% 3.39/1.00  --superposition_flag                    true
% 3.39/1.00  --sup_passive_queue_type                priority_queues
% 3.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.39/1.00  --demod_completeness_check              fast
% 3.39/1.00  --demod_use_ground                      true
% 3.39/1.00  --sup_to_prop_solver                    passive
% 3.39/1.00  --sup_prop_simpl_new                    true
% 3.39/1.00  --sup_prop_simpl_given                  true
% 3.39/1.00  --sup_fun_splitting                     true
% 3.39/1.00  --sup_smt_interval                      50000
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Simplification Setup
% 3.39/1.00  
% 3.39/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.39/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.39/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.39/1.00  --sup_immed_triv                        [TrivRules]
% 3.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_bw_main                     []
% 3.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_input_bw                          []
% 3.39/1.00  
% 3.39/1.00  ------ Combination Options
% 3.39/1.00  
% 3.39/1.00  --comb_res_mult                         3
% 3.39/1.00  --comb_sup_mult                         2
% 3.39/1.00  --comb_inst_mult                        10
% 3.39/1.00  
% 3.39/1.00  ------ Debug Options
% 3.39/1.00  
% 3.39/1.00  --dbg_backtrace                         false
% 3.39/1.00  --dbg_dump_prop_clauses                 false
% 3.39/1.00  --dbg_dump_prop_clauses_file            -
% 3.39/1.00  --dbg_out_stat                          false
% 3.39/1.00  ------ Parsing...
% 3.39/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.00  ------ Proving...
% 3.39/1.00  ------ Problem Properties 
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  clauses                                 25
% 3.39/1.00  conjectures                             7
% 3.39/1.00  EPR                                     3
% 3.39/1.00  Horn                                    22
% 3.39/1.00  unary                                   9
% 3.39/1.00  binary                                  6
% 3.39/1.00  lits                                    60
% 3.39/1.00  lits eq                                 24
% 3.39/1.00  fd_pure                                 0
% 3.39/1.00  fd_pseudo                               0
% 3.39/1.00  fd_cond                                 0
% 3.39/1.00  fd_pseudo_cond                          0
% 3.39/1.00  AC symbols                              0
% 3.39/1.00  
% 3.39/1.00  ------ Schedule dynamic 5 is on 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  Current options:
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options
% 3.39/1.00  
% 3.39/1.00  --out_options                           all
% 3.39/1.00  --tptp_safe_out                         true
% 3.39/1.00  --problem_path                          ""
% 3.39/1.00  --include_path                          ""
% 3.39/1.00  --clausifier                            res/vclausify_rel
% 3.39/1.00  --clausifier_options                    ""
% 3.39/1.00  --stdin                                 false
% 3.39/1.00  --stats_out                             all
% 3.39/1.00  
% 3.39/1.00  ------ General Options
% 3.39/1.00  
% 3.39/1.00  --fof                                   false
% 3.39/1.00  --time_out_real                         305.
% 3.39/1.00  --time_out_virtual                      -1.
% 3.39/1.00  --symbol_type_check                     false
% 3.39/1.00  --clausify_out                          false
% 3.39/1.00  --sig_cnt_out                           false
% 3.39/1.00  --trig_cnt_out                          false
% 3.39/1.00  --trig_cnt_out_tolerance                1.
% 3.39/1.00  --trig_cnt_out_sk_spl                   false
% 3.39/1.00  --abstr_cl_out                          false
% 3.39/1.00  
% 3.39/1.00  ------ Global Options
% 3.39/1.00  
% 3.39/1.00  --schedule                              default
% 3.39/1.00  --add_important_lit                     false
% 3.39/1.00  --prop_solver_per_cl                    1000
% 3.39/1.00  --min_unsat_core                        false
% 3.39/1.00  --soft_assumptions                      false
% 3.39/1.00  --soft_lemma_size                       3
% 3.39/1.00  --prop_impl_unit_size                   0
% 3.39/1.00  --prop_impl_unit                        []
% 3.39/1.00  --share_sel_clauses                     true
% 3.39/1.00  --reset_solvers                         false
% 3.39/1.00  --bc_imp_inh                            [conj_cone]
% 3.39/1.00  --conj_cone_tolerance                   3.
% 3.39/1.00  --extra_neg_conj                        none
% 3.39/1.00  --large_theory_mode                     true
% 3.39/1.00  --prolific_symb_bound                   200
% 3.39/1.00  --lt_threshold                          2000
% 3.39/1.00  --clause_weak_htbl                      true
% 3.39/1.00  --gc_record_bc_elim                     false
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing Options
% 3.39/1.00  
% 3.39/1.00  --preprocessing_flag                    true
% 3.39/1.00  --time_out_prep_mult                    0.1
% 3.39/1.00  --splitting_mode                        input
% 3.39/1.00  --splitting_grd                         true
% 3.39/1.00  --splitting_cvd                         false
% 3.39/1.00  --splitting_cvd_svl                     false
% 3.39/1.00  --splitting_nvd                         32
% 3.39/1.00  --sub_typing                            true
% 3.39/1.00  --prep_gs_sim                           true
% 3.39/1.00  --prep_unflatten                        true
% 3.39/1.00  --prep_res_sim                          true
% 3.39/1.00  --prep_upred                            true
% 3.39/1.00  --prep_sem_filter                       exhaustive
% 3.39/1.00  --prep_sem_filter_out                   false
% 3.39/1.00  --pred_elim                             true
% 3.39/1.00  --res_sim_input                         true
% 3.39/1.00  --eq_ax_congr_red                       true
% 3.39/1.00  --pure_diseq_elim                       true
% 3.39/1.00  --brand_transform                       false
% 3.39/1.00  --non_eq_to_eq                          false
% 3.39/1.00  --prep_def_merge                        true
% 3.39/1.00  --prep_def_merge_prop_impl              false
% 3.39/1.00  --prep_def_merge_mbd                    true
% 3.39/1.00  --prep_def_merge_tr_red                 false
% 3.39/1.00  --prep_def_merge_tr_cl                  false
% 3.39/1.00  --smt_preprocessing                     true
% 3.39/1.00  --smt_ac_axioms                         fast
% 3.39/1.00  --preprocessed_out                      false
% 3.39/1.00  --preprocessed_stats                    false
% 3.39/1.00  
% 3.39/1.00  ------ Abstraction refinement Options
% 3.39/1.00  
% 3.39/1.00  --abstr_ref                             []
% 3.39/1.00  --abstr_ref_prep                        false
% 3.39/1.00  --abstr_ref_until_sat                   false
% 3.39/1.00  --abstr_ref_sig_restrict                funpre
% 3.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/1.00  --abstr_ref_under                       []
% 3.39/1.00  
% 3.39/1.00  ------ SAT Options
% 3.39/1.00  
% 3.39/1.00  --sat_mode                              false
% 3.39/1.00  --sat_fm_restart_options                ""
% 3.39/1.00  --sat_gr_def                            false
% 3.39/1.00  --sat_epr_types                         true
% 3.39/1.00  --sat_non_cyclic_types                  false
% 3.39/1.00  --sat_finite_models                     false
% 3.39/1.00  --sat_fm_lemmas                         false
% 3.39/1.00  --sat_fm_prep                           false
% 3.39/1.00  --sat_fm_uc_incr                        true
% 3.39/1.00  --sat_out_model                         small
% 3.39/1.00  --sat_out_clauses                       false
% 3.39/1.00  
% 3.39/1.00  ------ QBF Options
% 3.39/1.00  
% 3.39/1.00  --qbf_mode                              false
% 3.39/1.00  --qbf_elim_univ                         false
% 3.39/1.00  --qbf_dom_inst                          none
% 3.39/1.00  --qbf_dom_pre_inst                      false
% 3.39/1.00  --qbf_sk_in                             false
% 3.39/1.00  --qbf_pred_elim                         true
% 3.39/1.00  --qbf_split                             512
% 3.39/1.00  
% 3.39/1.00  ------ BMC1 Options
% 3.39/1.00  
% 3.39/1.00  --bmc1_incremental                      false
% 3.39/1.00  --bmc1_axioms                           reachable_all
% 3.39/1.00  --bmc1_min_bound                        0
% 3.39/1.00  --bmc1_max_bound                        -1
% 3.39/1.00  --bmc1_max_bound_default                -1
% 3.39/1.00  --bmc1_symbol_reachability              true
% 3.39/1.00  --bmc1_property_lemmas                  false
% 3.39/1.00  --bmc1_k_induction                      false
% 3.39/1.00  --bmc1_non_equiv_states                 false
% 3.39/1.00  --bmc1_deadlock                         false
% 3.39/1.00  --bmc1_ucm                              false
% 3.39/1.00  --bmc1_add_unsat_core                   none
% 3.39/1.00  --bmc1_unsat_core_children              false
% 3.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/1.00  --bmc1_out_stat                         full
% 3.39/1.00  --bmc1_ground_init                      false
% 3.39/1.00  --bmc1_pre_inst_next_state              false
% 3.39/1.00  --bmc1_pre_inst_state                   false
% 3.39/1.00  --bmc1_pre_inst_reach_state             false
% 3.39/1.00  --bmc1_out_unsat_core                   false
% 3.39/1.00  --bmc1_aig_witness_out                  false
% 3.39/1.00  --bmc1_verbose                          false
% 3.39/1.00  --bmc1_dump_clauses_tptp                false
% 3.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.39/1.00  --bmc1_dump_file                        -
% 3.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.39/1.00  --bmc1_ucm_extend_mode                  1
% 3.39/1.00  --bmc1_ucm_init_mode                    2
% 3.39/1.00  --bmc1_ucm_cone_mode                    none
% 3.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.39/1.00  --bmc1_ucm_relax_model                  4
% 3.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/1.00  --bmc1_ucm_layered_model                none
% 3.39/1.00  --bmc1_ucm_max_lemma_size               10
% 3.39/1.00  
% 3.39/1.00  ------ AIG Options
% 3.39/1.00  
% 3.39/1.00  --aig_mode                              false
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation Options
% 3.39/1.00  
% 3.39/1.00  --instantiation_flag                    true
% 3.39/1.00  --inst_sos_flag                         true
% 3.39/1.00  --inst_sos_phase                        true
% 3.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel_side                     none
% 3.39/1.00  --inst_solver_per_active                1400
% 3.39/1.00  --inst_solver_calls_frac                1.
% 3.39/1.00  --inst_passive_queue_type               priority_queues
% 3.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/1.00  --inst_passive_queues_freq              [25;2]
% 3.39/1.00  --inst_dismatching                      true
% 3.39/1.00  --inst_eager_unprocessed_to_passive     true
% 3.39/1.00  --inst_prop_sim_given                   true
% 3.39/1.00  --inst_prop_sim_new                     false
% 3.39/1.00  --inst_subs_new                         false
% 3.39/1.00  --inst_eq_res_simp                      false
% 3.39/1.00  --inst_subs_given                       false
% 3.39/1.00  --inst_orphan_elimination               true
% 3.39/1.00  --inst_learning_loop_flag               true
% 3.39/1.00  --inst_learning_start                   3000
% 3.39/1.00  --inst_learning_factor                  2
% 3.39/1.00  --inst_start_prop_sim_after_learn       3
% 3.39/1.00  --inst_sel_renew                        solver
% 3.39/1.00  --inst_lit_activity_flag                true
% 3.39/1.00  --inst_restr_to_given                   false
% 3.39/1.00  --inst_activity_threshold               500
% 3.39/1.00  --inst_out_proof                        true
% 3.39/1.00  
% 3.39/1.00  ------ Resolution Options
% 3.39/1.00  
% 3.39/1.00  --resolution_flag                       false
% 3.39/1.00  --res_lit_sel                           adaptive
% 3.39/1.00  --res_lit_sel_side                      none
% 3.39/1.00  --res_ordering                          kbo
% 3.39/1.00  --res_to_prop_solver                    active
% 3.39/1.00  --res_prop_simpl_new                    false
% 3.39/1.00  --res_prop_simpl_given                  true
% 3.39/1.00  --res_passive_queue_type                priority_queues
% 3.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/1.00  --res_passive_queues_freq               [15;5]
% 3.39/1.00  --res_forward_subs                      full
% 3.39/1.00  --res_backward_subs                     full
% 3.39/1.00  --res_forward_subs_resolution           true
% 3.39/1.00  --res_backward_subs_resolution          true
% 3.39/1.00  --res_orphan_elimination                true
% 3.39/1.00  --res_time_limit                        2.
% 3.39/1.00  --res_out_proof                         true
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Options
% 3.39/1.00  
% 3.39/1.00  --superposition_flag                    true
% 3.39/1.00  --sup_passive_queue_type                priority_queues
% 3.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.39/1.00  --demod_completeness_check              fast
% 3.39/1.00  --demod_use_ground                      true
% 3.39/1.00  --sup_to_prop_solver                    passive
% 3.39/1.00  --sup_prop_simpl_new                    true
% 3.39/1.00  --sup_prop_simpl_given                  true
% 3.39/1.00  --sup_fun_splitting                     true
% 3.39/1.00  --sup_smt_interval                      50000
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Simplification Setup
% 3.39/1.00  
% 3.39/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.39/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.39/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.39/1.00  --sup_immed_triv                        [TrivRules]
% 3.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_bw_main                     []
% 3.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_input_bw                          []
% 3.39/1.00  
% 3.39/1.00  ------ Combination Options
% 3.39/1.00  
% 3.39/1.00  --comb_res_mult                         3
% 3.39/1.00  --comb_sup_mult                         2
% 3.39/1.00  --comb_inst_mult                        10
% 3.39/1.00  
% 3.39/1.00  ------ Debug Options
% 3.39/1.00  
% 3.39/1.00  --dbg_backtrace                         false
% 3.39/1.00  --dbg_dump_prop_clauses                 false
% 3.39/1.00  --dbg_dump_prop_clauses_file            -
% 3.39/1.00  --dbg_out_stat                          false
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ Proving...
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS status Theorem for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  fof(f14,conjecture,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f15,negated_conjecture,(
% 3.39/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 3.39/1.00    inference(negated_conjecture,[],[f14])).
% 3.39/1.00  
% 3.39/1.00  fof(f33,plain,(
% 3.39/1.00    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.39/1.00    inference(ennf_transformation,[],[f15])).
% 3.39/1.00  
% 3.39/1.00  fof(f34,plain,(
% 3.39/1.00    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.39/1.00    inference(flattening,[],[f33])).
% 3.39/1.00  
% 3.39/1.00  fof(f38,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f37,plain,(
% 3.39/1.00    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f39,plain,(
% 3.39/1.00    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f38,f37])).
% 3.39/1.00  
% 3.39/1.00  fof(f63,plain,(
% 3.39/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f66,plain,(
% 3.39/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f13,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f31,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.39/1.00    inference(ennf_transformation,[],[f13])).
% 3.39/1.00  
% 3.39/1.00  fof(f32,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.39/1.00    inference(flattening,[],[f31])).
% 3.39/1.00  
% 3.39/1.00  fof(f60,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f32])).
% 3.39/1.00  
% 3.39/1.00  fof(f64,plain,(
% 3.39/1.00    v1_funct_1(sK4)),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f61,plain,(
% 3.39/1.00    v1_funct_1(sK3)),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f12,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f29,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.39/1.00    inference(ennf_transformation,[],[f12])).
% 3.39/1.00  
% 3.39/1.00  fof(f30,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.39/1.00    inference(flattening,[],[f29])).
% 3.39/1.00  
% 3.39/1.00  fof(f59,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f30])).
% 3.39/1.00  
% 3.39/1.00  fof(f8,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f24,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f8])).
% 3.39/1.00  
% 3.39/1.00  fof(f48,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f24])).
% 3.39/1.00  
% 3.39/1.00  fof(f67,plain,(
% 3.39/1.00    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f6,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f16,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.39/1.00    inference(pure_predicate_removal,[],[f6])).
% 3.39/1.00  
% 3.39/1.00  fof(f22,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f16])).
% 3.39/1.00  
% 3.39/1.00  fof(f46,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f22])).
% 3.39/1.00  
% 3.39/1.00  fof(f2,axiom,(
% 3.39/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f18,plain,(
% 3.39/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f2])).
% 3.39/1.00  
% 3.39/1.00  fof(f35,plain,(
% 3.39/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.39/1.00    inference(nnf_transformation,[],[f18])).
% 3.39/1.00  
% 3.39/1.00  fof(f41,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f35])).
% 3.39/1.00  
% 3.39/1.00  fof(f5,axiom,(
% 3.39/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f20,plain,(
% 3.39/1.00    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.39/1.00    inference(ennf_transformation,[],[f5])).
% 3.39/1.00  
% 3.39/1.00  fof(f21,plain,(
% 3.39/1.00    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.39/1.00    inference(flattening,[],[f20])).
% 3.39/1.00  
% 3.39/1.00  fof(f45,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f21])).
% 3.39/1.00  
% 3.39/1.00  fof(f68,plain,(
% 3.39/1.00    v2_funct_1(sK4)),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f1,axiom,(
% 3.39/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f17,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f1])).
% 3.39/1.00  
% 3.39/1.00  fof(f40,plain,(
% 3.39/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f17])).
% 3.39/1.00  
% 3.39/1.00  fof(f3,axiom,(
% 3.39/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f43,plain,(
% 3.39/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f3])).
% 3.39/1.00  
% 3.39/1.00  fof(f7,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f23,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f7])).
% 3.39/1.00  
% 3.39/1.00  fof(f47,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f23])).
% 3.39/1.00  
% 3.39/1.00  fof(f11,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f27,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f11])).
% 3.39/1.00  
% 3.39/1.00  fof(f28,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(flattening,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f36,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(nnf_transformation,[],[f28])).
% 3.39/1.00  
% 3.39/1.00  fof(f52,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f36])).
% 3.39/1.00  
% 3.39/1.00  fof(f65,plain,(
% 3.39/1.00    v1_funct_2(sK4,sK1,sK2)),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f69,plain,(
% 3.39/1.00    k1_xboole_0 != sK2),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f4,axiom,(
% 3.39/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f19,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f4])).
% 3.39/1.00  
% 3.39/1.00  fof(f44,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f19])).
% 3.39/1.00  
% 3.39/1.00  fof(f10,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f26,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f10])).
% 3.39/1.00  
% 3.39/1.00  fof(f51,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f26])).
% 3.39/1.00  
% 3.39/1.00  fof(f9,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f25,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f9])).
% 3.39/1.00  
% 3.39/1.00  fof(f49,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f25])).
% 3.39/1.00  
% 3.39/1.00  fof(f70,plain,(
% 3.39/1.00    k2_relset_1(sK0,sK1,sK3) != sK1),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  cnf(c_28,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_647,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1039,plain,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_25,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_649,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1037,plain,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_20,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X3)
% 3.39/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_653,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.39/1.00      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
% 3.39/1.00      | ~ v1_funct_1(X0_53)
% 3.39/1.00      | ~ v1_funct_1(X3_53)
% 3.39/1.00      | k1_partfun1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53) = k5_relat_1(X3_53,X0_53) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1036,plain,
% 3.39/1.00      ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X4_53,X5_53) = k5_relat_1(X4_53,X5_53)
% 3.39/1.00      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 3.39/1.00      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.39/1.00      | v1_funct_1(X5_53) != iProver_top
% 3.39/1.00      | v1_funct_1(X4_53) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1895,plain,
% 3.39/1.00      ( k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
% 3.39/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.39/1.00      | v1_funct_1(X2_53) != iProver_top
% 3.39/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1037,c_1036]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_27,negated_conjecture,
% 3.39/1.00      ( v1_funct_1(sK4) ),
% 3.39/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_34,plain,
% 3.39/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2049,plain,
% 3.39/1.00      ( v1_funct_1(X2_53) != iProver_top
% 3.39/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.39/1.00      | k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_1895,c_34]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2050,plain,
% 3.39/1.00      ( k1_partfun1(X0_53,X1_53,sK1,sK2,X2_53,sK4) = k5_relat_1(X2_53,sK4)
% 3.39/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.39/1.00      | v1_funct_1(X2_53) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_2049]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2056,plain,
% 3.39/1.00      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1039,c_2050]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_30,negated_conjecture,
% 3.39/1.00      ( v1_funct_1(sK3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_31,plain,
% 3.39/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2151,plain,
% 3.39/1.00      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_2056,c_31]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_18,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.39/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_655,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.39/1.00      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53)))
% 3.39/1.00      | m1_subset_1(k1_partfun1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 3.39/1.00      | ~ v1_funct_1(X0_53)
% 3.39/1.00      | ~ v1_funct_1(X3_53) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1034,plain,
% 3.39/1.00      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 3.39/1.00      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X5_53))) != iProver_top
% 3.39/1.00      | m1_subset_1(k1_partfun1(X4_53,X5_53,X1_53,X2_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) = iProver_top
% 3.39/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.39/1.00      | v1_funct_1(X3_53) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2154,plain,
% 3.39/1.00      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.39/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.39/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.39/1.00      | v1_funct_1(sK4) != iProver_top
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2151,c_1034]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_33,plain,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_36,plain,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3899,plain,
% 3.39/1.00      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_2154,c_31,c_33,c_34,c_36]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_659,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.39/1.00      | k2_relset_1(X1_53,X2_53,X0_53) = k2_relat_1(X0_53) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1030,plain,
% 3.39/1.00      ( k2_relset_1(X0_53,X1_53,X2_53) = k2_relat_1(X2_53)
% 3.39/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3912,plain,
% 3.39/1.00      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_3899,c_1030]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_24,negated_conjecture,
% 3.39/1.00      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_650,negated_conjecture,
% 3.39/1.00      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2153,plain,
% 3.39/1.00      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_2151,c_650]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3915,plain,
% 3.39/1.00      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_3912,c_2153]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6,plain,
% 3.39/1.00      ( v5_relat_1(X0,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2,plain,
% 3.39/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 3.39/1.00      | ~ v5_relat_1(X0,X1)
% 3.39/1.00      | ~ v1_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_343,plain,
% 3.39/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.39/1.00      | ~ v1_relat_1(X0) ),
% 3.39/1.00      inference(resolution,[status(thm)],[c_6,c_2]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.39/1.00      | ~ v1_funct_1(X1)
% 3.39/1.00      | ~ v2_funct_1(X1)
% 3.39/1.00      | ~ v1_relat_1(X1)
% 3.39/1.00      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_23,negated_conjecture,
% 3.39/1.00      ( v2_funct_1(sK4) ),
% 3.39/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_318,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.39/1.00      | ~ v1_funct_1(X1)
% 3.39/1.00      | ~ v1_relat_1(X1)
% 3.39/1.00      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.39/1.00      | sK4 != X1 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_319,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.39/1.00      | ~ v1_funct_1(sK4)
% 3.39/1.00      | ~ v1_relat_1(sK4)
% 3.39/1.00      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.39/1.00      inference(unflattening,[status(thm)],[c_318]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_323,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.39/1.00      | ~ v1_relat_1(sK4)
% 3.39/1.00      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_319,c_27]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_362,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ v1_relat_1(X0)
% 3.39/1.00      | ~ v1_relat_1(sK4)
% 3.39/1.00      | k10_relat_1(sK4,k9_relat_1(sK4,X3)) = X3
% 3.39/1.00      | k1_relat_1(sK4) != X2
% 3.39/1.00      | k2_relat_1(X0) != X3 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_343,c_323]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_363,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relat_1(sK4))))
% 3.39/1.00      | ~ v1_relat_1(X0)
% 3.39/1.00      | ~ v1_relat_1(sK4)
% 3.39/1.00      | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0))) = k2_relat_1(X0) ),
% 3.39/1.00      inference(unflattening,[status(thm)],[c_362]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_645,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4))))
% 3.39/1.00      | ~ v1_relat_1(X0_53)
% 3.39/1.00      | ~ v1_relat_1(sK4)
% 3.39/1.00      | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_363]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1041,plain,
% 3.39/1.00      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53)
% 3.39/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4)))) != iProver_top
% 3.39/1.00      | v1_relat_1(X0_53) != iProver_top
% 3.39/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_724,plain,
% 3.39/1.00      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53)
% 3.39/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4)))) != iProver_top
% 3.39/1.00      | v1_relat_1(X0_53) != iProver_top
% 3.39/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_0,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.39/1.00      | ~ v1_relat_1(X1)
% 3.39/1.00      | v1_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_663,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 3.39/1.00      | ~ v1_relat_1(X1_53)
% 3.39/1.00      | v1_relat_1(X0_53) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1082,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0_53))
% 3.39/1.00      | ~ v1_relat_1(X0_53)
% 3.39/1.00      | v1_relat_1(sK4) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_663]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1104,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.39/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53))
% 3.39/1.00      | v1_relat_1(sK4) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1082]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1138,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.39/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 3.39/1.00      | v1_relat_1(sK4) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1104]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1139,plain,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.39/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.39/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3,plain,
% 3.39/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_662,plain,
% 3.39/1.00      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1148,plain,
% 3.39/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_662]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1149,plain,
% 3.39/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2328,plain,
% 3.39/1.00      ( v1_relat_1(X0_53) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4)))) != iProver_top
% 3.39/1.00      | k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_1041,c_36,c_724,c_1139,c_1149]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2329,plain,
% 3.39/1.00      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53)
% 3.39/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,k1_relat_1(sK4)))) != iProver_top
% 3.39/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_2328]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_660,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.39/1.00      | k1_relset_1(X1_53,X2_53,X0_53) = k1_relat_1(X0_53) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1029,plain,
% 3.39/1.00      ( k1_relset_1(X0_53,X1_53,X2_53) = k1_relat_1(X2_53)
% 3.39/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1278,plain,
% 3.39/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1037,c_1029]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_17,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_26,negated_conjecture,
% 3.39/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.39/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_459,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.39/1.00      | sK4 != X0
% 3.39/1.00      | sK2 != X2
% 3.39/1.00      | sK1 != X1
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_460,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.39/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.39/1.00      | k1_xboole_0 = sK2 ),
% 3.39/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_22,negated_conjecture,
% 3.39/1.00      ( k1_xboole_0 != sK2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_462,plain,
% 3.39/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_460,c_25,c_22]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_640,plain,
% 3.39/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_462]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1280,plain,
% 3.39/1.00      ( k1_relat_1(sK4) = sK1 ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_1278,c_640]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2334,plain,
% 3.39/1.00      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(X0_53))) = k2_relat_1(X0_53)
% 3.39/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 3.39/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_2329,c_1280]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2338,plain,
% 3.39/1.00      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3)
% 3.39/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1039,c_2334]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1027,plain,
% 3.39/1.00      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1026,plain,
% 3.39/1.00      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 3.39/1.00      | v1_relat_1(X1_53) != iProver_top
% 3.39/1.00      | v1_relat_1(X0_53) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1315,plain,
% 3.39/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.39/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1039,c_1026]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1461,plain,
% 3.39/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1027,c_1315]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1314,plain,
% 3.39/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.39/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1037,c_1026]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1456,plain,
% 3.39/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_1314,c_36,c_1139,c_1149]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4,plain,
% 3.39/1.00      ( ~ v1_relat_1(X0)
% 3.39/1.00      | ~ v1_relat_1(X1)
% 3.39/1.00      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_661,plain,
% 3.39/1.00      ( ~ v1_relat_1(X0_53)
% 3.39/1.00      | ~ v1_relat_1(X1_53)
% 3.39/1.00      | k9_relat_1(X1_53,k2_relat_1(X0_53)) = k2_relat_1(k5_relat_1(X0_53,X1_53)) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1028,plain,
% 3.39/1.00      ( k9_relat_1(X0_53,k2_relat_1(X1_53)) = k2_relat_1(k5_relat_1(X1_53,X0_53))
% 3.39/1.00      | v1_relat_1(X1_53) != iProver_top
% 3.39/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1645,plain,
% 3.39/1.00      ( k9_relat_1(sK4,k2_relat_1(X0_53)) = k2_relat_1(k5_relat_1(X0_53,sK4))
% 3.39/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1456,c_1028]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1957,plain,
% 3.39/1.00      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1461,c_1645]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2340,plain,
% 3.39/1.00      ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3)
% 3.39/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_2338,c_1957]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2857,plain,
% 3.39/1.00      ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_2340,c_1461]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3930,plain,
% 3.39/1.00      ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_3915,c_2857]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_657,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.39/1.00      | k8_relset_1(X1_53,X2_53,X0_53,X2_53) = k1_relset_1(X1_53,X2_53,X0_53) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1032,plain,
% 3.39/1.00      ( k8_relset_1(X0_53,X1_53,X2_53,X1_53) = k1_relset_1(X0_53,X1_53,X2_53)
% 3.39/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1596,plain,
% 3.39/1.00      ( k8_relset_1(sK1,sK2,sK4,sK2) = k1_relset_1(sK1,sK2,sK4) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1037,c_1032]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1599,plain,
% 3.39/1.00      ( k8_relset_1(sK1,sK2,sK4,sK2) = sK1 ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_1596,c_640]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_658,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.39/1.00      | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1031,plain,
% 3.39/1.00      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 3.39/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1546,plain,
% 3.39/1.00      ( k8_relset_1(sK1,sK2,sK4,X0_53) = k10_relat_1(sK4,X0_53) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1037,c_1031]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1703,plain,
% 3.39/1.00      ( k10_relat_1(sK4,sK2) = sK1 ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1599,c_1546]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3931,plain,
% 3.39/1.00      ( k2_relat_1(sK3) = sK1 ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_3930,c_1703]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1283,plain,
% 3.39/1.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1039,c_1030]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_667,plain,
% 3.39/1.00      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 3.39/1.00      theory(equality) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1095,plain,
% 3.39/1.00      ( X0_53 != X1_53 | sK1 != X1_53 | sK1 = X0_53 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_667]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1117,plain,
% 3.39/1.00      ( X0_53 != sK1 | sK1 = X0_53 | sK1 != sK1 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1095]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1235,plain,
% 3.39/1.00      ( k2_relat_1(sK3) != sK1 | sK1 = k2_relat_1(sK3) | sK1 != sK1 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1117]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1077,plain,
% 3.39/1.00      ( k2_relset_1(sK0,sK1,sK3) != X0_53
% 3.39/1.00      | k2_relset_1(sK0,sK1,sK3) = sK1
% 3.39/1.00      | sK1 != X0_53 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_667]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1157,plain,
% 3.39/1.00      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 3.39/1.00      | k2_relset_1(sK0,sK1,sK3) = sK1
% 3.39/1.00      | sK1 != k2_relat_1(sK3) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1077]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_665,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1121,plain,
% 3.39/1.00      ( sK1 = sK1 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_665]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_21,negated_conjecture,
% 3.39/1.00      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.39/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_652,negated_conjecture,
% 3.39/1.00      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(contradiction,plain,
% 3.39/1.00      ( $false ),
% 3.39/1.00      inference(minisat,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_3931,c_1283,c_1235,c_1157,c_1121,c_652]) ).
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  ------                               Statistics
% 3.39/1.00  
% 3.39/1.00  ------ General
% 3.39/1.00  
% 3.39/1.00  abstr_ref_over_cycles:                  0
% 3.39/1.00  abstr_ref_under_cycles:                 0
% 3.39/1.00  gc_basic_clause_elim:                   0
% 3.39/1.00  forced_gc_time:                         0
% 3.39/1.00  parsing_time:                           0.014
% 3.39/1.00  unif_index_cands_time:                  0.
% 3.39/1.00  unif_index_add_time:                    0.
% 3.39/1.00  orderings_time:                         0.
% 3.39/1.00  out_proof_time:                         0.03
% 3.39/1.00  total_time:                             0.242
% 3.39/1.00  num_of_symbols:                         58
% 3.39/1.00  num_of_terms:                           4657
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing
% 3.39/1.00  
% 3.39/1.00  num_of_splits:                          0
% 3.39/1.00  num_of_split_atoms:                     0
% 3.39/1.00  num_of_reused_defs:                     0
% 3.39/1.00  num_eq_ax_congr_red:                    37
% 3.39/1.00  num_of_sem_filtered_clauses:            1
% 3.39/1.00  num_of_subtypes:                        2
% 3.39/1.00  monotx_restored_types:                  0
% 3.39/1.00  sat_num_of_epr_types:                   0
% 3.39/1.00  sat_num_of_non_cyclic_types:            0
% 3.39/1.00  sat_guarded_non_collapsed_types:        0
% 3.39/1.00  num_pure_diseq_elim:                    0
% 3.39/1.00  simp_replaced_by:                       0
% 3.39/1.00  res_preprocessed:                       137
% 3.39/1.00  prep_upred:                             0
% 3.39/1.00  prep_unflattend:                        37
% 3.39/1.00  smt_new_axioms:                         0
% 3.39/1.00  pred_elim_cands:                        3
% 3.39/1.00  pred_elim:                              4
% 3.39/1.00  pred_elim_cl:                           6
% 3.39/1.00  pred_elim_cycles:                       6
% 3.39/1.00  merged_defs:                            0
% 3.39/1.00  merged_defs_ncl:                        0
% 3.39/1.00  bin_hyper_res:                          0
% 3.39/1.00  prep_cycles:                            4
% 3.39/1.00  pred_elim_time:                         0.008
% 3.39/1.00  splitting_time:                         0.
% 3.39/1.00  sem_filter_time:                        0.
% 3.39/1.00  monotx_time:                            0.
% 3.39/1.00  subtype_inf_time:                       0.
% 3.39/1.00  
% 3.39/1.00  ------ Problem properties
% 3.39/1.00  
% 3.39/1.00  clauses:                                25
% 3.39/1.00  conjectures:                            7
% 3.39/1.00  epr:                                    3
% 3.39/1.00  horn:                                   22
% 3.39/1.00  ground:                                 13
% 3.39/1.00  unary:                                  9
% 3.39/1.00  binary:                                 6
% 3.39/1.00  lits:                                   60
% 3.39/1.00  lits_eq:                                24
% 3.39/1.00  fd_pure:                                0
% 3.39/1.00  fd_pseudo:                              0
% 3.39/1.00  fd_cond:                                0
% 3.39/1.00  fd_pseudo_cond:                         0
% 3.39/1.00  ac_symbols:                             0
% 3.39/1.00  
% 3.39/1.00  ------ Propositional Solver
% 3.39/1.00  
% 3.39/1.00  prop_solver_calls:                      31
% 3.39/1.00  prop_fast_solver_calls:                 956
% 3.39/1.00  smt_solver_calls:                       0
% 3.39/1.00  smt_fast_solver_calls:                  0
% 3.39/1.00  prop_num_of_clauses:                    1477
% 3.39/1.00  prop_preprocess_simplified:             4384
% 3.39/1.00  prop_fo_subsumed:                       49
% 3.39/1.00  prop_solver_time:                       0.
% 3.39/1.00  smt_solver_time:                        0.
% 3.39/1.00  smt_fast_solver_time:                   0.
% 3.39/1.00  prop_fast_solver_time:                  0.
% 3.39/1.00  prop_unsat_core_time:                   0.
% 3.39/1.00  
% 3.39/1.00  ------ QBF
% 3.39/1.00  
% 3.39/1.00  qbf_q_res:                              0
% 3.39/1.00  qbf_num_tautologies:                    0
% 3.39/1.00  qbf_prep_cycles:                        0
% 3.39/1.00  
% 3.39/1.00  ------ BMC1
% 3.39/1.00  
% 3.39/1.00  bmc1_current_bound:                     -1
% 3.39/1.00  bmc1_last_solved_bound:                 -1
% 3.39/1.00  bmc1_unsat_core_size:                   -1
% 3.39/1.00  bmc1_unsat_core_parents_size:           -1
% 3.39/1.00  bmc1_merge_next_fun:                    0
% 3.39/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation
% 3.39/1.00  
% 3.39/1.00  inst_num_of_clauses:                    496
% 3.39/1.00  inst_num_in_passive:                    20
% 3.39/1.00  inst_num_in_active:                     353
% 3.39/1.00  inst_num_in_unprocessed:                123
% 3.39/1.00  inst_num_of_loops:                      420
% 3.39/1.00  inst_num_of_learning_restarts:          0
% 3.39/1.00  inst_num_moves_active_passive:          60
% 3.39/1.00  inst_lit_activity:                      0
% 3.39/1.00  inst_lit_activity_moves:                0
% 3.39/1.00  inst_num_tautologies:                   0
% 3.39/1.00  inst_num_prop_implied:                  0
% 3.39/1.00  inst_num_existing_simplified:           0
% 3.39/1.00  inst_num_eq_res_simplified:             0
% 3.39/1.00  inst_num_child_elim:                    0
% 3.39/1.00  inst_num_of_dismatching_blockings:      216
% 3.39/1.00  inst_num_of_non_proper_insts:           840
% 3.39/1.00  inst_num_of_duplicates:                 0
% 3.39/1.00  inst_inst_num_from_inst_to_res:         0
% 3.39/1.00  inst_dismatching_checking_time:         0.
% 3.39/1.00  
% 3.39/1.00  ------ Resolution
% 3.39/1.00  
% 3.39/1.00  res_num_of_clauses:                     0
% 3.39/1.00  res_num_in_passive:                     0
% 3.39/1.00  res_num_in_active:                      0
% 3.39/1.00  res_num_of_loops:                       141
% 3.39/1.00  res_forward_subset_subsumed:            139
% 3.39/1.00  res_backward_subset_subsumed:           2
% 3.39/1.00  res_forward_subsumed:                   0
% 3.39/1.00  res_backward_subsumed:                  0
% 3.39/1.00  res_forward_subsumption_resolution:     0
% 3.39/1.00  res_backward_subsumption_resolution:    0
% 3.39/1.00  res_clause_to_clause_subsumption:       262
% 3.39/1.00  res_orphan_elimination:                 0
% 3.39/1.00  res_tautology_del:                      167
% 3.39/1.00  res_num_eq_res_simplified:              0
% 3.39/1.00  res_num_sel_changes:                    0
% 3.39/1.00  res_moves_from_active_to_pass:          0
% 3.39/1.00  
% 3.39/1.00  ------ Superposition
% 3.39/1.00  
% 3.39/1.00  sup_time_total:                         0.
% 3.39/1.00  sup_time_generating:                    0.
% 3.39/1.00  sup_time_sim_full:                      0.
% 3.39/1.00  sup_time_sim_immed:                     0.
% 3.39/1.00  
% 3.39/1.00  sup_num_of_clauses:                     142
% 3.39/1.00  sup_num_in_active:                      79
% 3.39/1.00  sup_num_in_passive:                     63
% 3.39/1.00  sup_num_of_loops:                       83
% 3.39/1.00  sup_fw_superposition:                   57
% 3.39/1.00  sup_bw_superposition:                   69
% 3.39/1.00  sup_immediate_simplified:               22
% 3.39/1.00  sup_given_eliminated:                   0
% 3.39/1.00  comparisons_done:                       0
% 3.39/1.00  comparisons_avoided:                    3
% 3.39/1.00  
% 3.39/1.00  ------ Simplifications
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  sim_fw_subset_subsumed:                 0
% 3.39/1.00  sim_bw_subset_subsumed:                 1
% 3.39/1.00  sim_fw_subsumed:                        0
% 3.39/1.00  sim_bw_subsumed:                        1
% 3.39/1.00  sim_fw_subsumption_res:                 0
% 3.39/1.00  sim_bw_subsumption_res:                 0
% 3.39/1.00  sim_tautology_del:                      0
% 3.39/1.00  sim_eq_tautology_del:                   3
% 3.39/1.00  sim_eq_res_simp:                        0
% 3.39/1.00  sim_fw_demodulated:                     5
% 3.39/1.00  sim_bw_demodulated:                     3
% 3.39/1.00  sim_light_normalised:                   18
% 3.39/1.00  sim_joinable_taut:                      0
% 3.39/1.00  sim_joinable_simp:                      0
% 3.39/1.00  sim_ac_normalised:                      0
% 3.39/1.00  sim_smt_subsumption:                    0
% 3.39/1.00  
%------------------------------------------------------------------------------
