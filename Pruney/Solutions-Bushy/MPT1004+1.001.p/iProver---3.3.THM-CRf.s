%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:37 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  208 (3817 expanded)
%              Number of clauses        :  151 (1453 expanded)
%              Number of leaves         :   21 ( 878 expanded)
%              Depth                    :   29
%              Number of atoms          :  622 (22451 expanded)
%              Number of equality atoms :  331 (6386 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    inference(ennf_transformation,[],[f2])).

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

fof(f30,plain,(
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

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ! [X5] :
          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X5,X1,X2)
            & v1_funct_1(X5) )
         => ( ( k1_xboole_0 = X2
             => k1_xboole_0 = X1 )
           => r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X5,X1,X2)
              & v1_funct_1(X5) )
           => ( ( k1_xboole_0 = X2
               => k1_xboole_0 = X1 )
             => r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X5,X1,X2)
          & v1_funct_1(X5) )
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X5,X1,X2)
          & v1_funct_1(X5) )
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X5,X1,X2)
          & v1_funct_1(X5) )
     => ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,sK5),k7_relset_1(X1,X2,sK5,X3)))
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X2 )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X5,X1,X2)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,X5),k7_relset_1(sK1,sK2,X5,sK3)))
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X5,sK1,sK2)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK4,sK0,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK5,sK1,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK4,sK0,sK1)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f29,f33,f32])).

fof(f57,plain,(
    v1_funct_2(sK5,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f59,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f40])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK5) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_413,plain,
    ( k1_relset_1(sK1,sK2,sK5) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_20])).

cnf(c_651,plain,
    ( k1_relset_1(sK1,sK2,sK5) = sK1
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_413])).

cnf(c_659,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1226,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k1_relset_1(X1_52,X2_52,X0_52) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1218,plain,
    ( k1_relset_1(X0_52,X1_52,X2_52) = k1_relat_1(X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_1587,plain,
    ( k1_relset_1(sK1,sK2,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1226,c_1218])).

cnf(c_1749,plain,
    ( k1_relat_1(sK5) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_651,c_1587])).

cnf(c_15,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1)))
    | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_664,plain,
    ( r1_tarski(k10_relat_1(X0_52,X0_54),k10_relat_1(k5_relat_1(X0_52,X1_52),k9_relat_1(X1_52,X0_54)))
    | ~ r1_tarski(k2_relat_1(X0_52),k1_relat_1(X1_52))
    | ~ v1_relat_1(X0_52)
    | ~ v1_relat_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1222,plain,
    ( r1_tarski(k10_relat_1(X0_52,X0_54),k10_relat_1(k5_relat_1(X0_52,X1_52),k9_relat_1(X1_52,X0_54))) = iProver_top
    | r1_tarski(k2_relat_1(X0_52),k1_relat_1(X1_52)) != iProver_top
    | v1_relat_1(X0_52) != iProver_top
    | v1_relat_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_657,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1228,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X5_52)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X3_52)
    | k1_partfun1(X4_52,X5_52,X1_52,X2_52,X3_52,X0_52) = k5_relat_1(X3_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1217,plain,
    ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X4_52,X5_52) = k5_relat_1(X4_52,X5_52)
    | m1_subset_1(X5_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | m1_subset_1(X4_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X5_52) != iProver_top
    | v1_funct_1(X4_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_2327,plain,
    ( k1_partfun1(X0_52,X1_52,sK1,sK2,X2_52,sK5) = k5_relat_1(X2_52,sK5)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1217])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2466,plain,
    ( v1_funct_1(X2_52) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | k1_partfun1(X0_52,X1_52,sK1,sK2,X2_52,sK5) = k5_relat_1(X2_52,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2327,c_29])).

cnf(c_2467,plain,
    ( k1_partfun1(X0_52,X1_52,sK1,sK2,X2_52,sK5) = k5_relat_1(X2_52,sK5)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2466])).

cnf(c_2473,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_2467])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2529,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2473,c_26])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X5_52)))
    | m1_subset_1(k1_partfun1(X4_52,X5_52,X1_52,X2_52,X3_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(X4_52,X2_52)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X3_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1214,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X5_52))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_52,X5_52,X1_52,X2_52,X3_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(X4_52,X2_52))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X3_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_662,plain,
    ( r1_tarski(X0_52,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1224,plain,
    ( r1_tarski(X0_52,X1_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_1856,plain,
    ( r1_tarski(k1_partfun1(X0_52,X1_52,X2_52,X3_52,X4_52,X5_52),k2_zfmisc_1(X0_52,X3_52)) = iProver_top
    | m1_subset_1(X5_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | m1_subset_1(X4_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X5_52) != iProver_top
    | v1_funct_1(X4_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1224])).

cnf(c_2715,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK0,sK2)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2529,c_1856])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3763,plain,
    ( r1_tarski(k5_relat_1(sK4,sK5),k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2715,c_26,c_28,c_29,c_31])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_663,plain,
    ( ~ r1_tarski(X0_52,X1_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1223,plain,
    ( r1_tarski(X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k8_relset_1(X1_52,X2_52,X0_52,X0_54) = k10_relat_1(X0_52,X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1221,plain,
    ( k8_relset_1(X0_52,X1_52,X2_52,X0_54) = k10_relat_1(X2_52,X0_54)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_2001,plain,
    ( k8_relset_1(X0_52,X1_52,X2_52,X0_54) = k10_relat_1(X2_52,X0_54)
    | r1_tarski(X2_52,k2_zfmisc_1(X0_52,X1_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1221])).

cnf(c_3989,plain,
    ( k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),X0_54) = k10_relat_1(k5_relat_1(sK4,sK5),X0_54) ),
    inference(superposition,[status(thm)],[c_3763,c_2001])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k7_relset_1(X1_52,X2_52,X0_52,X0_54) = k9_relat_1(X0_52,X0_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1220,plain,
    ( k7_relset_1(X0_52,X1_52,X2_52,X0_54) = k9_relat_1(X2_52,X0_54)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_1941,plain,
    ( k7_relset_1(sK1,sK2,sK5,X0_54) = k9_relat_1(sK5,X0_54) ),
    inference(superposition,[status(thm)],[c_1226,c_1220])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_661,negated_conjecture,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1225,plain,
    ( r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_2076,plain,
    ( r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1941,c_1225])).

cnf(c_2000,plain,
    ( k8_relset_1(sK0,sK1,sK4,X0_54) = k10_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_1228,c_1221])).

cnf(c_2077,plain,
    ( r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2076,c_2000])).

cnf(c_3085,plain,
    ( r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2077,c_2529])).

cnf(c_13762,plain,
    ( r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3989,c_3085])).

cnf(c_14017,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_13762])).

cnf(c_32,plain,
    ( r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_689,plain,
    ( ~ r1_tarski(X0_52,X1_52)
    | r1_tarski(X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_1267,plain,
    ( ~ r1_tarski(X0_52,X1_52)
    | r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != X1_52
    | k8_relset_1(sK0,sK1,sK4,sK3) != X0_52 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1282,plain,
    ( r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | ~ r1_tarski(k10_relat_1(sK4,sK3),X0_52)
    | k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != X0_52
    | k8_relset_1(sK0,sK1,sK4,sK3) != k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1302,plain,
    ( r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | ~ r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))
    | k8_relset_1(sK0,sK1,sK4,sK3) != k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1303,plain,
    ( k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))
    | k8_relset_1(sK0,sK1,sK4,sK3) != k10_relat_1(sK4,sK3)
    | r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) = iProver_top
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k8_relset_1(sK0,sK1,sK4,sK3) = k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) = k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1213,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_1503,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1213])).

cnf(c_1504,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1213])).

cnf(c_1572,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_675,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1731,plain,
    ( k10_relat_1(sK4,sK3) = k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1946,plain,
    ( k7_relset_1(sK1,sK2,sK5,sK3) = k9_relat_1(sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_2250,plain,
    ( r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,X0_52),k9_relat_1(X0_52,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(X0_52))
    | ~ v1_relat_1(X0_52)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_4241,plain,
    ( r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2250])).

cnf(c_4242,plain,
    ( r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4241])).

cnf(c_688,plain,
    ( X0_54 != X1_54
    | X0_52 != X1_52
    | k10_relat_1(X0_52,X0_54) = k10_relat_1(X1_52,X1_54) ),
    theory(equality)).

cnf(c_3109,plain,
    ( k7_relset_1(sK1,sK2,sK5,sK3) != X0_54
    | k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) != X0_52
    | k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) = k10_relat_1(X0_52,X0_54) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_4159,plain,
    ( k7_relset_1(sK1,sK2,sK5,sK3) != k9_relat_1(sK5,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) != X0_52
    | k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) = k10_relat_1(X0_52,k9_relat_1(sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_3109])).

cnf(c_7170,plain,
    ( k7_relset_1(sK1,sK2,sK5,sK3) != k9_relat_1(sK5,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) != k5_relat_1(sK4,sK5)
    | k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) = k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_1534,plain,
    ( ~ r1_tarski(X0_52,X1_52)
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != X1_52
    | k10_relat_1(sK4,sK3) != X0_52 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1824,plain,
    ( ~ r1_tarski(k10_relat_1(X0_52,X0_54),X1_52)
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != X1_52
    | k10_relat_1(sK4,sK3) != k10_relat_1(X0_52,X0_54) ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_2276,plain,
    ( ~ r1_tarski(k10_relat_1(X0_52,X0_54),k10_relat_1(X1_52,X1_54))
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != k10_relat_1(X1_52,X1_54)
    | k10_relat_1(sK4,sK3) != k10_relat_1(X0_52,X0_54) ),
    inference(instantiation,[status(thm)],[c_1824])).

cnf(c_3121,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,X0_54),k10_relat_1(X0_52,X1_54))
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != k10_relat_1(X0_52,X1_54)
    | k10_relat_1(sK4,sK3) != k10_relat_1(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_2276])).

cnf(c_13220,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,X0_54),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))
    | k10_relat_1(sK4,sK3) != k10_relat_1(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_3121])).

cnf(c_13221,plain,
    ( k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))
    | k10_relat_1(sK4,sK3) != k10_relat_1(sK4,X0_54)
    | r1_tarski(k10_relat_1(sK4,X0_54),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) != iProver_top
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13220])).

cnf(c_13223,plain,
    ( k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)) != k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))
    | k10_relat_1(sK4,sK3) != k10_relat_1(sK4,sK3)
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) = iProver_top
    | r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13221])).

cnf(c_14359,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14017,c_25,c_26,c_23,c_22,c_20,c_32,c_1303,c_1365,c_1432,c_1503,c_1504,c_1572,c_1731,c_1946,c_2473,c_4242,c_7170,c_13223])).

cnf(c_14363,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_14359])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k2_relset_1(X1_52,X2_52,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1219,plain,
    ( k2_relset_1(X0_52,X1_52,X2_52) = k2_relat_1(X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_1645,plain,
    ( k2_relset_1(sK0,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1228,c_1219])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | m1_subset_1(k2_relset_1(X1_52,X2_52,X0_52),k1_zfmisc_1(X2_52)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1216,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_52,X2_52,X0_52),k1_zfmisc_1(X2_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_1921,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1645,c_1216])).

cnf(c_3016,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1921,c_28])).

cnf(c_3020,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3016,c_1224])).

cnf(c_14556,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14363,c_3020])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK5 != X0
    | sK2 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_385,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK5) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_653,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK5) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_385])).

cnf(c_1232,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK5) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_14628,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14556,c_1232])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_660,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_14636,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14556,c_660])).

cnf(c_14637,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_14636])).

cnf(c_14632,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_14556,c_1587])).

cnf(c_14640,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_14632,c_14637])).

cnf(c_14644,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14628,c_14637,c_14640])).

cnf(c_14645,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14644])).

cnf(c_701,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1761,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_678,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_2493,plain,
    ( sK2 != X0_52
    | k1_xboole_0 != X0_52
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_2494,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2493])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK5 != X0
    | sK2 != k1_xboole_0
    | sK1 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_349,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_655,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_349])).

cnf(c_1230,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK1
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_2651,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1230,c_701,c_660,c_2494])).

cnf(c_2652,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(renaming,[status(thm)],[c_2651])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0_52,X0_53)
    | m1_subset_1(X1_52,X1_53)
    | X1_53 != X0_53
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_3350,plain,
    ( ~ m1_subset_1(X0_52,X0_53)
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
    | k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)) != X0_53
    | X1_52 != X0_52 ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_7332,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | X0_52 != sK5 ),
    inference(instantiation,[status(thm)],[c_3350])).

cnf(c_7500,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7332])).

cnf(c_7501,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7500])).

cnf(c_7503,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7501])).

cnf(c_680,plain,
    ( X0_52 != X1_52
    | X2_52 != X3_52
    | k2_zfmisc_1(X0_52,X2_52) = k2_zfmisc_1(X1_52,X3_52) ),
    theory(equality)).

cnf(c_8449,plain,
    ( X0_52 != sK2
    | X1_52 != sK1
    | k2_zfmisc_1(X1_52,X0_52) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_8450,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_8449])).

cnf(c_681,plain,
    ( k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52)
    | X0_52 != X1_52 ),
    theory(equality)).

cnf(c_7567,plain,
    ( k1_zfmisc_1(X0_52) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | X0_52 != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_13654,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k2_zfmisc_1(X0_52,X1_52) != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_7567])).

cnf(c_13655,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_13654])).

cnf(c_39938,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14645,c_31,c_701,c_1761,c_2494,c_2652,c_3020,c_7503,c_8450,c_13655,c_14363])).

cnf(c_39941,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_39938,c_14359])).

cnf(c_14840,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14637,c_3020])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39941,c_14840])).


%------------------------------------------------------------------------------
