%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:46 EST 2020

% Result     : Theorem 31.89s
% Output     : CNFRefutation 31.89s
% Verified   : 
% Statistics : Number of formulae       :  481 (14713 expanded)
%              Number of clauses        :  395 (6268 expanded)
%              Number of leaves         :   26 (2698 expanded)
%              Depth                    :   39
%              Number of atoms          : 1412 (64649 expanded)
%              Number of equality atoms :  900 (22956 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f47])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f46,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f82,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f81,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f88,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1425,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1411,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1413,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5916,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1413])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1707,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3588,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_6265,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5916,c_33,c_31,c_3588])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1415,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6402,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6265,c_1415])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6522,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6402,c_34,c_36])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_11])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_404,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_15])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_404])).

cnf(c_1408,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_6534,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6522,c_1408])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1412,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_526,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_31])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1417,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3066,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1411,c_1417])).

cnf(c_3461,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_526,c_3066])).

cnf(c_1418,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2442,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1418])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1419,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4228,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_1419])).

cnf(c_10889,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2442,c_4228])).

cnf(c_11571,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK0)) = k1_relat_1(sK3)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3461,c_10889])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1421,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11573,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10889,c_1419])).

cnf(c_6533,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6522,c_1418])).

cnf(c_11890,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11573,c_6533])).

cnf(c_11901,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_11890])).

cnf(c_11950,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(k7_relat_1(X0,sK0)))) = k1_relat_1(k7_relat_1(X0,sK0))
    | sK1 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_11901])).

cnf(c_14084,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(k7_relat_1(sK3,sK0)))) = k1_relat_1(k7_relat_1(sK3,sK0))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2442,c_11950])).

cnf(c_14144,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),k1_relat_1(k7_relat_1(sK3,sK0)))) = k1_relat_1(k7_relat_1(sK3,sK0))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3461,c_14084])).

cnf(c_14250,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),k1_relat_1(sK3))) = k1_relat_1(k7_relat_1(sK3,sK0))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11571,c_14144])).

cnf(c_15557,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14250,c_1421])).

cnf(c_76,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_98,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_100,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_106,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_534,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_1646,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1648,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1646])).

cnf(c_1651,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_819,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1678,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1679,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_13,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1722,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1729,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_818,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1835,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_820,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1878,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1880,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1878])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1907,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1925,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_1978,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1746,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1995,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_1996,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2021,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2023,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2021])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_456,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_1406,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1510,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1406,c_4])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1677,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1924,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1677])).

cnf(c_2072,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_2073,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2072])).

cnf(c_2136,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1510,c_29,c_100,c_101,c_1924,c_1925,c_2073])).

cnf(c_2137,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2136])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1691,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2029,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_2148,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_2224,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_2225,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_2723,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_824,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_2728,plain,
    ( k1_relat_1(sK3) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_2733,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2728])).

cnf(c_1420,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1424,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2259,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1424])).

cnf(c_75,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_77,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_105,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_107,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_1647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_1649,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_1879,plain,
    ( X0 != X1
    | k2_zfmisc_1(X2,X3) != X4
    | r1_tarski(X1,X4) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1878])).

cnf(c_1881,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_2264,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2259,c_77,c_100,c_101,c_107,c_1649,c_1881])).

cnf(c_2900,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_1421])).

cnf(c_2922,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2900])).

cnf(c_2924,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2922])).

cnf(c_823,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1696,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_1904,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1696])).

cnf(c_3260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(c_3262,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3260])).

cnf(c_3590,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3588])).

cnf(c_1951,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3)
    | X2 != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_2714,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(X1,sK3)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_5166,plain,
    ( r1_tarski(X0,sK3)
    | ~ r1_tarski(k7_relat_1(sK3,X1),sK3)
    | X0 != k7_relat_1(sK3,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2714])).

cnf(c_5168,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3)
    | r1_tarski(k1_xboole_0,sK3)
    | sK3 != sK3
    | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5166])).

cnf(c_2726,plain,
    ( X0 != X1
    | k1_relat_1(sK3) != X1
    | k1_relat_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_5223,plain,
    ( X0 != k1_relat_1(sK3)
    | k1_relat_1(sK3) = X0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2726])).

cnf(c_5224,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5223])).

cnf(c_2292,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_6025,plain,
    ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
    | X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_2292])).

cnf(c_6026,plain,
    ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6025])).

cnf(c_3491,plain,
    ( k2_zfmisc_1(sK2,sK1) != X0
    | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_6505,plain,
    ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3491])).

cnf(c_6507,plain,
    ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6505])).

cnf(c_821,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_6506,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(X0,X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_6508,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6506])).

cnf(c_3504,plain,
    ( k2_zfmisc_1(sK0,sK1) != X0
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_6515,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3504])).

cnf(c_6517,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6515])).

cnf(c_6516,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_6518,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6516])).

cnf(c_6669,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6670,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,X0)
    | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6669])).

cnf(c_6672,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6670])).

cnf(c_1816,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1408])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1416,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4714,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1416])).

cnf(c_7050,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_4714])).

cnf(c_1652,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_7477,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7050,c_36,c_1652])).

cnf(c_7478,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7477])).

cnf(c_7479,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7478])).

cnf(c_19,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_429,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_430,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1407,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_1561,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1407,c_4])).

cnf(c_97,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_99,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_2075,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1561,c_99,c_107])).

cnf(c_2076,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2075])).

cnf(c_6270,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6265,c_2076])).

cnf(c_1414,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2794,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1414])).

cnf(c_2030,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2029])).

cnf(c_3464,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2794,c_34,c_36,c_2030])).

cnf(c_6273,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6265,c_3464])).

cnf(c_6297,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6270,c_6273])).

cnf(c_1676,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1918,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_1919,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_2206,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1808,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_2211,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_2891,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_7853,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6297,c_30,c_29,c_100,c_101,c_1918,c_1919,c_2073,c_2206,c_2891])).

cnf(c_7854,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7853])).

cnf(c_2903,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1424])).

cnf(c_3737,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2442,c_2903])).

cnf(c_4713,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1416])).

cnf(c_6181,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3737,c_4713])).

cnf(c_1723,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1724,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1723])).

cnf(c_1726,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_1728,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1722])).

cnf(c_1730,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_239,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_240,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_300,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_240])).

cnf(c_1737,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_1956,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
    | v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_1957,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1956])).

cnf(c_1959,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_7051,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6534,c_4714])).

cnf(c_7105,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7051])).

cnf(c_8098,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6181,c_36,c_1652,c_1726,c_1730,c_1959,c_7105])).

cnf(c_1422,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8103,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8098,c_1422])).

cnf(c_8667,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1926,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_8723,plain,
    ( k1_relat_1(sK3) != X0
    | sK0 != X0
    | sK0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_8726,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK0 = k1_relat_1(sK3)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8723])).

cnf(c_2703,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_8722,plain,
    ( k1_relat_1(sK3) != sK0
    | sK0 = k1_relat_1(sK3)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2703])).

cnf(c_3266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(c_5271,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3266])).

cnf(c_8834,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5271])).

cnf(c_2016,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),X2)
    | X2 != X1
    | k1_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_4302,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | r1_tarski(k1_relat_1(sK3),X1)
    | X1 != X0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_9887,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | X0 != sK0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4302])).

cnf(c_9904,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_9887])).

cnf(c_822,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4159,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_10699,plain,
    ( k2_zfmisc_1(sK2,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_10700,plain,
    ( k2_zfmisc_1(sK2,sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10699])).

cnf(c_11537,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_12526,plain,
    ( k2_zfmisc_1(sK0,sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_12527,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12526])).

cnf(c_14458,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_14459,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14458])).

cnf(c_9557,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | X0 != k1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4302])).

cnf(c_18924,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | r1_tarski(k1_relat_1(sK3),sK0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | sK0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9557])).

cnf(c_826,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_2295,plain,
    ( X0 != X1
    | X2 != sK3
    | X3 != sK1
    | X4 != sK0
    | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_4086,plain,
    ( X0 != X1
    | X2 != sK1
    | X3 != sK0
    | k2_partfun1(X3,X2,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2295])).

cnf(c_10832,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_4086])).

cnf(c_21314,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,X0)
    | sK2 != X0
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_10832])).

cnf(c_21317,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_21314])).

cnf(c_9062,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8103,c_1424])).

cnf(c_1426,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4106,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k7_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1426])).

cnf(c_22237,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9062,c_4106])).

cnf(c_22242,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22237,c_9062])).

cnf(c_22275,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22242])).

cnf(c_26667,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = sK0
    | sK0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5223])).

cnf(c_1759,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_28716,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_28723,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28716])).

cnf(c_3577,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_30917,plain,
    ( X0 != k2_partfun1(sK0,sK1,sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_3577])).

cnf(c_30918,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_30917])).

cnf(c_35479,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(sK3),X2)
    | X2 != X1
    | k1_relat_1(sK3) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_35481,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_35479])).

cnf(c_40657,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15557,c_33,c_31,c_76,c_98,c_100,c_101,c_106,c_534,c_1648,c_1651,c_1679,c_1729,c_1835,c_1880,c_1907,c_1925,c_1978,c_1995,c_1996,c_2023,c_2137,c_2148,c_2225,c_2723,c_2733,c_2924,c_3262,c_3461,c_3590,c_5168,c_5224,c_6026,c_6507,c_6508,c_6517,c_6518,c_6672,c_7479,c_7854,c_8103,c_8667,c_8726,c_8722,c_8834,c_9904,c_10700,c_11537,c_12527,c_14459,c_18924,c_21317,c_22275,c_26667,c_28723,c_30918,c_35481])).

cnf(c_4233,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_1419])).

cnf(c_4444,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4233,c_36,c_1652])).

cnf(c_4445,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4444])).

cnf(c_4451,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK0)) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1425,c_4445])).

cnf(c_14251,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) = k1_relat_1(k7_relat_1(sK3,sK0))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4451,c_14144])).

cnf(c_14280,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),sK0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14251,c_1421])).

cnf(c_37529,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),sK0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14280,c_33,c_31,c_76,c_98,c_100,c_101,c_106,c_534,c_1648,c_1651,c_1679,c_1729,c_1835,c_1880,c_1907,c_1925,c_1978,c_1995,c_1996,c_2023,c_2137,c_2148,c_2225,c_2723,c_2733,c_2924,c_3262,c_3461,c_3590,c_5168,c_5224,c_6026,c_6507,c_6508,c_6517,c_6518,c_6672,c_7479,c_7854,c_8103,c_8667,c_8726,c_8722,c_8834,c_9904,c_10700,c_11537,c_12527,c_14459,c_18924,c_21317,c_22275,c_26667,c_28723,c_30918,c_35481])).

cnf(c_37535,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37529,c_6533])).

cnf(c_37539,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK0)) = sK0
    | r1_tarski(sK0,k1_relat_1(k7_relat_1(sK3,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37535,c_1426])).

cnf(c_1981,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1978])).

cnf(c_1983,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(sK3))
    | X2 != X0
    | k1_relat_1(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_2722,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | r1_tarski(X1,k1_relat_1(sK3))
    | X1 != X0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_5200,plain,
    ( r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | X0 != k1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2722])).

cnf(c_8721,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | r1_tarski(sK0,k1_relat_1(sK3))
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | sK0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5200])).

cnf(c_8724,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | sK0 != k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8721])).

cnf(c_1736,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_17243,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_17244,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK0)) = sK0
    | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17243])).

cnf(c_38370,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_37539,c_31,c_36,c_76,c_100,c_101,c_106,c_1648,c_1651,c_1652,c_1729,c_1880,c_1907,c_1925,c_1981,c_1995,c_1996,c_2023,c_2137,c_2723,c_2733,c_2924,c_3461,c_5168,c_5224,c_6517,c_6518,c_6672,c_8103,c_8667,c_8724,c_8726,c_8722,c_8834,c_11537,c_12527,c_14459,c_17244,c_26667,c_35481])).

cnf(c_40661,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_40657,c_38370])).

cnf(c_40664,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_40661,c_6533])).

cnf(c_40667,plain,
    ( k1_relat_1(sK3) = sK0
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_40664,c_1426])).

cnf(c_41530,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_40667,c_31,c_76,c_100,c_101,c_106,c_1648,c_1651,c_1729,c_1880,c_1907,c_1995,c_1996,c_2023,c_2137,c_2723,c_2733,c_2924,c_3461,c_5168,c_5224,c_6517,c_6518,c_6672,c_8103,c_8667,c_8726,c_8834,c_11537,c_12527,c_14459,c_26667,c_35481])).

cnf(c_41749,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_41530,c_1419])).

cnf(c_41765,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41749,c_33,c_31,c_36,c_76,c_98,c_100,c_101,c_106,c_534,c_1648,c_1651,c_1652,c_1679,c_1729,c_1835,c_1880,c_1907,c_1925,c_1978,c_1995,c_1996,c_2023,c_2137,c_2148,c_2225,c_2723,c_2733,c_2924,c_3262,c_3461,c_3590,c_4233,c_5168,c_5224,c_6026,c_6507,c_6508,c_6517,c_6518,c_6672,c_7479,c_7854,c_8103,c_8667,c_8726,c_8722,c_8834,c_9904,c_10700,c_11537,c_12527,c_14459,c_18924,c_21317,c_22275,c_26667,c_28723,c_30918,c_35481])).

cnf(c_41766,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_41765])).

cnf(c_41775,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1412,c_41766])).

cnf(c_4716,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_1417])).

cnf(c_133452,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41775,c_4716])).

cnf(c_133702,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = sK2
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_133452,c_41775])).

cnf(c_12652,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_12653,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12652])).

cnf(c_14612,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_14613,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14612])).

cnf(c_134854,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_133702,c_36,c_1652,c_12653,c_14613])).

cnf(c_134855,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = sK2
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_134854])).

cnf(c_134867,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6534,c_134855])).

cnf(c_135318,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1425,c_134867])).

cnf(c_73712,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(sK2,sK1))
    | X2 != X0
    | k2_zfmisc_1(sK2,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_77939,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
    | r1_tarski(X1,k2_zfmisc_1(sK2,sK1))
    | X1 != X0
    | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_73712])).

cnf(c_92067,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | X0 != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_77939])).

cnf(c_115264,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | k7_relat_1(sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_92067])).

cnf(c_72397,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_73239,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_72397])).

cnf(c_74978,plain,
    ( ~ r1_tarski(k1_relat_1(X0),sK2)
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_73239])).

cnf(c_81217,plain,
    ( r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k7_relat_1(sK3,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_74978])).

cnf(c_74979,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_78445,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_74979])).

cnf(c_11948,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0)) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1425,c_11901])).

cnf(c_12614,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3461,c_11948])).

cnf(c_4715,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_1422])).

cnf(c_24088,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_4715])).

cnf(c_1819,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1408])).

cnf(c_7049,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_4714])).

cnf(c_24087,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_4715])).

cnf(c_24128,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_24087])).

cnf(c_24581,plain,
    ( r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24088,c_1819,c_7049,c_24128])).

cnf(c_24582,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_24581])).

cnf(c_24607,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,sK0),sK0),k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12614,c_24582])).

cnf(c_2221,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2222,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2221])).

cnf(c_1863,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3560,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_3562,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3560])).

cnf(c_1910,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_2682,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_4816,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2682])).

cnf(c_4822,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4816])).

cnf(c_3269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(X1)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(c_3599,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3269])).

cnf(c_7663,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3599])).

cnf(c_7665,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_7663])).

cnf(c_11543,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_11544,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_11543])).

cnf(c_28892,plain,
    ( X0 != sK1
    | X1 != sK0
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_28893,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_28892])).

cnf(c_31408,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK3,sK0),sK0),k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24607,c_33,c_31,c_30,c_98,c_100,c_101,c_106,c_534,c_1651,c_1679,c_1835,c_1918,c_1919,c_1924,c_1925,c_1995,c_1996,c_2073,c_2148,c_2206,c_2222,c_2891,c_3262,c_3562,c_3590,c_4822,c_6026,c_6507,c_6508,c_6672,c_7665,c_8103,c_10700,c_11544,c_14459,c_21317,c_22275,c_28723,c_28893,c_30918])).

cnf(c_31420,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK0),sK0) = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31408,c_1424])).

cnf(c_2022,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_2024,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_3572,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_5167,plain,
    ( X0 != k7_relat_1(sK3,X1)
    | sK3 != sK3
    | r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5166])).

cnf(c_5169,plain,
    ( sK3 != sK3
    | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5167])).

cnf(c_6017,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3588])).

cnf(c_1702,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2036,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_6787,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2036])).

cnf(c_7483,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_7478])).

cnf(c_7489,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7483,c_1422])).

cnf(c_3571,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_3260])).

cnf(c_11547,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3571])).

cnf(c_4454,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1412,c_4445])).

cnf(c_24592,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4454,c_24582])).

cnf(c_25485,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24592,c_36,c_1652,c_12653,c_14613])).

cnf(c_25486,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_25485])).

cnf(c_25497,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_25486,c_1424])).

cnf(c_25539,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k7_relat_1(sK3,sK2) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25497])).

cnf(c_4024,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,X2) != X1
    | k2_partfun1(sK0,sK1,sK3,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_10587,plain,
    ( X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) = X0
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_4024])).

cnf(c_12014,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k2_partfun1(sK0,sK1,sK3,X0) = sK3
    | sK3 != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_10587])).

cnf(c_28902,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_12014])).

cnf(c_2027,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_31108,plain,
    ( k7_relat_1(sK3,sK2) != X0
    | sK3 != X0
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_31110,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK3 = k7_relat_1(sK3,sK2)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_31108])).

cnf(c_31611,plain,
    ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_11543])).

cnf(c_14551,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,X0)
    | sK2 != sK0
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_6506])).

cnf(c_67436,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,sK1)
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_14551])).

cnf(c_67942,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31420,c_33,c_31,c_36,c_30,c_76,c_98,c_100,c_101,c_106,c_534,c_1648,c_1651,c_1652,c_1679,c_1729,c_1730,c_1835,c_1880,c_1907,c_1918,c_1919,c_1924,c_1925,c_1978,c_1995,c_1996,c_2023,c_2024,c_2137,c_2148,c_2206,c_2222,c_2225,c_2723,c_2733,c_2891,c_2924,c_3262,c_3461,c_3572,c_3590,c_5168,c_5169,c_5224,c_6017,c_6026,c_6507,c_6508,c_6517,c_6518,c_6672,c_6787,c_7479,c_7489,c_7854,c_8103,c_8667,c_8726,c_8722,c_8834,c_9904,c_10700,c_11537,c_11547,c_12527,c_14459,c_18924,c_21317,c_22275,c_25539,c_26667,c_28723,c_28902,c_30918,c_31110,c_31611,c_35481,c_67436])).

cnf(c_6606,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1646])).

cnf(c_43097,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_6606])).

cnf(c_1782,plain,
    ( ~ m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(k2_relat_1(k2_partfun1(X0,X1,sK3,X2)),X1) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_2176,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,X0)),sK1) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_40030,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_2176])).

cnf(c_6679,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_6025])).

cnf(c_18487,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k7_relat_1(sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2)
    | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_6679])).

cnf(c_6680,plain,
    ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_15648,plain,
    ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_6680])).

cnf(c_6503,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_22,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_507,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_508,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1403,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_6272,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6265,c_1403])).

cnf(c_6280,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6272,c_6273])).

cnf(c_6398,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6280])).

cnf(c_4675,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_3525,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_1783,plain,
    ( ~ m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k2_partfun1(X0,X1,sK3,X2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2177,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_3521,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2177])).

cnf(c_2627,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1826,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1827,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1826])).

cnf(c_1829,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_135318,c_115264,c_81217,c_78445,c_67942,c_43097,c_40030,c_18487,c_15648,c_6787,c_6503,c_6398,c_6017,c_4675,c_3525,c_3521,c_2627,c_2137,c_1919,c_1829,c_1651,c_107,c_101,c_100,c_31,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.40/4.55  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.40/4.55  
% 31.40/4.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.40/4.55  
% 31.40/4.55  ------  iProver source info
% 31.40/4.55  
% 31.40/4.55  git: date: 2020-06-30 10:37:57 +0100
% 31.40/4.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.40/4.55  git: non_committed_changes: false
% 31.40/4.55  git: last_make_outside_of_git: false
% 31.40/4.55  
% 31.40/4.55  ------ 
% 31.40/4.55  
% 31.40/4.55  ------ Input Options
% 31.40/4.55  
% 31.40/4.55  --out_options                           all
% 31.40/4.55  --tptp_safe_out                         true
% 31.40/4.55  --problem_path                          ""
% 31.40/4.55  --include_path                          ""
% 31.40/4.55  --clausifier                            res/vclausify_rel
% 31.40/4.55  --clausifier_options                    --mode clausify
% 31.40/4.55  --stdin                                 false
% 31.40/4.55  --stats_out                             all
% 31.40/4.55  
% 31.40/4.55  ------ General Options
% 31.40/4.55  
% 31.40/4.55  --fof                                   false
% 31.40/4.55  --time_out_real                         305.
% 31.40/4.55  --time_out_virtual                      -1.
% 31.40/4.55  --symbol_type_check                     false
% 31.40/4.55  --clausify_out                          false
% 31.40/4.55  --sig_cnt_out                           false
% 31.40/4.55  --trig_cnt_out                          false
% 31.40/4.55  --trig_cnt_out_tolerance                1.
% 31.40/4.55  --trig_cnt_out_sk_spl                   false
% 31.40/4.55  --abstr_cl_out                          false
% 31.40/4.55  
% 31.40/4.55  ------ Global Options
% 31.40/4.55  
% 31.40/4.55  --schedule                              default
% 31.40/4.55  --add_important_lit                     false
% 31.40/4.55  --prop_solver_per_cl                    1000
% 31.40/4.55  --min_unsat_core                        false
% 31.40/4.55  --soft_assumptions                      false
% 31.40/4.55  --soft_lemma_size                       3
% 31.40/4.55  --prop_impl_unit_size                   0
% 31.40/4.55  --prop_impl_unit                        []
% 31.40/4.55  --share_sel_clauses                     true
% 31.40/4.55  --reset_solvers                         false
% 31.40/4.55  --bc_imp_inh                            [conj_cone]
% 31.40/4.55  --conj_cone_tolerance                   3.
% 31.40/4.55  --extra_neg_conj                        none
% 31.40/4.55  --large_theory_mode                     true
% 31.40/4.55  --prolific_symb_bound                   200
% 31.40/4.55  --lt_threshold                          2000
% 31.40/4.55  --clause_weak_htbl                      true
% 31.40/4.55  --gc_record_bc_elim                     false
% 31.40/4.55  
% 31.40/4.55  ------ Preprocessing Options
% 31.40/4.55  
% 31.40/4.55  --preprocessing_flag                    true
% 31.40/4.55  --time_out_prep_mult                    0.1
% 31.40/4.55  --splitting_mode                        input
% 31.40/4.55  --splitting_grd                         true
% 31.40/4.55  --splitting_cvd                         false
% 31.40/4.55  --splitting_cvd_svl                     false
% 31.40/4.55  --splitting_nvd                         32
% 31.40/4.55  --sub_typing                            true
% 31.40/4.55  --prep_gs_sim                           true
% 31.40/4.55  --prep_unflatten                        true
% 31.40/4.55  --prep_res_sim                          true
% 31.40/4.55  --prep_upred                            true
% 31.40/4.55  --prep_sem_filter                       exhaustive
% 31.40/4.55  --prep_sem_filter_out                   false
% 31.40/4.55  --pred_elim                             true
% 31.40/4.55  --res_sim_input                         true
% 31.40/4.55  --eq_ax_congr_red                       true
% 31.40/4.55  --pure_diseq_elim                       true
% 31.40/4.55  --brand_transform                       false
% 31.40/4.55  --non_eq_to_eq                          false
% 31.40/4.55  --prep_def_merge                        true
% 31.40/4.55  --prep_def_merge_prop_impl              false
% 31.40/4.55  --prep_def_merge_mbd                    true
% 31.40/4.55  --prep_def_merge_tr_red                 false
% 31.40/4.55  --prep_def_merge_tr_cl                  false
% 31.40/4.55  --smt_preprocessing                     true
% 31.40/4.55  --smt_ac_axioms                         fast
% 31.40/4.55  --preprocessed_out                      false
% 31.40/4.55  --preprocessed_stats                    false
% 31.40/4.55  
% 31.40/4.55  ------ Abstraction refinement Options
% 31.40/4.55  
% 31.40/4.55  --abstr_ref                             []
% 31.40/4.55  --abstr_ref_prep                        false
% 31.40/4.55  --abstr_ref_until_sat                   false
% 31.40/4.55  --abstr_ref_sig_restrict                funpre
% 31.40/4.55  --abstr_ref_af_restrict_to_split_sk     false
% 31.40/4.55  --abstr_ref_under                       []
% 31.40/4.55  
% 31.40/4.55  ------ SAT Options
% 31.40/4.55  
% 31.40/4.55  --sat_mode                              false
% 31.40/4.55  --sat_fm_restart_options                ""
% 31.40/4.55  --sat_gr_def                            false
% 31.40/4.55  --sat_epr_types                         true
% 31.40/4.55  --sat_non_cyclic_types                  false
% 31.40/4.55  --sat_finite_models                     false
% 31.40/4.55  --sat_fm_lemmas                         false
% 31.40/4.55  --sat_fm_prep                           false
% 31.40/4.55  --sat_fm_uc_incr                        true
% 31.40/4.55  --sat_out_model                         small
% 31.40/4.55  --sat_out_clauses                       false
% 31.40/4.55  
% 31.40/4.55  ------ QBF Options
% 31.40/4.55  
% 31.40/4.55  --qbf_mode                              false
% 31.40/4.55  --qbf_elim_univ                         false
% 31.40/4.55  --qbf_dom_inst                          none
% 31.40/4.55  --qbf_dom_pre_inst                      false
% 31.40/4.55  --qbf_sk_in                             false
% 31.40/4.55  --qbf_pred_elim                         true
% 31.40/4.55  --qbf_split                             512
% 31.40/4.55  
% 31.40/4.55  ------ BMC1 Options
% 31.40/4.55  
% 31.40/4.55  --bmc1_incremental                      false
% 31.40/4.55  --bmc1_axioms                           reachable_all
% 31.40/4.55  --bmc1_min_bound                        0
% 31.40/4.55  --bmc1_max_bound                        -1
% 31.40/4.55  --bmc1_max_bound_default                -1
% 31.40/4.55  --bmc1_symbol_reachability              true
% 31.40/4.55  --bmc1_property_lemmas                  false
% 31.40/4.55  --bmc1_k_induction                      false
% 31.40/4.55  --bmc1_non_equiv_states                 false
% 31.40/4.55  --bmc1_deadlock                         false
% 31.40/4.55  --bmc1_ucm                              false
% 31.40/4.55  --bmc1_add_unsat_core                   none
% 31.40/4.55  --bmc1_unsat_core_children              false
% 31.40/4.55  --bmc1_unsat_core_extrapolate_axioms    false
% 31.40/4.55  --bmc1_out_stat                         full
% 31.40/4.55  --bmc1_ground_init                      false
% 31.40/4.55  --bmc1_pre_inst_next_state              false
% 31.40/4.55  --bmc1_pre_inst_state                   false
% 31.40/4.55  --bmc1_pre_inst_reach_state             false
% 31.40/4.55  --bmc1_out_unsat_core                   false
% 31.40/4.55  --bmc1_aig_witness_out                  false
% 31.40/4.55  --bmc1_verbose                          false
% 31.40/4.55  --bmc1_dump_clauses_tptp                false
% 31.40/4.55  --bmc1_dump_unsat_core_tptp             false
% 31.40/4.55  --bmc1_dump_file                        -
% 31.40/4.55  --bmc1_ucm_expand_uc_limit              128
% 31.40/4.55  --bmc1_ucm_n_expand_iterations          6
% 31.40/4.55  --bmc1_ucm_extend_mode                  1
% 31.40/4.55  --bmc1_ucm_init_mode                    2
% 31.40/4.55  --bmc1_ucm_cone_mode                    none
% 31.40/4.55  --bmc1_ucm_reduced_relation_type        0
% 31.40/4.55  --bmc1_ucm_relax_model                  4
% 31.40/4.55  --bmc1_ucm_full_tr_after_sat            true
% 31.40/4.55  --bmc1_ucm_expand_neg_assumptions       false
% 31.40/4.55  --bmc1_ucm_layered_model                none
% 31.40/4.55  --bmc1_ucm_max_lemma_size               10
% 31.40/4.55  
% 31.40/4.55  ------ AIG Options
% 31.40/4.55  
% 31.40/4.55  --aig_mode                              false
% 31.40/4.55  
% 31.40/4.55  ------ Instantiation Options
% 31.40/4.55  
% 31.40/4.55  --instantiation_flag                    true
% 31.40/4.55  --inst_sos_flag                         false
% 31.40/4.55  --inst_sos_phase                        true
% 31.40/4.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.40/4.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.40/4.55  --inst_lit_sel_side                     num_symb
% 31.40/4.55  --inst_solver_per_active                1400
% 31.40/4.55  --inst_solver_calls_frac                1.
% 31.40/4.55  --inst_passive_queue_type               priority_queues
% 31.40/4.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.40/4.55  --inst_passive_queues_freq              [25;2]
% 31.40/4.55  --inst_dismatching                      true
% 31.40/4.55  --inst_eager_unprocessed_to_passive     true
% 31.40/4.55  --inst_prop_sim_given                   true
% 31.40/4.55  --inst_prop_sim_new                     false
% 31.40/4.55  --inst_subs_new                         false
% 31.40/4.55  --inst_eq_res_simp                      false
% 31.40/4.55  --inst_subs_given                       false
% 31.40/4.55  --inst_orphan_elimination               true
% 31.40/4.55  --inst_learning_loop_flag               true
% 31.40/4.55  --inst_learning_start                   3000
% 31.40/4.55  --inst_learning_factor                  2
% 31.40/4.55  --inst_start_prop_sim_after_learn       3
% 31.40/4.55  --inst_sel_renew                        solver
% 31.40/4.55  --inst_lit_activity_flag                true
% 31.40/4.55  --inst_restr_to_given                   false
% 31.40/4.55  --inst_activity_threshold               500
% 31.40/4.55  --inst_out_proof                        true
% 31.40/4.55  
% 31.40/4.55  ------ Resolution Options
% 31.40/4.55  
% 31.40/4.55  --resolution_flag                       true
% 31.40/4.55  --res_lit_sel                           adaptive
% 31.40/4.55  --res_lit_sel_side                      none
% 31.40/4.55  --res_ordering                          kbo
% 31.40/4.55  --res_to_prop_solver                    active
% 31.40/4.55  --res_prop_simpl_new                    false
% 31.40/4.55  --res_prop_simpl_given                  true
% 31.40/4.55  --res_passive_queue_type                priority_queues
% 31.40/4.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.40/4.55  --res_passive_queues_freq               [15;5]
% 31.40/4.55  --res_forward_subs                      full
% 31.40/4.55  --res_backward_subs                     full
% 31.40/4.55  --res_forward_subs_resolution           true
% 31.40/4.55  --res_backward_subs_resolution          true
% 31.40/4.55  --res_orphan_elimination                true
% 31.40/4.55  --res_time_limit                        2.
% 31.40/4.55  --res_out_proof                         true
% 31.40/4.55  
% 31.40/4.55  ------ Superposition Options
% 31.40/4.55  
% 31.40/4.55  --superposition_flag                    true
% 31.40/4.55  --sup_passive_queue_type                priority_queues
% 31.40/4.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.40/4.55  --sup_passive_queues_freq               [8;1;4]
% 31.40/4.55  --demod_completeness_check              fast
% 31.40/4.55  --demod_use_ground                      true
% 31.40/4.55  --sup_to_prop_solver                    passive
% 31.40/4.55  --sup_prop_simpl_new                    true
% 31.40/4.55  --sup_prop_simpl_given                  true
% 31.40/4.55  --sup_fun_splitting                     false
% 31.40/4.55  --sup_smt_interval                      50000
% 31.40/4.55  
% 31.40/4.55  ------ Superposition Simplification Setup
% 31.40/4.55  
% 31.40/4.55  --sup_indices_passive                   []
% 31.40/4.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.40/4.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.40/4.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.40/4.55  --sup_full_triv                         [TrivRules;PropSubs]
% 31.40/4.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.40/4.55  --sup_full_bw                           [BwDemod]
% 31.40/4.55  --sup_immed_triv                        [TrivRules]
% 31.40/4.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.40/4.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.40/4.55  --sup_immed_bw_main                     []
% 31.40/4.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.40/4.55  --sup_input_triv                        [Unflattening;TrivRules]
% 31.40/4.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.40/4.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.40/4.55  
% 31.40/4.55  ------ Combination Options
% 31.40/4.55  
% 31.40/4.55  --comb_res_mult                         3
% 31.40/4.55  --comb_sup_mult                         2
% 31.40/4.55  --comb_inst_mult                        10
% 31.40/4.55  
% 31.40/4.55  ------ Debug Options
% 31.40/4.55  
% 31.40/4.55  --dbg_backtrace                         false
% 31.40/4.55  --dbg_dump_prop_clauses                 false
% 31.40/4.55  --dbg_dump_prop_clauses_file            -
% 31.40/4.55  --dbg_out_stat                          false
% 31.40/4.55  ------ Parsing...
% 31.40/4.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.40/4.55  
% 31.40/4.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.40/4.55  
% 31.40/4.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.40/4.55  
% 31.40/4.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.40/4.55  ------ Proving...
% 31.40/4.55  ------ Problem Properties 
% 31.40/4.55  
% 31.40/4.55  
% 31.40/4.55  clauses                                 30
% 31.40/4.55  conjectures                             4
% 31.40/4.55  EPR                                     7
% 31.40/4.55  Horn                                    27
% 31.40/4.55  unary                                   6
% 31.40/4.55  binary                                  10
% 31.40/4.55  lits                                    77
% 31.40/4.55  lits eq                                 28
% 31.40/4.55  fd_pure                                 0
% 31.40/4.55  fd_pseudo                               0
% 31.40/4.55  fd_cond                                 2
% 31.40/4.55  fd_pseudo_cond                          1
% 31.40/4.55  AC symbols                              0
% 31.40/4.55  
% 31.40/4.55  ------ Schedule dynamic 5 is on 
% 31.40/4.55  
% 31.40/4.55  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.40/4.55  
% 31.40/4.55  
% 31.40/4.55  ------ 
% 31.40/4.55  Current options:
% 31.40/4.55  ------ 
% 31.40/4.55  
% 31.40/4.55  ------ Input Options
% 31.40/4.55  
% 31.40/4.55  --out_options                           all
% 31.40/4.55  --tptp_safe_out                         true
% 31.40/4.55  --problem_path                          ""
% 31.40/4.55  --include_path                          ""
% 31.40/4.55  --clausifier                            res/vclausify_rel
% 31.40/4.55  --clausifier_options                    --mode clausify
% 31.40/4.55  --stdin                                 false
% 31.40/4.55  --stats_out                             all
% 31.89/4.55  
% 31.89/4.55  ------ General Options
% 31.89/4.55  
% 31.89/4.55  --fof                                   false
% 31.89/4.55  --time_out_real                         305.
% 31.89/4.55  --time_out_virtual                      -1.
% 31.89/4.55  --symbol_type_check                     false
% 31.89/4.55  --clausify_out                          false
% 31.89/4.55  --sig_cnt_out                           false
% 31.89/4.55  --trig_cnt_out                          false
% 31.89/4.55  --trig_cnt_out_tolerance                1.
% 31.89/4.55  --trig_cnt_out_sk_spl                   false
% 31.89/4.55  --abstr_cl_out                          false
% 31.89/4.55  
% 31.89/4.55  ------ Global Options
% 31.89/4.55  
% 31.89/4.55  --schedule                              default
% 31.89/4.55  --add_important_lit                     false
% 31.89/4.55  --prop_solver_per_cl                    1000
% 31.89/4.55  --min_unsat_core                        false
% 31.89/4.55  --soft_assumptions                      false
% 31.89/4.55  --soft_lemma_size                       3
% 31.89/4.55  --prop_impl_unit_size                   0
% 31.89/4.55  --prop_impl_unit                        []
% 31.89/4.55  --share_sel_clauses                     true
% 31.89/4.55  --reset_solvers                         false
% 31.89/4.55  --bc_imp_inh                            [conj_cone]
% 31.89/4.55  --conj_cone_tolerance                   3.
% 31.89/4.55  --extra_neg_conj                        none
% 31.89/4.55  --large_theory_mode                     true
% 31.89/4.55  --prolific_symb_bound                   200
% 31.89/4.55  --lt_threshold                          2000
% 31.89/4.55  --clause_weak_htbl                      true
% 31.89/4.55  --gc_record_bc_elim                     false
% 31.89/4.55  
% 31.89/4.55  ------ Preprocessing Options
% 31.89/4.55  
% 31.89/4.55  --preprocessing_flag                    true
% 31.89/4.55  --time_out_prep_mult                    0.1
% 31.89/4.55  --splitting_mode                        input
% 31.89/4.55  --splitting_grd                         true
% 31.89/4.55  --splitting_cvd                         false
% 31.89/4.55  --splitting_cvd_svl                     false
% 31.89/4.55  --splitting_nvd                         32
% 31.89/4.55  --sub_typing                            true
% 31.89/4.55  --prep_gs_sim                           true
% 31.89/4.55  --prep_unflatten                        true
% 31.89/4.55  --prep_res_sim                          true
% 31.89/4.55  --prep_upred                            true
% 31.89/4.55  --prep_sem_filter                       exhaustive
% 31.89/4.55  --prep_sem_filter_out                   false
% 31.89/4.55  --pred_elim                             true
% 31.89/4.55  --res_sim_input                         true
% 31.89/4.55  --eq_ax_congr_red                       true
% 31.89/4.55  --pure_diseq_elim                       true
% 31.89/4.55  --brand_transform                       false
% 31.89/4.55  --non_eq_to_eq                          false
% 31.89/4.55  --prep_def_merge                        true
% 31.89/4.55  --prep_def_merge_prop_impl              false
% 31.89/4.55  --prep_def_merge_mbd                    true
% 31.89/4.55  --prep_def_merge_tr_red                 false
% 31.89/4.55  --prep_def_merge_tr_cl                  false
% 31.89/4.55  --smt_preprocessing                     true
% 31.89/4.55  --smt_ac_axioms                         fast
% 31.89/4.55  --preprocessed_out                      false
% 31.89/4.55  --preprocessed_stats                    false
% 31.89/4.55  
% 31.89/4.55  ------ Abstraction refinement Options
% 31.89/4.55  
% 31.89/4.55  --abstr_ref                             []
% 31.89/4.55  --abstr_ref_prep                        false
% 31.89/4.55  --abstr_ref_until_sat                   false
% 31.89/4.55  --abstr_ref_sig_restrict                funpre
% 31.89/4.55  --abstr_ref_af_restrict_to_split_sk     false
% 31.89/4.55  --abstr_ref_under                       []
% 31.89/4.55  
% 31.89/4.55  ------ SAT Options
% 31.89/4.55  
% 31.89/4.55  --sat_mode                              false
% 31.89/4.55  --sat_fm_restart_options                ""
% 31.89/4.55  --sat_gr_def                            false
% 31.89/4.55  --sat_epr_types                         true
% 31.89/4.55  --sat_non_cyclic_types                  false
% 31.89/4.55  --sat_finite_models                     false
% 31.89/4.55  --sat_fm_lemmas                         false
% 31.89/4.55  --sat_fm_prep                           false
% 31.89/4.55  --sat_fm_uc_incr                        true
% 31.89/4.55  --sat_out_model                         small
% 31.89/4.55  --sat_out_clauses                       false
% 31.89/4.55  
% 31.89/4.55  ------ QBF Options
% 31.89/4.55  
% 31.89/4.55  --qbf_mode                              false
% 31.89/4.55  --qbf_elim_univ                         false
% 31.89/4.55  --qbf_dom_inst                          none
% 31.89/4.55  --qbf_dom_pre_inst                      false
% 31.89/4.55  --qbf_sk_in                             false
% 31.89/4.55  --qbf_pred_elim                         true
% 31.89/4.55  --qbf_split                             512
% 31.89/4.55  
% 31.89/4.55  ------ BMC1 Options
% 31.89/4.55  
% 31.89/4.55  --bmc1_incremental                      false
% 31.89/4.55  --bmc1_axioms                           reachable_all
% 31.89/4.55  --bmc1_min_bound                        0
% 31.89/4.55  --bmc1_max_bound                        -1
% 31.89/4.55  --bmc1_max_bound_default                -1
% 31.89/4.55  --bmc1_symbol_reachability              true
% 31.89/4.55  --bmc1_property_lemmas                  false
% 31.89/4.55  --bmc1_k_induction                      false
% 31.89/4.55  --bmc1_non_equiv_states                 false
% 31.89/4.55  --bmc1_deadlock                         false
% 31.89/4.55  --bmc1_ucm                              false
% 31.89/4.55  --bmc1_add_unsat_core                   none
% 31.89/4.55  --bmc1_unsat_core_children              false
% 31.89/4.55  --bmc1_unsat_core_extrapolate_axioms    false
% 31.89/4.55  --bmc1_out_stat                         full
% 31.89/4.55  --bmc1_ground_init                      false
% 31.89/4.55  --bmc1_pre_inst_next_state              false
% 31.89/4.55  --bmc1_pre_inst_state                   false
% 31.89/4.55  --bmc1_pre_inst_reach_state             false
% 31.89/4.55  --bmc1_out_unsat_core                   false
% 31.89/4.55  --bmc1_aig_witness_out                  false
% 31.89/4.55  --bmc1_verbose                          false
% 31.89/4.55  --bmc1_dump_clauses_tptp                false
% 31.89/4.55  --bmc1_dump_unsat_core_tptp             false
% 31.89/4.55  --bmc1_dump_file                        -
% 31.89/4.55  --bmc1_ucm_expand_uc_limit              128
% 31.89/4.55  --bmc1_ucm_n_expand_iterations          6
% 31.89/4.55  --bmc1_ucm_extend_mode                  1
% 31.89/4.55  --bmc1_ucm_init_mode                    2
% 31.89/4.55  --bmc1_ucm_cone_mode                    none
% 31.89/4.55  --bmc1_ucm_reduced_relation_type        0
% 31.89/4.55  --bmc1_ucm_relax_model                  4
% 31.89/4.55  --bmc1_ucm_full_tr_after_sat            true
% 31.89/4.55  --bmc1_ucm_expand_neg_assumptions       false
% 31.89/4.55  --bmc1_ucm_layered_model                none
% 31.89/4.55  --bmc1_ucm_max_lemma_size               10
% 31.89/4.55  
% 31.89/4.55  ------ AIG Options
% 31.89/4.55  
% 31.89/4.55  --aig_mode                              false
% 31.89/4.55  
% 31.89/4.55  ------ Instantiation Options
% 31.89/4.55  
% 31.89/4.55  --instantiation_flag                    true
% 31.89/4.55  --inst_sos_flag                         false
% 31.89/4.55  --inst_sos_phase                        true
% 31.89/4.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.89/4.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.89/4.55  --inst_lit_sel_side                     none
% 31.89/4.55  --inst_solver_per_active                1400
% 31.89/4.55  --inst_solver_calls_frac                1.
% 31.89/4.55  --inst_passive_queue_type               priority_queues
% 31.89/4.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.89/4.55  --inst_passive_queues_freq              [25;2]
% 31.89/4.55  --inst_dismatching                      true
% 31.89/4.55  --inst_eager_unprocessed_to_passive     true
% 31.89/4.55  --inst_prop_sim_given                   true
% 31.89/4.55  --inst_prop_sim_new                     false
% 31.89/4.55  --inst_subs_new                         false
% 31.89/4.55  --inst_eq_res_simp                      false
% 31.89/4.55  --inst_subs_given                       false
% 31.89/4.55  --inst_orphan_elimination               true
% 31.89/4.55  --inst_learning_loop_flag               true
% 31.89/4.55  --inst_learning_start                   3000
% 31.89/4.55  --inst_learning_factor                  2
% 31.89/4.55  --inst_start_prop_sim_after_learn       3
% 31.89/4.55  --inst_sel_renew                        solver
% 31.89/4.55  --inst_lit_activity_flag                true
% 31.89/4.55  --inst_restr_to_given                   false
% 31.89/4.55  --inst_activity_threshold               500
% 31.89/4.55  --inst_out_proof                        true
% 31.89/4.55  
% 31.89/4.55  ------ Resolution Options
% 31.89/4.55  
% 31.89/4.55  --resolution_flag                       false
% 31.89/4.55  --res_lit_sel                           adaptive
% 31.89/4.55  --res_lit_sel_side                      none
% 31.89/4.55  --res_ordering                          kbo
% 31.89/4.55  --res_to_prop_solver                    active
% 31.89/4.55  --res_prop_simpl_new                    false
% 31.89/4.55  --res_prop_simpl_given                  true
% 31.89/4.55  --res_passive_queue_type                priority_queues
% 31.89/4.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.89/4.55  --res_passive_queues_freq               [15;5]
% 31.89/4.55  --res_forward_subs                      full
% 31.89/4.55  --res_backward_subs                     full
% 31.89/4.55  --res_forward_subs_resolution           true
% 31.89/4.55  --res_backward_subs_resolution          true
% 31.89/4.55  --res_orphan_elimination                true
% 31.89/4.55  --res_time_limit                        2.
% 31.89/4.55  --res_out_proof                         true
% 31.89/4.55  
% 31.89/4.55  ------ Superposition Options
% 31.89/4.55  
% 31.89/4.55  --superposition_flag                    true
% 31.89/4.55  --sup_passive_queue_type                priority_queues
% 31.89/4.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.89/4.55  --sup_passive_queues_freq               [8;1;4]
% 31.89/4.55  --demod_completeness_check              fast
% 31.89/4.55  --demod_use_ground                      true
% 31.89/4.55  --sup_to_prop_solver                    passive
% 31.89/4.55  --sup_prop_simpl_new                    true
% 31.89/4.55  --sup_prop_simpl_given                  true
% 31.89/4.55  --sup_fun_splitting                     false
% 31.89/4.55  --sup_smt_interval                      50000
% 31.89/4.55  
% 31.89/4.55  ------ Superposition Simplification Setup
% 31.89/4.55  
% 31.89/4.55  --sup_indices_passive                   []
% 31.89/4.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.89/4.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.89/4.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.89/4.55  --sup_full_triv                         [TrivRules;PropSubs]
% 31.89/4.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.89/4.55  --sup_full_bw                           [BwDemod]
% 31.89/4.55  --sup_immed_triv                        [TrivRules]
% 31.89/4.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.89/4.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.89/4.55  --sup_immed_bw_main                     []
% 31.89/4.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.89/4.55  --sup_input_triv                        [Unflattening;TrivRules]
% 31.89/4.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.89/4.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.89/4.55  
% 31.89/4.55  ------ Combination Options
% 31.89/4.55  
% 31.89/4.55  --comb_res_mult                         3
% 31.89/4.55  --comb_sup_mult                         2
% 31.89/4.55  --comb_inst_mult                        10
% 31.89/4.55  
% 31.89/4.55  ------ Debug Options
% 31.89/4.55  
% 31.89/4.55  --dbg_backtrace                         false
% 31.89/4.55  --dbg_dump_prop_clauses                 false
% 31.89/4.55  --dbg_dump_prop_clauses_file            -
% 31.89/4.55  --dbg_out_stat                          false
% 31.89/4.55  
% 31.89/4.55  
% 31.89/4.55  
% 31.89/4.55  
% 31.89/4.55  ------ Proving...
% 31.89/4.55  
% 31.89/4.55  
% 31.89/4.55  % SZS status Theorem for theBenchmark.p
% 31.89/4.55  
% 31.89/4.55  % SZS output start CNFRefutation for theBenchmark.p
% 31.89/4.55  
% 31.89/4.55  fof(f1,axiom,(
% 31.89/4.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f40,plain,(
% 31.89/4.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.89/4.55    inference(nnf_transformation,[],[f1])).
% 31.89/4.55  
% 31.89/4.55  fof(f41,plain,(
% 31.89/4.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.89/4.55    inference(flattening,[],[f40])).
% 31.89/4.55  
% 31.89/4.55  fof(f50,plain,(
% 31.89/4.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 31.89/4.55    inference(cnf_transformation,[],[f41])).
% 31.89/4.55  
% 31.89/4.55  fof(f83,plain,(
% 31.89/4.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.89/4.55    inference(equality_resolution,[],[f50])).
% 31.89/4.55  
% 31.89/4.55  fof(f17,conjecture,(
% 31.89/4.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f18,negated_conjecture,(
% 31.89/4.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 31.89/4.55    inference(negated_conjecture,[],[f17])).
% 31.89/4.55  
% 31.89/4.55  fof(f38,plain,(
% 31.89/4.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 31.89/4.55    inference(ennf_transformation,[],[f18])).
% 31.89/4.55  
% 31.89/4.55  fof(f39,plain,(
% 31.89/4.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 31.89/4.55    inference(flattening,[],[f38])).
% 31.89/4.55  
% 31.89/4.55  fof(f47,plain,(
% 31.89/4.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 31.89/4.55    introduced(choice_axiom,[])).
% 31.89/4.55  
% 31.89/4.55  fof(f48,plain,(
% 31.89/4.55    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 31.89/4.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f47])).
% 31.89/4.55  
% 31.89/4.55  fof(f79,plain,(
% 31.89/4.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.89/4.55    inference(cnf_transformation,[],[f48])).
% 31.89/4.55  
% 31.89/4.55  fof(f16,axiom,(
% 31.89/4.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f36,plain,(
% 31.89/4.55    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 31.89/4.55    inference(ennf_transformation,[],[f16])).
% 31.89/4.55  
% 31.89/4.55  fof(f37,plain,(
% 31.89/4.55    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 31.89/4.55    inference(flattening,[],[f36])).
% 31.89/4.55  
% 31.89/4.55  fof(f76,plain,(
% 31.89/4.55    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f37])).
% 31.89/4.55  
% 31.89/4.55  fof(f77,plain,(
% 31.89/4.55    v1_funct_1(sK3)),
% 31.89/4.55    inference(cnf_transformation,[],[f48])).
% 31.89/4.55  
% 31.89/4.55  fof(f15,axiom,(
% 31.89/4.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f34,plain,(
% 31.89/4.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 31.89/4.55    inference(ennf_transformation,[],[f15])).
% 31.89/4.55  
% 31.89/4.55  fof(f35,plain,(
% 31.89/4.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 31.89/4.55    inference(flattening,[],[f34])).
% 31.89/4.55  
% 31.89/4.55  fof(f75,plain,(
% 31.89/4.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f35])).
% 31.89/4.55  
% 31.89/4.55  fof(f11,axiom,(
% 31.89/4.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f19,plain,(
% 31.89/4.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 31.89/4.55    inference(pure_predicate_removal,[],[f11])).
% 31.89/4.55  
% 31.89/4.55  fof(f28,plain,(
% 31.89/4.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.89/4.55    inference(ennf_transformation,[],[f19])).
% 31.89/4.55  
% 31.89/4.55  fof(f65,plain,(
% 31.89/4.55    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.89/4.55    inference(cnf_transformation,[],[f28])).
% 31.89/4.55  
% 31.89/4.55  fof(f6,axiom,(
% 31.89/4.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f22,plain,(
% 31.89/4.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.89/4.55    inference(ennf_transformation,[],[f6])).
% 31.89/4.55  
% 31.89/4.55  fof(f45,plain,(
% 31.89/4.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 31.89/4.55    inference(nnf_transformation,[],[f22])).
% 31.89/4.55  
% 31.89/4.55  fof(f59,plain,(
% 31.89/4.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f45])).
% 31.89/4.55  
% 31.89/4.55  fof(f10,axiom,(
% 31.89/4.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f27,plain,(
% 31.89/4.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.89/4.55    inference(ennf_transformation,[],[f10])).
% 31.89/4.55  
% 31.89/4.55  fof(f64,plain,(
% 31.89/4.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.89/4.55    inference(cnf_transformation,[],[f27])).
% 31.89/4.55  
% 31.89/4.55  fof(f80,plain,(
% 31.89/4.55    r1_tarski(sK2,sK0)),
% 31.89/4.55    inference(cnf_transformation,[],[f48])).
% 31.89/4.55  
% 31.89/4.55  fof(f14,axiom,(
% 31.89/4.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f32,plain,(
% 31.89/4.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.89/4.55    inference(ennf_transformation,[],[f14])).
% 31.89/4.55  
% 31.89/4.55  fof(f33,plain,(
% 31.89/4.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.89/4.55    inference(flattening,[],[f32])).
% 31.89/4.55  
% 31.89/4.55  fof(f46,plain,(
% 31.89/4.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.89/4.55    inference(nnf_transformation,[],[f33])).
% 31.89/4.55  
% 31.89/4.55  fof(f68,plain,(
% 31.89/4.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.89/4.55    inference(cnf_transformation,[],[f46])).
% 31.89/4.55  
% 31.89/4.55  fof(f78,plain,(
% 31.89/4.55    v1_funct_2(sK3,sK0,sK1)),
% 31.89/4.55    inference(cnf_transformation,[],[f48])).
% 31.89/4.55  
% 31.89/4.55  fof(f12,axiom,(
% 31.89/4.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f29,plain,(
% 31.89/4.55    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.89/4.55    inference(ennf_transformation,[],[f12])).
% 31.89/4.55  
% 31.89/4.55  fof(f66,plain,(
% 31.89/4.55    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.89/4.55    inference(cnf_transformation,[],[f29])).
% 31.89/4.55  
% 31.89/4.55  fof(f9,axiom,(
% 31.89/4.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f25,plain,(
% 31.89/4.55    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 31.89/4.55    inference(ennf_transformation,[],[f9])).
% 31.89/4.55  
% 31.89/4.55  fof(f26,plain,(
% 31.89/4.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 31.89/4.55    inference(flattening,[],[f25])).
% 31.89/4.55  
% 31.89/4.55  fof(f63,plain,(
% 31.89/4.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f26])).
% 31.89/4.55  
% 31.89/4.55  fof(f7,axiom,(
% 31.89/4.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f23,plain,(
% 31.89/4.55    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 31.89/4.55    inference(ennf_transformation,[],[f7])).
% 31.89/4.55  
% 31.89/4.55  fof(f61,plain,(
% 31.89/4.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f23])).
% 31.89/4.55  
% 31.89/4.55  fof(f4,axiom,(
% 31.89/4.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f44,plain,(
% 31.89/4.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.89/4.55    inference(nnf_transformation,[],[f4])).
% 31.89/4.55  
% 31.89/4.55  fof(f57,plain,(
% 31.89/4.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f44])).
% 31.89/4.55  
% 31.89/4.55  fof(f3,axiom,(
% 31.89/4.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f42,plain,(
% 31.89/4.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.89/4.55    inference(nnf_transformation,[],[f3])).
% 31.89/4.55  
% 31.89/4.55  fof(f43,plain,(
% 31.89/4.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.89/4.55    inference(flattening,[],[f42])).
% 31.89/4.55  
% 31.89/4.55  fof(f53,plain,(
% 31.89/4.55    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f43])).
% 31.89/4.55  
% 31.89/4.55  fof(f54,plain,(
% 31.89/4.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 31.89/4.55    inference(cnf_transformation,[],[f43])).
% 31.89/4.55  
% 31.89/4.55  fof(f86,plain,(
% 31.89/4.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 31.89/4.55    inference(equality_resolution,[],[f54])).
% 31.89/4.55  
% 31.89/4.55  fof(f49,plain,(
% 31.89/4.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.89/4.55    inference(cnf_transformation,[],[f41])).
% 31.89/4.55  
% 31.89/4.55  fof(f84,plain,(
% 31.89/4.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.89/4.55    inference(equality_resolution,[],[f49])).
% 31.89/4.55  
% 31.89/4.55  fof(f82,plain,(
% 31.89/4.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 31.89/4.55    inference(cnf_transformation,[],[f48])).
% 31.89/4.55  
% 31.89/4.55  fof(f8,axiom,(
% 31.89/4.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f24,plain,(
% 31.89/4.55    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 31.89/4.55    inference(ennf_transformation,[],[f8])).
% 31.89/4.55  
% 31.89/4.55  fof(f62,plain,(
% 31.89/4.55    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f24])).
% 31.89/4.55  
% 31.89/4.55  fof(f56,plain,(
% 31.89/4.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.89/4.55    inference(cnf_transformation,[],[f44])).
% 31.89/4.55  
% 31.89/4.55  fof(f51,plain,(
% 31.89/4.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f41])).
% 31.89/4.55  
% 31.89/4.55  fof(f72,plain,(
% 31.89/4.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.89/4.55    inference(cnf_transformation,[],[f46])).
% 31.89/4.55  
% 31.89/4.55  fof(f89,plain,(
% 31.89/4.55    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 31.89/4.55    inference(equality_resolution,[],[f72])).
% 31.89/4.55  
% 31.89/4.55  fof(f55,plain,(
% 31.89/4.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 31.89/4.55    inference(cnf_transformation,[],[f43])).
% 31.89/4.55  
% 31.89/4.55  fof(f85,plain,(
% 31.89/4.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 31.89/4.55    inference(equality_resolution,[],[f55])).
% 31.89/4.55  
% 31.89/4.55  fof(f81,plain,(
% 31.89/4.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 31.89/4.55    inference(cnf_transformation,[],[f48])).
% 31.89/4.55  
% 31.89/4.55  fof(f74,plain,(
% 31.89/4.55    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f35])).
% 31.89/4.55  
% 31.89/4.55  fof(f2,axiom,(
% 31.89/4.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f20,plain,(
% 31.89/4.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 31.89/4.55    inference(ennf_transformation,[],[f2])).
% 31.89/4.55  
% 31.89/4.55  fof(f52,plain,(
% 31.89/4.55    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f20])).
% 31.89/4.55  
% 31.89/4.55  fof(f13,axiom,(
% 31.89/4.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f30,plain,(
% 31.89/4.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 31.89/4.55    inference(ennf_transformation,[],[f13])).
% 31.89/4.55  
% 31.89/4.55  fof(f31,plain,(
% 31.89/4.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 31.89/4.55    inference(flattening,[],[f30])).
% 31.89/4.55  
% 31.89/4.55  fof(f67,plain,(
% 31.89/4.55    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f31])).
% 31.89/4.55  
% 31.89/4.55  fof(f73,plain,(
% 31.89/4.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.89/4.55    inference(cnf_transformation,[],[f46])).
% 31.89/4.55  
% 31.89/4.55  fof(f87,plain,(
% 31.89/4.55    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.89/4.55    inference(equality_resolution,[],[f73])).
% 31.89/4.55  
% 31.89/4.55  fof(f88,plain,(
% 31.89/4.55    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 31.89/4.55    inference(equality_resolution,[],[f87])).
% 31.89/4.55  
% 31.89/4.55  fof(f5,axiom,(
% 31.89/4.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.89/4.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.55  
% 31.89/4.55  fof(f21,plain,(
% 31.89/4.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.89/4.55    inference(ennf_transformation,[],[f5])).
% 31.89/4.55  
% 31.89/4.55  fof(f58,plain,(
% 31.89/4.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.89/4.55    inference(cnf_transformation,[],[f21])).
% 31.89/4.55  
% 31.89/4.55  fof(f70,plain,(
% 31.89/4.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.89/4.55    inference(cnf_transformation,[],[f46])).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1,plain,
% 31.89/4.55      ( r1_tarski(X0,X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f83]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1425,plain,
% 31.89/4.55      ( r1_tarski(X0,X0) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_31,negated_conjecture,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.89/4.55      inference(cnf_transformation,[],[f79]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1411,plain,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_27,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | ~ v1_funct_1(X0)
% 31.89/4.55      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 31.89/4.55      inference(cnf_transformation,[],[f76]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1413,plain,
% 31.89/4.55      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 31.89/4.55      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.89/4.55      | v1_funct_1(X2) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5916,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 31.89/4.55      | v1_funct_1(sK3) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1411,c_1413]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_33,negated_conjecture,
% 31.89/4.55      ( v1_funct_1(sK3) ),
% 31.89/4.55      inference(cnf_transformation,[],[f77]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1707,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | ~ v1_funct_1(sK3)
% 31.89/4.55      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_27]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3588,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | ~ v1_funct_1(sK3)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1707]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6265,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_5916,c_33,c_31,c_3588]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_25,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | ~ v1_funct_1(X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f75]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1415,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.89/4.55      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.89/4.55      | v1_funct_1(X0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6402,plain,
% 31.89/4.55      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.89/4.55      | v1_funct_1(sK3) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_6265,c_1415]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_34,plain,
% 31.89/4.55      ( v1_funct_1(sK3) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_36,plain,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6522,plain,
% 31.89/4.55      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_6402,c_34,c_36]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_16,plain,
% 31.89/4.55      ( v5_relat_1(X0,X1)
% 31.89/4.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 31.89/4.55      inference(cnf_transformation,[],[f65]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11,plain,
% 31.89/4.55      ( ~ v5_relat_1(X0,X1)
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),X1)
% 31.89/4.55      | ~ v1_relat_1(X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f59]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_400,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),X2)
% 31.89/4.55      | ~ v1_relat_1(X0) ),
% 31.89/4.55      inference(resolution,[status(thm)],[c_16,c_11]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_15,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | v1_relat_1(X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f64]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_404,plain,
% 31.89/4.55      ( r1_tarski(k2_relat_1(X0),X2)
% 31.89/4.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_400,c_15]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_405,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),X2) ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_404]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1408,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6534,plain,
% 31.89/4.55      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_6522,c_1408]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_30,negated_conjecture,
% 31.89/4.55      ( r1_tarski(sK2,sK0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f80]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1412,plain,
% 31.89/4.55      ( r1_tarski(sK2,sK0) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_24,plain,
% 31.89/4.55      ( ~ v1_funct_2(X0,X1,X2)
% 31.89/4.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | k1_relset_1(X1,X2,X0) = X1
% 31.89/4.55      | k1_xboole_0 = X2 ),
% 31.89/4.55      inference(cnf_transformation,[],[f68]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_32,negated_conjecture,
% 31.89/4.55      ( v1_funct_2(sK3,sK0,sK1) ),
% 31.89/4.55      inference(cnf_transformation,[],[f78]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_523,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | k1_relset_1(X1,X2,X0) = X1
% 31.89/4.55      | sK3 != X0
% 31.89/4.55      | sK1 != X2
% 31.89/4.55      | sK0 != X1
% 31.89/4.55      | k1_xboole_0 = X2 ),
% 31.89/4.55      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_524,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | k1_relset_1(sK0,sK1,sK3) = sK0
% 31.89/4.55      | k1_xboole_0 = sK1 ),
% 31.89/4.55      inference(unflattening,[status(thm)],[c_523]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_526,plain,
% 31.89/4.55      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_524,c_31]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_17,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f66]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1417,plain,
% 31.89/4.55      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.89/4.55      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3066,plain,
% 31.89/4.55      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1411,c_1417]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3461,plain,
% 31.89/4.55      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_526,c_3066]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1418,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2442,plain,
% 31.89/4.55      ( v1_relat_1(sK3) = iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1411,c_1418]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 31.89/4.55      | ~ v1_relat_1(X1)
% 31.89/4.55      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 31.89/4.55      inference(cnf_transformation,[],[f63]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1419,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 31.89/4.55      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4228,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1425,c_1419]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_10889,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_2442,c_4228]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11571,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,sK0)) = k1_relat_1(sK3)
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_3461,c_10889]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_12,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f61]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1421,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11573,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
% 31.89/4.55      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_10889,c_1419]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6533,plain,
% 31.89/4.55      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_6522,c_1418]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11890,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
% 31.89/4.55      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 31.89/4.55      inference(forward_subsumption_resolution,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_11573,c_6533]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11901,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
% 31.89/4.55      | sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(X0,sK0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_3461,c_11890]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11950,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(k7_relat_1(X0,sK0)))) = k1_relat_1(k7_relat_1(X0,sK0))
% 31.89/4.55      | sK1 = k1_xboole_0
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1421,c_11901]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14084,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(k7_relat_1(sK3,sK0)))) = k1_relat_1(k7_relat_1(sK3,sK0))
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_2442,c_11950]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14144,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),k1_relat_1(k7_relat_1(sK3,sK0)))) = k1_relat_1(k7_relat_1(sK3,sK0))
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_3461,c_14084]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14250,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),k1_relat_1(sK3))) = k1_relat_1(k7_relat_1(sK3,sK0))
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_11571,c_14144]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_15557,plain,
% 31.89/4.55      ( sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),k1_relat_1(sK3)) = iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_14250,c_1421]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_76,plain,
% 31.89/4.55      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 31.89/4.55      | v1_relat_1(k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_15]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.89/4.55      inference(cnf_transformation,[],[f57]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_98,plain,
% 31.89/4.55      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 31.89/4.55      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_7]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6,plain,
% 31.89/4.55      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = X0
% 31.89/4.55      | k1_xboole_0 = X1 ),
% 31.89/4.55      inference(cnf_transformation,[],[f53]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_100,plain,
% 31.89/4.55      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5,plain,
% 31.89/4.55      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.89/4.55      inference(cnf_transformation,[],[f86]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_101,plain,
% 31.89/4.55      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_5]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2,plain,
% 31.89/4.55      ( r1_tarski(X0,X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f84]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_106,plain,
% 31.89/4.55      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_28,negated_conjecture,
% 31.89/4.55      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 31.89/4.55      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 31.89/4.55      inference(cnf_transformation,[],[f82]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_534,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 31.89/4.55      | sK2 != sK0
% 31.89/4.55      | sK1 != sK1 ),
% 31.89/4.55      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1646,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_7]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1648,plain,
% 31.89/4.55      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 31.89/4.55      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1646]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1651,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_15]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_819,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1678,plain,
% 31.89/4.55      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1679,plain,
% 31.89/4.55      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1678]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_13,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f62]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1722,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_13]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1729,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) | ~ v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1722]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_818,plain,( X0 = X0 ),theory(equality) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1835,plain,
% 31.89/4.55      ( sK1 = sK1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_818]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_820,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.89/4.55      theory(equality) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1878,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1)
% 31.89/4.55      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 31.89/4.55      | X2 != X0
% 31.89/4.55      | k2_zfmisc_1(X3,X4) != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1880,plain,
% 31.89/4.55      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 31.89/4.55      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 31.89/4.55      | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1878]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.89/4.55      inference(cnf_transformation,[],[f56]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1907,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_8]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1925,plain,
% 31.89/4.55      ( sK0 = sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_818]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1978,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_0,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.89/4.55      inference(cnf_transformation,[],[f51]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1746,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_0]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1995,plain,
% 31.89/4.55      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1746]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1996,plain,
% 31.89/4.55      ( r1_tarski(sK3,sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2021,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_0]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2023,plain,
% 31.89/4.55      ( ~ r1_tarski(sK3,k1_xboole_0)
% 31.89/4.55      | ~ r1_tarski(k1_xboole_0,sK3)
% 31.89/4.55      | sK3 = k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2021]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_20,plain,
% 31.89/4.55      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 31.89/4.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 31.89/4.55      | k1_xboole_0 = X1
% 31.89/4.55      | k1_xboole_0 = X0 ),
% 31.89/4.55      inference(cnf_transformation,[],[f89]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_455,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 31.89/4.55      | sK3 != X0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | sK0 != X1
% 31.89/4.55      | k1_xboole_0 = X0
% 31.89/4.55      | k1_xboole_0 = X1 ),
% 31.89/4.55      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_456,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = sK3
% 31.89/4.55      | k1_xboole_0 = sK0 ),
% 31.89/4.55      inference(unflattening,[status(thm)],[c_455]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1406,plain,
% 31.89/4.55      ( sK1 != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = sK3
% 31.89/4.55      | k1_xboole_0 = sK0
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4,plain,
% 31.89/4.55      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.55      inference(cnf_transformation,[],[f85]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1510,plain,
% 31.89/4.55      ( sK3 = k1_xboole_0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | sK0 = k1_xboole_0
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 31.89/4.55      inference(demodulation,[status(thm)],[c_1406,c_4]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_29,negated_conjecture,
% 31.89/4.55      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 31.89/4.55      inference(cnf_transformation,[],[f81]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1677,plain,
% 31.89/4.55      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1924,plain,
% 31.89/4.55      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1677]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2072,plain,
% 31.89/4.55      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2073,plain,
% 31.89/4.55      ( sK1 != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = sK1
% 31.89/4.55      | k1_xboole_0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2072]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2136,plain,
% 31.89/4.55      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_1510,c_29,c_100,c_101,c_1924,c_1925,c_2073]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2137,plain,
% 31.89/4.55      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_2136]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_26,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | ~ v1_funct_1(X0)
% 31.89/4.55      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 31.89/4.55      inference(cnf_transformation,[],[f74]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1691,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 31.89/4.55      | ~ v1_funct_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_26]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2029,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 31.89/4.55      | ~ v1_funct_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1691]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2148,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.89/4.55      | ~ v1_funct_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2029]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2224,plain,
% 31.89/4.55      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2225,plain,
% 31.89/4.55      ( sK0 != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = sK0
% 31.89/4.55      | k1_xboole_0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2224]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2723,plain,
% 31.89/4.55      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_818]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_824,plain,
% 31.89/4.55      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 31.89/4.55      theory(equality) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2728,plain,
% 31.89/4.55      ( k1_relat_1(sK3) = k1_relat_1(X0) | sK3 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_824]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2733,plain,
% 31.89/4.55      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2728]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1420,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 31.89/4.55      inference(cnf_transformation,[],[f52]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1424,plain,
% 31.89/4.55      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2259,plain,
% 31.89/4.55      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 31.89/4.55      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1420,c_1424]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_75,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_77,plain,
% 31.89/4.55      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 31.89/4.55      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_75]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_105,plain,
% 31.89/4.55      ( r1_tarski(X0,X0) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_107,plain,
% 31.89/4.55      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_105]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1647,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.89/4.55      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1649,plain,
% 31.89/4.55      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 31.89/4.55      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1647]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1879,plain,
% 31.89/4.55      ( X0 != X1
% 31.89/4.55      | k2_zfmisc_1(X2,X3) != X4
% 31.89/4.55      | r1_tarski(X1,X4) != iProver_top
% 31.89/4.55      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1878]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1881,plain,
% 31.89/4.55      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k1_xboole_0
% 31.89/4.55      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1879]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2264,plain,
% 31.89/4.55      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_2259,c_77,c_100,c_101,c_107,c_1649,c_1881]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2900,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 31.89/4.55      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_2264,c_1421]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2922,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
% 31.89/4.55      | ~ v1_relat_1(k1_xboole_0) ),
% 31.89/4.55      inference(predicate_to_equality_rev,[status(thm)],[c_2900]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2924,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 31.89/4.55      | ~ v1_relat_1(k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2922]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_823,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.89/4.55      theory(equality) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1696,plain,
% 31.89/4.55      ( m1_subset_1(X0,X1)
% 31.89/4.55      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 31.89/4.55      | X0 != X2
% 31.89/4.55      | X1 != k1_zfmisc_1(X3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_823]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1904,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.89/4.55      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 31.89/4.55      | X2 != X0
% 31.89/4.55      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1696]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3260,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.89/4.55      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1904]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3262,plain,
% 31.89/4.55      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3260]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3590,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | ~ v1_funct_1(sK3)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3588]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1951,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK3) | X2 != X0 | sK3 != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2714,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,sK3) | r1_tarski(X1,sK3) | X1 != X0 | sK3 != sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1951]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5166,plain,
% 31.89/4.55      ( r1_tarski(X0,sK3)
% 31.89/4.55      | ~ r1_tarski(k7_relat_1(sK3,X1),sK3)
% 31.89/4.55      | X0 != k7_relat_1(sK3,X1)
% 31.89/4.55      | sK3 != sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2714]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5168,plain,
% 31.89/4.55      ( ~ r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3)
% 31.89/4.55      | r1_tarski(k1_xboole_0,sK3)
% 31.89/4.55      | sK3 != sK3
% 31.89/4.55      | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_5166]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2726,plain,
% 31.89/4.55      ( X0 != X1 | k1_relat_1(sK3) != X1 | k1_relat_1(sK3) = X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5223,plain,
% 31.89/4.55      ( X0 != k1_relat_1(sK3)
% 31.89/4.55      | k1_relat_1(sK3) = X0
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2726]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5224,plain,
% 31.89/4.55      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.89/4.55      | k1_relat_1(sK3) = k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_5223]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2292,plain,
% 31.89/4.55      ( X0 != X1
% 31.89/4.55      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6025,plain,
% 31.89/4.55      ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
% 31.89/4.55      | X0 != k7_relat_1(sK3,X1)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2292]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6026,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0)
% 31.89/4.55      | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 31.89/4.55      | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6025]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3491,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) != X0
% 31.89/4.55      | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6505,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(X0,X1)
% 31.89/4.55      | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3491]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6507,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 31.89/4.55      | k2_zfmisc_1(sK2,sK1) = k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6505]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_821,plain,
% 31.89/4.55      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 31.89/4.55      theory(equality) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6506,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(X0,X1)
% 31.89/4.55      | sK2 != X0
% 31.89/4.55      | sK1 != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_821]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6508,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 31.89/4.55      | sK2 != k1_xboole_0
% 31.89/4.55      | sK1 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6506]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3504,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK0,sK1) != X0
% 31.89/4.55      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6515,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
% 31.89/4.55      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3504]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6517,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 31.89/4.55      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6515]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6516,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
% 31.89/4.55      | sK1 != X1
% 31.89/4.55      | sK0 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_821]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6518,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | sK0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6516]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6669,plain,
% 31.89/4.55      ( ~ r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
% 31.89/4.55      | k1_xboole_0 = k7_relat_1(sK3,X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6670,plain,
% 31.89/4.55      ( k1_xboole_0 = k7_relat_1(sK3,X0)
% 31.89/4.55      | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_6669]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6672,plain,
% 31.89/4.55      ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
% 31.89/4.55      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6670]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1816,plain,
% 31.89/4.55      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1411,c_1408]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_18,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | ~ r1_tarski(k1_relat_1(X0),X1)
% 31.89/4.55      | ~ r1_tarski(k2_relat_1(X0),X2)
% 31.89/4.55      | ~ v1_relat_1(X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f67]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1416,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4714,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_5,c_1416]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7050,plain,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1816,c_4714]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1652,plain,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.89/4.55      | v1_relat_1(sK3) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7477,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_7050,c_36,c_1652]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7478,plain,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_7477]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7479,plain,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 31.89/4.55      | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
% 31.89/4.55      inference(predicate_to_equality_rev,[status(thm)],[c_7478]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_19,plain,
% 31.89/4.55      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 31.89/4.55      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 31.89/4.55      | k1_xboole_0 = X0 ),
% 31.89/4.55      inference(cnf_transformation,[],[f88]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_429,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 31.89/4.55      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK2 != X0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = X0 ),
% 31.89/4.55      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_430,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 31.89/4.55      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = sK2 ),
% 31.89/4.55      inference(unflattening,[status(thm)],[c_429]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1407,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = sK2
% 31.89/4.55      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.89/4.55      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 31.89/4.55      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1561,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK2 = k1_xboole_0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.89/4.55      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.89/4.55      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(demodulation,[status(thm)],[c_1407,c_4]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_97,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.89/4.55      | r1_tarski(X0,X1) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_99,plain,
% 31.89/4.55      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_97]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2075,plain,
% 31.89/4.55      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | sK2 = k1_xboole_0
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.89/4.55      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_1561,c_99,c_107]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2076,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK2 = k1_xboole_0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.89/4.55      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_2075]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6270,plain,
% 31.89/4.55      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK2 = k1_xboole_0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.89/4.55      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(demodulation,[status(thm)],[c_6265,c_2076]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1414,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.89/4.55      | v1_funct_1(X0) != iProver_top
% 31.89/4.55      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2794,plain,
% 31.89/4.55      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 31.89/4.55      | v1_funct_1(sK3) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1411,c_1414]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2030,plain,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.89/4.55      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 31.89/4.55      | v1_funct_1(sK3) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_2029]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3464,plain,
% 31.89/4.55      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_2794,c_34,c_36,c_2030]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6273,plain,
% 31.89/4.55      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 31.89/4.55      inference(demodulation,[status(thm)],[c_6265,c_3464]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6297,plain,
% 31.89/4.55      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK2 = k1_xboole_0
% 31.89/4.55      | sK1 != k1_xboole_0
% 31.89/4.55      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 31.89/4.55      inference(forward_subsumption_resolution,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_6270,c_6273]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1676,plain,
% 31.89/4.55      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1918,plain,
% 31.89/4.55      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1676]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1919,plain,
% 31.89/4.55      ( sK2 = sK2 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_818]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2206,plain,
% 31.89/4.55      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1808,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1)
% 31.89/4.55      | r1_tarski(sK2,k1_xboole_0)
% 31.89/4.55      | sK2 != X0
% 31.89/4.55      | k1_xboole_0 != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2211,plain,
% 31.89/4.55      ( ~ r1_tarski(sK2,X0)
% 31.89/4.55      | r1_tarski(sK2,k1_xboole_0)
% 31.89/4.55      | sK2 != sK2
% 31.89/4.55      | k1_xboole_0 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1808]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2891,plain,
% 31.89/4.55      ( ~ r1_tarski(sK2,sK0)
% 31.89/4.55      | r1_tarski(sK2,k1_xboole_0)
% 31.89/4.55      | sK2 != sK2
% 31.89/4.55      | k1_xboole_0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2211]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7853,plain,
% 31.89/4.55      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_6297,c_30,c_29,c_100,c_101,c_1918,c_1919,c_2073,
% 31.89/4.55                 c_2206,c_2891]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7854,plain,
% 31.89/4.55      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_7853]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2903,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1421,c_1424]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3737,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_2442,c_2903]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4713,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_4,c_1416]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6181,plain,
% 31.89/4.55      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
% 31.89/4.55      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_3737,c_4713]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1723,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
% 31.89/4.55      | ~ v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_12]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1724,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1723]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1726,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1724]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1728,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1722]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1730,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1728]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_9,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.89/4.55      | ~ v1_relat_1(X1)
% 31.89/4.55      | v1_relat_1(X0) ),
% 31.89/4.55      inference(cnf_transformation,[],[f58]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_239,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.89/4.55      inference(prop_impl,[status(thm)],[c_7]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_240,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_239]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_300,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.89/4.55      inference(bin_hyper_res,[status(thm)],[c_9,c_240]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1737,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,sK3) | v1_relat_1(X0) | ~ v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_300]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1956,plain,
% 31.89/4.55      ( ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,X0))
% 31.89/4.55      | ~ v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1737]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1957,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1956]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1959,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1957]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7051,plain,
% 31.89/4.55      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_6534,c_4714]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7105,plain,
% 31.89/4.55      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_7051]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8098,plain,
% 31.89/4.55      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_6181,c_36,c_1652,c_1726,c_1730,c_1959,c_7105]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1422,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.89/4.55      | r1_tarski(X0,X1) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8103,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_8098,c_1422]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8667,plain,
% 31.89/4.55      ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 31.89/4.55      | k1_xboole_0 = k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1926,plain,
% 31.89/4.55      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8723,plain,
% 31.89/4.55      ( k1_relat_1(sK3) != X0 | sK0 != X0 | sK0 = k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1926]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8726,plain,
% 31.89/4.55      ( k1_relat_1(sK3) != k1_xboole_0
% 31.89/4.55      | sK0 = k1_relat_1(sK3)
% 31.89/4.55      | sK0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_8723]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2703,plain,
% 31.89/4.55      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1926]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8722,plain,
% 31.89/4.55      ( k1_relat_1(sK3) != sK0 | sK0 = k1_relat_1(sK3) | sK0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2703]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3266,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 31.89/4.55      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1)
% 31.89/4.55      | sK3 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1904]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5271,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 31.89/4.55      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X0)
% 31.89/4.55      | sK3 != sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3266]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8834,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 31.89/4.55      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 31.89/4.55      | sK3 != sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_5271]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2016,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1)
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),X2)
% 31.89/4.55      | X2 != X1
% 31.89/4.55      | k1_relat_1(sK3) != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4302,plain,
% 31.89/4.55      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),X1)
% 31.89/4.55      | X1 != X0
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2016]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_9887,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(sK3),X0)
% 31.89/4.55      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 31.89/4.55      | X0 != sK0
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_4302]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_9904,plain,
% 31.89/4.55      ( ~ r1_tarski(k1_relat_1(sK3),sK0)
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.89/4.55      | k1_xboole_0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_9887]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_822,plain,
% 31.89/4.55      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 31.89/4.55      theory(equality) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4159,plain,
% 31.89/4.55      ( k2_zfmisc_1(X0,X1) != X2
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_822]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_10699,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) != X0
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_4159]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_10700,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) != k1_xboole_0
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_10699]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11537,plain,
% 31.89/4.55      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 31.89/4.55      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_822]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_12526,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK0,sK1) != X0
% 31.89/4.55      | k1_xboole_0 != X0
% 31.89/4.55      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_12527,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 31.89/4.55      | k1_xboole_0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_12526]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14458,plain,
% 31.89/4.55      ( k2_zfmisc_1(X0,X1) != X2
% 31.89/4.55      | k1_xboole_0 != X2
% 31.89/4.55      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14459,plain,
% 31.89/4.55      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 31.89/4.55      | k1_xboole_0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_14458]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_9557,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(sK3),X0)
% 31.89/4.55      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 31.89/4.55      | X0 != k1_relat_1(sK3)
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_4302]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_18924,plain,
% 31.89/4.55      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),sK0)
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.89/4.55      | sK0 != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_9557]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_826,plain,
% 31.89/4.55      ( X0 != X1
% 31.89/4.55      | X2 != X3
% 31.89/4.55      | X4 != X5
% 31.89/4.55      | X6 != X7
% 31.89/4.55      | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
% 31.89/4.55      theory(equality) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2295,plain,
% 31.89/4.55      ( X0 != X1
% 31.89/4.55      | X2 != sK3
% 31.89/4.55      | X3 != sK1
% 31.89/4.55      | X4 != sK0
% 31.89/4.55      | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_826]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4086,plain,
% 31.89/4.55      ( X0 != X1
% 31.89/4.55      | X2 != sK1
% 31.89/4.55      | X3 != sK0
% 31.89/4.55      | k2_partfun1(X3,X2,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 31.89/4.55      | sK3 != sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2295]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_10832,plain,
% 31.89/4.55      ( X0 != X1
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 31.89/4.55      | sK3 != sK3
% 31.89/4.55      | sK1 != sK1
% 31.89/4.55      | sK0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_4086]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_21314,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,X0)
% 31.89/4.55      | sK2 != X0
% 31.89/4.55      | sK3 != sK3
% 31.89/4.55      | sK1 != sK1
% 31.89/4.55      | sK0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_10832]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_21317,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 31.89/4.55      | sK2 != k1_xboole_0
% 31.89/4.55      | sK3 != sK3
% 31.89/4.55      | sK1 != sK1
% 31.89/4.55      | sK0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_21314]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_9062,plain,
% 31.89/4.55      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_8103,c_1424]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1426,plain,
% 31.89/4.55      ( X0 = X1
% 31.89/4.55      | r1_tarski(X0,X1) != iProver_top
% 31.89/4.55      | r1_tarski(X1,X0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4106,plain,
% 31.89/4.55      ( k7_relat_1(X0,X1) = X0
% 31.89/4.55      | r1_tarski(X0,k7_relat_1(X0,X1)) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1420,c_1426]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_22237,plain,
% 31.89/4.55      ( k7_relat_1(sK3,k1_xboole_0) = sK3
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_9062,c_4106]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_22242,plain,
% 31.89/4.55      ( sK3 = k1_xboole_0
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(light_normalisation,[status(thm)],[c_22237,c_9062]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_22275,plain,
% 31.89/4.55      ( ~ r1_tarski(sK3,k1_xboole_0)
% 31.89/4.55      | ~ v1_relat_1(sK3)
% 31.89/4.55      | sK3 = k1_xboole_0 ),
% 31.89/4.55      inference(predicate_to_equality_rev,[status(thm)],[c_22242]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_26667,plain,
% 31.89/4.55      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.89/4.55      | k1_relat_1(sK3) = sK0
% 31.89/4.55      | sK0 != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_5223]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1759,plain,
% 31.89/4.55      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_28716,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 31.89/4.55      | sK3 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1759]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_28723,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK3 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_28716]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3577,plain,
% 31.89/4.55      ( X0 != X1
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != X1
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_30917,plain,
% 31.89/4.55      ( X0 != k2_partfun1(sK0,sK1,sK3,X1)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) = X0
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3577]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_30918,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_30917]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_35479,plain,
% 31.89/4.55      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),X2)
% 31.89/4.55      | X2 != X1
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2016]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_35481,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 31.89/4.55      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(k1_xboole_0)
% 31.89/4.55      | k1_xboole_0 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_35479]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_40657,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),k1_relat_1(sK3)) = iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_15557,c_33,c_31,c_76,c_98,c_100,c_101,c_106,c_534,
% 31.89/4.55                 c_1648,c_1651,c_1679,c_1729,c_1835,c_1880,c_1907,c_1925,
% 31.89/4.55                 c_1978,c_1995,c_1996,c_2023,c_2137,c_2148,c_2225,c_2723,
% 31.89/4.55                 c_2733,c_2924,c_3262,c_3461,c_3590,c_5168,c_5224,c_6026,
% 31.89/4.55                 c_6507,c_6508,c_6517,c_6518,c_6672,c_7479,c_7854,c_8103,
% 31.89/4.55                 c_8667,c_8726,c_8722,c_8834,c_9904,c_10700,c_11537,
% 31.89/4.55                 c_12527,c_14459,c_18924,c_21317,c_22275,c_26667,c_28723,
% 31.89/4.55                 c_30918,c_35481]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4233,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 31.89/4.55      | sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(X0,sK0) != iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_3461,c_1419]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4444,plain,
% 31.89/4.55      ( r1_tarski(X0,sK0) != iProver_top
% 31.89/4.55      | sK1 = k1_xboole_0
% 31.89/4.55      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_4233,c_36,c_1652]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4445,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 31.89/4.55      | sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(X0,sK0) != iProver_top ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_4444]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4451,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,sK0)) = sK0 | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1425,c_4445]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14251,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) = k1_relat_1(k7_relat_1(sK3,sK0))
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_4451,c_14144]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14280,plain,
% 31.89/4.55      ( sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),sK0) = iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_14251,c_1421]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_37529,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),sK0) = iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_14280,c_33,c_31,c_76,c_98,c_100,c_101,c_106,c_534,
% 31.89/4.55                 c_1648,c_1651,c_1679,c_1729,c_1835,c_1880,c_1907,c_1925,
% 31.89/4.55                 c_1978,c_1995,c_1996,c_2023,c_2137,c_2148,c_2225,c_2723,
% 31.89/4.55                 c_2733,c_2924,c_3262,c_3461,c_3590,c_5168,c_5224,c_6026,
% 31.89/4.55                 c_6507,c_6508,c_6517,c_6518,c_6672,c_7479,c_7854,c_8103,
% 31.89/4.55                 c_8667,c_8726,c_8722,c_8834,c_9904,c_10700,c_11537,
% 31.89/4.55                 c_12527,c_14459,c_18924,c_21317,c_22275,c_26667,c_28723,
% 31.89/4.55                 c_30918,c_35481]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_37535,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK0)),sK0) = iProver_top ),
% 31.89/4.55      inference(forward_subsumption_resolution,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_37529,c_6533]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_37539,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,sK0)) = sK0
% 31.89/4.55      | r1_tarski(sK0,k1_relat_1(k7_relat_1(sK3,sK0))) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_37535,c_1426]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1981,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1978]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1983,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1)
% 31.89/4.55      | r1_tarski(X2,k1_relat_1(sK3))
% 31.89/4.55      | X2 != X0
% 31.89/4.55      | k1_relat_1(sK3) != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2722,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 31.89/4.55      | r1_tarski(X1,k1_relat_1(sK3))
% 31.89/4.55      | X1 != X0
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1983]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5200,plain,
% 31.89/4.55      ( r1_tarski(X0,k1_relat_1(sK3))
% 31.89/4.55      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 31.89/4.55      | X0 != k1_relat_1(sK3)
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2722]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8721,plain,
% 31.89/4.55      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 31.89/4.55      | r1_tarski(sK0,k1_relat_1(sK3))
% 31.89/4.55      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.89/4.55      | sK0 != k1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_5200]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_8724,plain,
% 31.89/4.55      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.89/4.55      | sK0 != k1_relat_1(sK3)
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 31.89/4.55      | r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_8721]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1736,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 31.89/4.55      | ~ v1_relat_1(sK3)
% 31.89/4.55      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_14]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_17243,plain,
% 31.89/4.55      ( ~ r1_tarski(sK0,k1_relat_1(sK3))
% 31.89/4.55      | ~ v1_relat_1(sK3)
% 31.89/4.55      | k1_relat_1(k7_relat_1(sK3,sK0)) = sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1736]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_17244,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,sK0)) = sK0
% 31.89/4.55      | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_17243]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_38370,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,sK0)) = sK0 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_37539,c_31,c_36,c_76,c_100,c_101,c_106,c_1648,c_1651,
% 31.89/4.55                 c_1652,c_1729,c_1880,c_1907,c_1925,c_1981,c_1995,c_1996,
% 31.89/4.55                 c_2023,c_2137,c_2723,c_2733,c_2924,c_3461,c_5168,c_5224,
% 31.89/4.55                 c_6517,c_6518,c_6672,c_8103,c_8667,c_8724,c_8726,c_8722,
% 31.89/4.55                 c_8834,c_11537,c_12527,c_14459,c_17244,c_26667,c_35481]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_40661,plain,
% 31.89/4.55      ( r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK0)) != iProver_top ),
% 31.89/4.55      inference(light_normalisation,[status(thm)],[c_40657,c_38370]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_40664,plain,
% 31.89/4.55      ( r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top ),
% 31.89/4.55      inference(forward_subsumption_resolution,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_40661,c_6533]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_40667,plain,
% 31.89/4.55      ( k1_relat_1(sK3) = sK0
% 31.89/4.55      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_40664,c_1426]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_41530,plain,
% 31.89/4.55      ( k1_relat_1(sK3) = sK0 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_40667,c_31,c_76,c_100,c_101,c_106,c_1648,c_1651,
% 31.89/4.55                 c_1729,c_1880,c_1907,c_1995,c_1996,c_2023,c_2137,c_2723,
% 31.89/4.55                 c_2733,c_2924,c_3461,c_5168,c_5224,c_6517,c_6518,c_6672,
% 31.89/4.55                 c_8103,c_8667,c_8726,c_8834,c_11537,c_12527,c_14459,
% 31.89/4.55                 c_26667,c_35481]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_41749,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 31.89/4.55      | r1_tarski(X0,sK0) != iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_41530,c_1419]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_41765,plain,
% 31.89/4.55      ( r1_tarski(X0,sK0) != iProver_top
% 31.89/4.55      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_41749,c_33,c_31,c_36,c_76,c_98,c_100,c_101,c_106,
% 31.89/4.55                 c_534,c_1648,c_1651,c_1652,c_1679,c_1729,c_1835,c_1880,
% 31.89/4.55                 c_1907,c_1925,c_1978,c_1995,c_1996,c_2023,c_2137,c_2148,
% 31.89/4.55                 c_2225,c_2723,c_2733,c_2924,c_3262,c_3461,c_3590,c_4233,
% 31.89/4.55                 c_5168,c_5224,c_6026,c_6507,c_6508,c_6517,c_6518,c_6672,
% 31.89/4.55                 c_7479,c_7854,c_8103,c_8667,c_8726,c_8722,c_8834,c_9904,
% 31.89/4.55                 c_10700,c_11537,c_12527,c_14459,c_18924,c_21317,c_22275,
% 31.89/4.55                 c_26667,c_28723,c_30918,c_35481]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_41766,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 31.89/4.55      | r1_tarski(X0,sK0) != iProver_top ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_41765]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_41775,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1412,c_41766]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4716,plain,
% 31.89/4.55      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.89/4.55      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 31.89/4.55      | v1_relat_1(X2) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1416,c_1417]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_133452,plain,
% 31.89/4.55      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 31.89/4.55      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 31.89/4.55      | r1_tarski(sK2,X0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_41775,c_4716]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_133702,plain,
% 31.89/4.55      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = sK2
% 31.89/4.55      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 31.89/4.55      | r1_tarski(sK2,X0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(light_normalisation,[status(thm)],[c_133452,c_41775]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_12652,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~ v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1722]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_12653,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) = iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_12652]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14612,plain,
% 31.89/4.55      ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK2))
% 31.89/4.55      | ~ v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1956]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14613,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 31.89/4.55      | v1_relat_1(sK3) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_14612]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_134854,plain,
% 31.89/4.55      ( r1_tarski(sK2,X0) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 31.89/4.55      | k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = sK2 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_133702,c_36,c_1652,c_12653,c_14613]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_134855,plain,
% 31.89/4.55      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = sK2
% 31.89/4.55      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 31.89/4.55      | r1_tarski(sK2,X0) != iProver_top ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_134854]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_134867,plain,
% 31.89/4.55      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2
% 31.89/4.55      | r1_tarski(sK2,X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_6534,c_134855]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_135318,plain,
% 31.89/4.55      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = sK2 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1425,c_134867]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_73712,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1)
% 31.89/4.55      | r1_tarski(X2,k2_zfmisc_1(sK2,sK1))
% 31.89/4.55      | X2 != X0
% 31.89/4.55      | k2_zfmisc_1(sK2,sK1) != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_77939,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
% 31.89/4.55      | r1_tarski(X1,k2_zfmisc_1(sK2,sK1))
% 31.89/4.55      | X1 != X0
% 31.89/4.55      | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_73712]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_92067,plain,
% 31.89/4.55      ( r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
% 31.89/4.55      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 31.89/4.55      | X0 != k2_partfun1(sK0,sK1,sK3,sK2)
% 31.89/4.55      | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_77939]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_115264,plain,
% 31.89/4.55      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 31.89/4.55      | r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 31.89/4.55      | k7_relat_1(sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 31.89/4.55      | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_92067]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_72397,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1)
% 31.89/4.55      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 31.89/4.55      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
% 31.89/4.55      | sK2 != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_73239,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,sK2)
% 31.89/4.55      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 31.89/4.55      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
% 31.89/4.55      | sK2 != sK2 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_72397]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_74978,plain,
% 31.89/4.55      ( ~ r1_tarski(k1_relat_1(X0),sK2)
% 31.89/4.55      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 31.89/4.55      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(X0)
% 31.89/4.55      | sK2 != sK2 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_73239]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_81217,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 31.89/4.55      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 31.89/4.55      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k7_relat_1(sK3,sK2))
% 31.89/4.55      | sK2 != sK2 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_74978]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_74979,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.89/4.55      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_824]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_78445,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 31.89/4.55      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_74979]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11948,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0)) = sK0
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1425,c_11901]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_12614,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) = sK0
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_3461,c_11948]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4715,plain,
% 31.89/4.55      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1416,c_1422]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_24088,plain,
% 31.89/4.55      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_5,c_4715]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1819,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_4,c_1408]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7049,plain,
% 31.89/4.55      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1425,c_4714]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_24087,plain,
% 31.89/4.55      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_4,c_4715]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_24128,plain,
% 31.89/4.55      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1425,c_24087]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_24581,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 31.89/4.55      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_24088,c_1819,c_7049,c_24128]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_24582,plain,
% 31.89/4.55      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(X0) != iProver_top ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_24581]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_24607,plain,
% 31.89/4.55      ( sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(k7_relat_1(k7_relat_1(sK3,sK0),sK0),k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_12614,c_24582]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2221,plain,
% 31.89/4.55      ( ~ r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2222,plain,
% 31.89/4.55      ( k1_xboole_0 = sK0 | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_2221]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1863,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_8]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3560,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1863]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3562,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 31.89/4.55      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3560]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1910,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1)
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0)
% 31.89/4.55      | sK3 != X0
% 31.89/4.55      | k1_xboole_0 != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2682,plain,
% 31.89/4.55      ( ~ r1_tarski(sK3,X0)
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0)
% 31.89/4.55      | sK3 != sK3
% 31.89/4.55      | k1_xboole_0 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1910]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4816,plain,
% 31.89/4.55      ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0)
% 31.89/4.55      | sK3 != sK3
% 31.89/4.55      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2682]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4822,plain,
% 31.89/4.55      ( ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0)
% 31.89/4.55      | sK3 != sK3
% 31.89/4.55      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_4816]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3269,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(X1)
% 31.89/4.55      | sK3 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1904]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3599,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X0)
% 31.89/4.55      | sK3 != sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3269]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7663,plain,
% 31.89/4.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 31.89/4.55      | sK3 != sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3599]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7665,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 31.89/4.55      | sK3 != sK3 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_7663]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11543,plain,
% 31.89/4.55      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_4159]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11544,plain,
% 31.89/4.55      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK0,sK1)
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_11543]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_28892,plain,
% 31.89/4.55      ( X0 != sK1
% 31.89/4.55      | X1 != sK0
% 31.89/4.55      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK0,sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_821]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_28893,plain,
% 31.89/4.55      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
% 31.89/4.55      | k1_xboole_0 != sK1
% 31.89/4.55      | k1_xboole_0 != sK0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_28892]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_31408,plain,
% 31.89/4.55      ( r1_tarski(k7_relat_1(k7_relat_1(sK3,sK0),sK0),k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) != iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_24607,c_33,c_31,c_30,c_98,c_100,c_101,c_106,c_534,
% 31.89/4.55                 c_1651,c_1679,c_1835,c_1918,c_1919,c_1924,c_1925,c_1995,
% 31.89/4.55                 c_1996,c_2073,c_2148,c_2206,c_2222,c_2891,c_3262,c_3562,
% 31.89/4.55                 c_3590,c_4822,c_6026,c_6507,c_6508,c_6672,c_7665,c_8103,
% 31.89/4.55                 c_10700,c_11544,c_14459,c_21317,c_22275,c_28723,c_28893,
% 31.89/4.55                 c_30918]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_31420,plain,
% 31.89/4.55      ( k7_relat_1(k7_relat_1(sK3,sK0),sK0) = k1_xboole_0
% 31.89/4.55      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK0)) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_31408,c_1424]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2022,plain,
% 31.89/4.55      ( sK3 = X0
% 31.89/4.55      | r1_tarski(X0,sK3) != iProver_top
% 31.89/4.55      | r1_tarski(sK3,X0) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2024,plain,
% 31.89/4.55      ( sK3 = k1_xboole_0
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 31.89/4.55      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2022]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3572,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_818]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5167,plain,
% 31.89/4.55      ( X0 != k7_relat_1(sK3,X1)
% 31.89/4.55      | sK3 != sK3
% 31.89/4.55      | r1_tarski(X0,sK3) = iProver_top
% 31.89/4.55      | r1_tarski(k7_relat_1(sK3,X1),sK3) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_5166]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_5169,plain,
% 31.89/4.55      ( sK3 != sK3
% 31.89/4.55      | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
% 31.89/4.55      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
% 31.89/4.55      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_5167]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6017,plain,
% 31.89/4.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | ~ v1_funct_1(sK3)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3588]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1702,plain,
% 31.89/4.55      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | ~ v1_funct_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_25]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2036,plain,
% 31.89/4.55      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | ~ v1_funct_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1702]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6787,plain,
% 31.89/4.55      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | ~ v1_funct_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2036]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7483,plain,
% 31.89/4.55      ( sK1 = k1_xboole_0
% 31.89/4.55      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.89/4.55      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_3461,c_7478]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_7489,plain,
% 31.89/4.55      ( sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_7483,c_1422]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3571,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0))
% 31.89/4.55      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3260]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_11547,plain,
% 31.89/4.55      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_3571]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4454,plain,
% 31.89/4.55      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_1412,c_4445]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_24592,plain,
% 31.89/4.55      ( sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 31.89/4.55      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_4454,c_24582]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_25485,plain,
% 31.89/4.55      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 31.89/4.55      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_24592,c_36,c_1652,c_12653,c_14613]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_25486,plain,
% 31.89/4.55      ( sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(renaming,[status(thm)],[c_25485]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_25497,plain,
% 31.89/4.55      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 31.89/4.55      | sK1 = k1_xboole_0
% 31.89/4.55      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(superposition,[status(thm)],[c_25486,c_1424]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_25539,plain,
% 31.89/4.55      ( ~ r1_tarski(sK2,k1_xboole_0)
% 31.89/4.55      | k7_relat_1(sK3,sK2) = k1_xboole_0
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(predicate_to_equality_rev,[status(thm)],[c_25497]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4024,plain,
% 31.89/4.55      ( X0 != X1
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X2) != X1
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X2) = X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_10587,plain,
% 31.89/4.55      ( X0 != k7_relat_1(sK3,X1)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X1) = X0
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_4024]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_12014,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,X0) = sK3
% 31.89/4.55      | sK3 != k7_relat_1(sK3,X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_10587]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_28902,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 31.89/4.55      | sK3 != k7_relat_1(sK3,sK2) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_12014]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2027,plain,
% 31.89/4.55      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_819]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_31108,plain,
% 31.89/4.55      ( k7_relat_1(sK3,sK2) != X0
% 31.89/4.55      | sK3 != X0
% 31.89/4.55      | sK3 = k7_relat_1(sK3,sK2) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2027]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_31110,plain,
% 31.89/4.55      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 31.89/4.55      | sK3 = k7_relat_1(sK3,sK2)
% 31.89/4.55      | sK3 != k1_xboole_0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_31108]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_31611,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK0,sK1)
% 31.89/4.55      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_11543]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_14551,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,X0)
% 31.89/4.55      | sK2 != sK0
% 31.89/4.55      | sK1 != X0 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6506]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_67436,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,sK1)
% 31.89/4.55      | sK2 != sK0
% 31.89/4.55      | sK1 != sK1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_14551]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_67942,plain,
% 31.89/4.55      ( r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(global_propositional_subsumption,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_31420,c_33,c_31,c_36,c_30,c_76,c_98,c_100,c_101,c_106,
% 31.89/4.55                 c_534,c_1648,c_1651,c_1652,c_1679,c_1729,c_1730,c_1835,
% 31.89/4.55                 c_1880,c_1907,c_1918,c_1919,c_1924,c_1925,c_1978,c_1995,
% 31.89/4.55                 c_1996,c_2023,c_2024,c_2137,c_2148,c_2206,c_2222,c_2225,
% 31.89/4.55                 c_2723,c_2733,c_2891,c_2924,c_3262,c_3461,c_3572,c_3590,
% 31.89/4.55                 c_5168,c_5169,c_5224,c_6017,c_6026,c_6507,c_6508,c_6517,
% 31.89/4.55                 c_6518,c_6672,c_6787,c_7479,c_7489,c_7854,c_8103,c_8667,
% 31.89/4.55                 c_8726,c_8722,c_8834,c_9904,c_10700,c_11537,c_11547,
% 31.89/4.55                 c_12527,c_14459,c_18924,c_21317,c_22275,c_25539,c_26667,
% 31.89/4.55                 c_28723,c_28902,c_30918,c_31110,c_31611,c_35481,c_67436]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6606,plain,
% 31.89/4.55      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(X0,X1)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1646]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_43097,plain,
% 31.89/4.55      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6606]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1782,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | r1_tarski(k2_relat_1(k2_partfun1(X0,X1,sK3,X2)),X1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_405]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2176,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,X0)),sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1782]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_40030,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2176]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6679,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 31.89/4.55      | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
% 31.89/4.55      | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6025]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_18487,plain,
% 31.89/4.55      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 31.89/4.55      | k7_relat_1(sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2)
% 31.89/4.55      | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6679]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6680,plain,
% 31.89/4.55      ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_818]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_15648,plain,
% 31.89/4.55      ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_6680]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6503,plain,
% 31.89/4.55      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,sK1) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_818]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_22,plain,
% 31.89/4.55      ( v1_funct_2(X0,X1,X2)
% 31.89/4.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | k1_relset_1(X1,X2,X0) != X1
% 31.89/4.55      | k1_xboole_0 = X2 ),
% 31.89/4.55      inference(cnf_transformation,[],[f70]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_507,plain,
% 31.89/4.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.89/4.55      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.89/4.55      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.89/4.55      | k1_relset_1(X1,X2,X0) != X1
% 31.89/4.55      | sK2 != X1
% 31.89/4.55      | sK1 != X2
% 31.89/4.55      | k1_xboole_0 = X2 ),
% 31.89/4.55      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_508,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.89/4.55      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 31.89/4.55      | k1_xboole_0 = sK1 ),
% 31.89/4.55      inference(unflattening,[status(thm)],[c_507]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1403,plain,
% 31.89/4.55      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 31.89/4.55      | k1_xboole_0 = sK1
% 31.89/4.55      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.89/4.55      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6272,plain,
% 31.89/4.55      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 31.89/4.55      | sK1 = k1_xboole_0
% 31.89/4.55      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.89/4.55      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.89/4.55      inference(demodulation,[status(thm)],[c_6265,c_1403]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6280,plain,
% 31.89/4.55      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 31.89/4.55      | sK1 = k1_xboole_0
% 31.89/4.55      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 31.89/4.55      inference(forward_subsumption_resolution,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_6272,c_6273]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_6398,plain,
% 31.89/4.55      ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 31.89/4.55      | sK1 = k1_xboole_0 ),
% 31.89/4.55      inference(predicate_to_equality_rev,[status(thm)],[c_6280]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_4675,plain,
% 31.89/4.55      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 31.89/4.55      | ~ v1_relat_1(sK3) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1723]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3525,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1863]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1783,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.89/4.55      | v1_relat_1(k2_partfun1(X0,X1,sK3,X2)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_15]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2177,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1783]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_3521,plain,
% 31.89/4.55      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.89/4.55      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_2177]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_2627,plain,
% 31.89/4.55      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.89/4.55      | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 31.89/4.55      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 31.89/4.55      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_18]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1826,plain,
% 31.89/4.55      ( ~ r1_tarski(X0,X1)
% 31.89/4.55      | r1_tarski(sK0,k1_xboole_0)
% 31.89/4.55      | sK0 != X0
% 31.89/4.55      | k1_xboole_0 != X1 ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_820]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1827,plain,
% 31.89/4.55      ( sK0 != X0
% 31.89/4.55      | k1_xboole_0 != X1
% 31.89/4.55      | r1_tarski(X0,X1) != iProver_top
% 31.89/4.55      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 31.89/4.55      inference(predicate_to_equality,[status(thm)],[c_1826]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(c_1829,plain,
% 31.89/4.55      ( sK0 != k1_xboole_0
% 31.89/4.55      | k1_xboole_0 != k1_xboole_0
% 31.89/4.55      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 31.89/4.55      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.89/4.55      inference(instantiation,[status(thm)],[c_1827]) ).
% 31.89/4.55  
% 31.89/4.55  cnf(contradiction,plain,
% 31.89/4.55      ( $false ),
% 31.89/4.55      inference(minisat,
% 31.89/4.55                [status(thm)],
% 31.89/4.55                [c_135318,c_115264,c_81217,c_78445,c_67942,c_43097,
% 31.89/4.55                 c_40030,c_18487,c_15648,c_6787,c_6503,c_6398,c_6017,
% 31.89/4.55                 c_4675,c_3525,c_3521,c_2627,c_2137,c_1919,c_1829,c_1651,
% 31.89/4.55                 c_107,c_101,c_100,c_31,c_33]) ).
% 31.89/4.55  
% 31.89/4.55  
% 31.89/4.55  % SZS output end CNFRefutation for theBenchmark.p
% 31.89/4.55  
% 31.89/4.55  ------                               Statistics
% 31.89/4.55  
% 31.89/4.55  ------ General
% 31.89/4.55  
% 31.89/4.55  abstr_ref_over_cycles:                  0
% 31.89/4.55  abstr_ref_under_cycles:                 0
% 31.89/4.55  gc_basic_clause_elim:                   0
% 31.89/4.55  forced_gc_time:                         0
% 31.89/4.55  parsing_time:                           0.009
% 31.89/4.55  unif_index_cands_time:                  0.
% 31.89/4.55  unif_index_add_time:                    0.
% 31.89/4.55  orderings_time:                         0.
% 31.89/4.55  out_proof_time:                         0.047
% 31.89/4.55  total_time:                             3.763
% 31.89/4.55  num_of_symbols:                         49
% 31.89/4.55  num_of_terms:                           134303
% 31.89/4.55  
% 31.89/4.55  ------ Preprocessing
% 31.89/4.55  
% 31.89/4.55  num_of_splits:                          0
% 31.89/4.55  num_of_split_atoms:                     0
% 31.89/4.55  num_of_reused_defs:                     0
% 31.89/4.55  num_eq_ax_congr_red:                    16
% 31.89/4.55  num_of_sem_filtered_clauses:            1
% 31.89/4.55  num_of_subtypes:                        0
% 31.89/4.55  monotx_restored_types:                  0
% 31.89/4.55  sat_num_of_epr_types:                   0
% 31.89/4.55  sat_num_of_non_cyclic_types:            0
% 31.89/4.55  sat_guarded_non_collapsed_types:        0
% 31.89/4.55  num_pure_diseq_elim:                    0
% 31.89/4.55  simp_replaced_by:                       0
% 31.89/4.55  res_preprocessed:                       144
% 31.89/4.55  prep_upred:                             0
% 31.89/4.55  prep_unflattend:                        33
% 31.89/4.55  smt_new_axioms:                         0
% 31.89/4.55  pred_elim_cands:                        4
% 31.89/4.55  pred_elim:                              2
% 31.89/4.55  pred_elim_cl:                           3
% 31.89/4.55  pred_elim_cycles:                       4
% 31.89/4.55  merged_defs:                            8
% 31.89/4.55  merged_defs_ncl:                        0
% 31.89/4.55  bin_hyper_res:                          9
% 31.89/4.55  prep_cycles:                            4
% 31.89/4.55  pred_elim_time:                         0.006
% 31.89/4.55  splitting_time:                         0.
% 31.89/4.55  sem_filter_time:                        0.
% 31.89/4.55  monotx_time:                            0.
% 31.89/4.55  subtype_inf_time:                       0.
% 31.89/4.55  
% 31.89/4.55  ------ Problem properties
% 31.89/4.55  
% 31.89/4.55  clauses:                                30
% 31.89/4.55  conjectures:                            4
% 31.89/4.55  epr:                                    7
% 31.89/4.55  horn:                                   27
% 31.89/4.55  ground:                                 11
% 31.89/4.55  unary:                                  6
% 31.89/4.55  binary:                                 10
% 31.89/4.55  lits:                                   77
% 31.89/4.55  lits_eq:                                28
% 31.89/4.55  fd_pure:                                0
% 31.89/4.55  fd_pseudo:                              0
% 31.89/4.55  fd_cond:                                2
% 31.89/4.55  fd_pseudo_cond:                         1
% 31.89/4.55  ac_symbols:                             0
% 31.89/4.55  
% 31.89/4.55  ------ Propositional Solver
% 31.89/4.55  
% 31.89/4.55  prop_solver_calls:                      49
% 31.89/4.55  prop_fast_solver_calls:                 3913
% 31.89/4.55  smt_solver_calls:                       0
% 31.89/4.55  smt_fast_solver_calls:                  0
% 31.89/4.55  prop_num_of_clauses:                    48898
% 31.89/4.55  prop_preprocess_simplified:             78150
% 31.89/4.55  prop_fo_subsumed:                       165
% 31.89/4.55  prop_solver_time:                       0.
% 31.89/4.55  smt_solver_time:                        0.
% 31.89/4.55  smt_fast_solver_time:                   0.
% 31.89/4.55  prop_fast_solver_time:                  0.
% 31.89/4.55  prop_unsat_core_time:                   0.005
% 31.89/4.55  
% 31.89/4.55  ------ QBF
% 31.89/4.55  
% 31.89/4.55  qbf_q_res:                              0
% 31.89/4.55  qbf_num_tautologies:                    0
% 31.89/4.55  qbf_prep_cycles:                        0
% 31.89/4.55  
% 31.89/4.55  ------ BMC1
% 31.89/4.55  
% 31.89/4.55  bmc1_current_bound:                     -1
% 31.89/4.55  bmc1_last_solved_bound:                 -1
% 31.89/4.55  bmc1_unsat_core_size:                   -1
% 31.89/4.55  bmc1_unsat_core_parents_size:           -1
% 31.89/4.55  bmc1_merge_next_fun:                    0
% 31.89/4.55  bmc1_unsat_core_clauses_time:           0.
% 31.89/4.55  
% 31.89/4.55  ------ Instantiation
% 31.89/4.55  
% 31.89/4.55  inst_num_of_clauses:                    6176
% 31.89/4.55  inst_num_in_passive:                    3512
% 31.89/4.55  inst_num_in_active:                     4001
% 31.89/4.55  inst_num_in_unprocessed:                518
% 31.89/4.55  inst_num_of_loops:                      5229
% 31.89/4.55  inst_num_of_learning_restarts:          1
% 31.89/4.55  inst_num_moves_active_passive:          1221
% 31.89/4.55  inst_lit_activity:                      0
% 31.89/4.55  inst_lit_activity_moves:                0
% 31.89/4.55  inst_num_tautologies:                   0
% 31.89/4.55  inst_num_prop_implied:                  0
% 31.89/4.55  inst_num_existing_simplified:           0
% 31.89/4.55  inst_num_eq_res_simplified:             0
% 31.89/4.55  inst_num_child_elim:                    0
% 31.89/4.55  inst_num_of_dismatching_blockings:      6266
% 31.89/4.55  inst_num_of_non_proper_insts:           13917
% 31.89/4.55  inst_num_of_duplicates:                 0
% 31.89/4.55  inst_inst_num_from_inst_to_res:         0
% 31.89/4.55  inst_dismatching_checking_time:         0.
% 31.89/4.55  
% 31.89/4.55  ------ Resolution
% 31.89/4.55  
% 31.89/4.55  res_num_of_clauses:                     40
% 31.89/4.55  res_num_in_passive:                     40
% 31.89/4.55  res_num_in_active:                      0
% 31.89/4.55  res_num_of_loops:                       148
% 31.89/4.55  res_forward_subset_subsumed:            519
% 31.89/4.55  res_backward_subset_subsumed:           8
% 31.89/4.55  res_forward_subsumed:                   0
% 31.89/4.55  res_backward_subsumed:                  0
% 31.89/4.55  res_forward_subsumption_resolution:     0
% 31.89/4.55  res_backward_subsumption_resolution:    0
% 31.89/4.55  res_clause_to_clause_subsumption:       26493
% 31.89/4.55  res_orphan_elimination:                 0
% 31.89/4.55  res_tautology_del:                      742
% 31.89/4.55  res_num_eq_res_simplified:              1
% 31.89/4.55  res_num_sel_changes:                    0
% 31.89/4.55  res_moves_from_active_to_pass:          0
% 31.89/4.55  
% 31.89/4.55  ------ Superposition
% 31.89/4.55  
% 31.89/4.55  sup_time_total:                         0.
% 31.89/4.55  sup_time_generating:                    0.
% 31.89/4.55  sup_time_sim_full:                      0.
% 31.89/4.55  sup_time_sim_immed:                     0.
% 31.89/4.55  
% 31.89/4.55  sup_num_of_clauses:                     5503
% 31.89/4.55  sup_num_in_active:                      890
% 31.89/4.55  sup_num_in_passive:                     4613
% 31.89/4.55  sup_num_of_loops:                       1044
% 31.89/4.55  sup_fw_superposition:                   6225
% 31.89/4.55  sup_bw_superposition:                   2659
% 31.89/4.55  sup_immediate_simplified:               2427
% 31.89/4.55  sup_given_eliminated:                   6
% 31.89/4.55  comparisons_done:                       0
% 31.89/4.55  comparisons_avoided:                    276
% 31.89/4.55  
% 31.89/4.55  ------ Simplifications
% 31.89/4.55  
% 31.89/4.55  
% 31.89/4.55  sim_fw_subset_subsumed:                 443
% 31.89/4.55  sim_bw_subset_subsumed:                 74
% 31.89/4.55  sim_fw_subsumed:                        466
% 31.89/4.55  sim_bw_subsumed:                        138
% 31.89/4.55  sim_fw_subsumption_res:                 90
% 31.89/4.55  sim_bw_subsumption_res:                 10
% 31.89/4.55  sim_tautology_del:                      126
% 31.89/4.55  sim_eq_tautology_del:                   344
% 31.89/4.55  sim_eq_res_simp:                        0
% 31.89/4.55  sim_fw_demodulated:                     711
% 31.89/4.55  sim_bw_demodulated:                     150
% 31.89/4.55  sim_light_normalised:                   1010
% 31.89/4.55  sim_joinable_taut:                      0
% 31.89/4.55  sim_joinable_simp:                      0
% 31.89/4.55  sim_ac_normalised:                      0
% 31.89/4.55  sim_smt_subsumption:                    0
% 31.89/4.55  
%------------------------------------------------------------------------------
