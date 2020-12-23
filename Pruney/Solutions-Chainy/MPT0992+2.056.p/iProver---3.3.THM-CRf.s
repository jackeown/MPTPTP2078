%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:57 EST 2020

% Result     : Theorem 11.83s
% Output     : CNFRefutation 11.83s
% Verified   : 
% Statistics : Number of formulae       :  311 (3623 expanded)
%              Number of clauses        :  211 (1463 expanded)
%              Number of leaves         :   27 ( 639 expanded)
%              Depth                    :   29
%              Number of atoms          :  953 (16461 expanded)
%              Number of equality atoms :  546 (5037 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
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

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f65,plain,
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

fof(f66,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f65])).

fof(f110,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f22,axiom,(
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

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f108,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f109,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f107,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f112,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f66])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f102])).

fof(f118,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f117])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f59])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f116,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f119,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f101])).

fof(f111,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f66])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_42,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2100,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2122,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_27,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_27,c_14])).

cnf(c_2096,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_3830,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2119,c_2096])).

cnf(c_14471,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_3830])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_118,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18741,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14471,c_118])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2121,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18750,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(k2_zfmisc_1(X2,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_18741,c_2121])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_44])).

cnf(c_795,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_797,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_43])).

cnf(c_2099,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2103,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3843,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2099,c_2103])).

cnf(c_4080,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_797,c_3843])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2108,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5835,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4080,c_2108])).

cnf(c_2114,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3223,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2099,c_2118])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_336,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_337,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_336])).

cnf(c_409,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_337])).

cnf(c_2097,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_4431,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3223,c_2097])).

cnf(c_5297,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2114,c_4431])).

cnf(c_7446,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5835,c_5297])).

cnf(c_7447,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7446])).

cnf(c_18817,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(k2_zfmisc_1(X0,X1))
    | sK1 = k1_xboole_0
    | r1_tarski(X1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18750,c_7447])).

cnf(c_29294,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,sK2)))) = k2_relat_1(k2_zfmisc_1(X0,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2100,c_18817])).

cnf(c_21,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2109,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4428,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) != iProver_top
    | v1_relat_1(k1_relat_1(k7_relat_1(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2109,c_2097])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2113,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5994,plain,
    ( k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2113])).

cnf(c_50370,plain,
    ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(X0,X1)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(X0,X1)),sK2)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4428,c_5994])).

cnf(c_51061,plain,
    ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,sK2))),X1)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,sK2))),X1)),sK2)
    | sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,sK2)))) != iProver_top
    | v1_relat_1(k2_relat_1(k2_zfmisc_1(X0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29294,c_50370])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2115,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7454,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2100,c_7447])).

cnf(c_51055,plain,
    ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)),sK2)
    | sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7454,c_50370])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3831,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2099,c_2096])).

cnf(c_25,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2830,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_27735,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2830])).

cnf(c_27736,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27735])).

cnf(c_24,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2106,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5765,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(X0,X2)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2106,c_2121])).

cnf(c_37,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2101,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7657,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7454,c_2101])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2102,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6916,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2099,c_2102])).

cnf(c_7218,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6916,c_46])).

cnf(c_38,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_40,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_805,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_40])).

cnf(c_806,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_818,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_806,c_542])).

cnf(c_2087,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_7223,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7218,c_2087])).

cnf(c_7664,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7454,c_7223])).

cnf(c_9621,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7657,c_7664])).

cnf(c_42848,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5765,c_9621])).

cnf(c_51298,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_51055,c_46,c_3831,c_5297,c_27736,c_42848])).

cnf(c_51299,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_51298])).

cnf(c_51302,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2115,c_51299])).

cnf(c_51389,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_51061,c_5297,c_51302])).

cnf(c_30,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_621,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_40])).

cnf(c_622,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_2095,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2127,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2095,c_5])).

cnf(c_140,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_142,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_149,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_151,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_2748,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2127,c_142,c_151])).

cnf(c_2749,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2748])).

cnf(c_7222,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7218,c_2749])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_143,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_144,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_150,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1283,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2236,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_2238,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_1282,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2186,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_2249,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_2216,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2310,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_1281,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2377,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2784,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_44])).

cnf(c_674,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_2093,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_2125,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2093,c_5])).

cnf(c_41,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2190,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_2254,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2380,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_2767,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_2768,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_2826,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2125,c_41,c_143,c_144,c_2254,c_2380,c_2768])).

cnf(c_2827,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2826])).

cnf(c_7439,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7222,c_42,c_143,c_144,c_150,c_2238,c_2249,c_2310,c_2377,c_2784,c_2827])).

cnf(c_51607,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51389,c_7439])).

cnf(c_51647,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_51607])).

cnf(c_824,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_44])).

cnf(c_938,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_824])).

cnf(c_2086,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_825,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_824])).

cnf(c_1291,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2192,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_2287,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_2288,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2287])).

cnf(c_2357,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_2502,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != sK0
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2086,c_46,c_825,c_2288,c_2357])).

cnf(c_2503,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2502])).

cnf(c_7224,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7218,c_2503])).

cnf(c_51609,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_51389,c_7224])).

cnf(c_51626,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51389,c_41])).

cnf(c_51627,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_51626])).

cnf(c_51645,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_51609,c_51627])).

cnf(c_51646,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_51645,c_5])).

cnf(c_51648,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_51647,c_51646])).

cnf(c_51650,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_51648])).

cnf(c_19,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2111,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2120,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3414,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2111,c_2120])).

cnf(c_5599,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5297,c_3414])).

cnf(c_30767,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5599,c_2101])).

cnf(c_30784,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30767,c_6])).

cnf(c_2831,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2830])).

cnf(c_2833,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2831])).

cnf(c_31198,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30784,c_46,c_2833,c_5297])).

cnf(c_31199,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_31198])).

cnf(c_31204,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_31199])).

cnf(c_31209,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31204,c_2118])).

cnf(c_36567,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31209,c_2120])).

cnf(c_36587,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2115,c_36567])).

cnf(c_36626,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36587,c_5297])).

cnf(c_51651,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_51650,c_36626])).

cnf(c_5769,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3831,c_2121])).

cnf(c_6424,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5769,c_5297])).

cnf(c_6425,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6424])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_38])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_664,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_648,c_37])).

cnf(c_2094,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_6439,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6425,c_2094])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2682,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2683,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2682])).

cnf(c_2685,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2683])).

cnf(c_20,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3611,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3612,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3611])).

cnf(c_3614,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3612])).

cnf(c_2714,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK3)
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3704,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK3,X1))
    | r1_tarski(X0,sK3)
    | ~ r1_tarski(k7_relat_1(sK3,X1),sK3) ),
    inference(instantiation,[status(thm)],[c_2714])).

cnf(c_3705,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3704])).

cnf(c_3707,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
    | r1_tarski(k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3705])).

cnf(c_5734,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4080,c_2101])).

cnf(c_9509,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5734,c_46,c_5297])).

cnf(c_9515,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_9509])).

cnf(c_2208,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_2209,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_2211,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_5732,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2101])).

cnf(c_7080,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6425,c_5732])).

cnf(c_9796,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9515,c_46,c_143,c_144,c_151,c_2211,c_5297,c_7080])).

cnf(c_9800,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6425,c_9796])).

cnf(c_10190,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9800,c_2118])).

cnf(c_26113,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k7_relat_1(sK3,X3))
    | X2 != X0
    | k7_relat_1(sK3,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_26114,plain,
    ( X0 != X1
    | k7_relat_1(sK3,X2) != X3
    | r1_tarski(X1,X3) != iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26113])).

cnf(c_26116,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_26114])).

cnf(c_47930,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6439,c_143,c_144,c_151,c_2685,c_3614,c_3707,c_5297,c_10190,c_26116,c_36587])).

cnf(c_47932,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_47930])).

cnf(c_2210,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2208])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51651,c_51302,c_47932,c_5297,c_2210,c_151,c_150,c_144,c_143,c_142])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:37:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.83/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.83/2.00  
% 11.83/2.00  ------  iProver source info
% 11.83/2.00  
% 11.83/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.83/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.83/2.00  git: non_committed_changes: false
% 11.83/2.00  git: last_make_outside_of_git: false
% 11.83/2.00  
% 11.83/2.00  ------ 
% 11.83/2.00  
% 11.83/2.00  ------ Input Options
% 11.83/2.00  
% 11.83/2.00  --out_options                           all
% 11.83/2.00  --tptp_safe_out                         true
% 11.83/2.00  --problem_path                          ""
% 11.83/2.00  --include_path                          ""
% 11.83/2.00  --clausifier                            res/vclausify_rel
% 11.83/2.00  --clausifier_options                    ""
% 11.83/2.00  --stdin                                 false
% 11.83/2.00  --stats_out                             all
% 11.83/2.00  
% 11.83/2.00  ------ General Options
% 11.83/2.00  
% 11.83/2.00  --fof                                   false
% 11.83/2.00  --time_out_real                         305.
% 11.83/2.00  --time_out_virtual                      -1.
% 11.83/2.00  --symbol_type_check                     false
% 11.83/2.00  --clausify_out                          false
% 11.83/2.00  --sig_cnt_out                           false
% 11.83/2.00  --trig_cnt_out                          false
% 11.83/2.00  --trig_cnt_out_tolerance                1.
% 11.83/2.00  --trig_cnt_out_sk_spl                   false
% 11.83/2.00  --abstr_cl_out                          false
% 11.83/2.00  
% 11.83/2.00  ------ Global Options
% 11.83/2.00  
% 11.83/2.00  --schedule                              default
% 11.83/2.00  --add_important_lit                     false
% 11.83/2.00  --prop_solver_per_cl                    1000
% 11.83/2.00  --min_unsat_core                        false
% 11.83/2.00  --soft_assumptions                      false
% 11.83/2.00  --soft_lemma_size                       3
% 11.83/2.00  --prop_impl_unit_size                   0
% 11.83/2.00  --prop_impl_unit                        []
% 11.83/2.00  --share_sel_clauses                     true
% 11.83/2.00  --reset_solvers                         false
% 11.83/2.00  --bc_imp_inh                            [conj_cone]
% 11.83/2.00  --conj_cone_tolerance                   3.
% 11.83/2.00  --extra_neg_conj                        none
% 11.83/2.00  --large_theory_mode                     true
% 11.83/2.00  --prolific_symb_bound                   200
% 11.83/2.00  --lt_threshold                          2000
% 11.83/2.00  --clause_weak_htbl                      true
% 11.83/2.00  --gc_record_bc_elim                     false
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing Options
% 11.83/2.00  
% 11.83/2.00  --preprocessing_flag                    true
% 11.83/2.00  --time_out_prep_mult                    0.1
% 11.83/2.00  --splitting_mode                        input
% 11.83/2.00  --splitting_grd                         true
% 11.83/2.00  --splitting_cvd                         false
% 11.83/2.00  --splitting_cvd_svl                     false
% 11.83/2.00  --splitting_nvd                         32
% 11.83/2.00  --sub_typing                            true
% 11.83/2.00  --prep_gs_sim                           true
% 11.83/2.00  --prep_unflatten                        true
% 11.83/2.00  --prep_res_sim                          true
% 11.83/2.00  --prep_upred                            true
% 11.83/2.00  --prep_sem_filter                       exhaustive
% 11.83/2.00  --prep_sem_filter_out                   false
% 11.83/2.00  --pred_elim                             true
% 11.83/2.00  --res_sim_input                         true
% 11.83/2.00  --eq_ax_congr_red                       true
% 11.83/2.00  --pure_diseq_elim                       true
% 11.83/2.00  --brand_transform                       false
% 11.83/2.00  --non_eq_to_eq                          false
% 11.83/2.00  --prep_def_merge                        true
% 11.83/2.00  --prep_def_merge_prop_impl              false
% 11.83/2.00  --prep_def_merge_mbd                    true
% 11.83/2.00  --prep_def_merge_tr_red                 false
% 11.83/2.00  --prep_def_merge_tr_cl                  false
% 11.83/2.00  --smt_preprocessing                     true
% 11.83/2.00  --smt_ac_axioms                         fast
% 11.83/2.00  --preprocessed_out                      false
% 11.83/2.00  --preprocessed_stats                    false
% 11.83/2.00  
% 11.83/2.00  ------ Abstraction refinement Options
% 11.83/2.00  
% 11.83/2.00  --abstr_ref                             []
% 11.83/2.00  --abstr_ref_prep                        false
% 11.83/2.00  --abstr_ref_until_sat                   false
% 11.83/2.00  --abstr_ref_sig_restrict                funpre
% 11.83/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.83/2.00  --abstr_ref_under                       []
% 11.83/2.00  
% 11.83/2.00  ------ SAT Options
% 11.83/2.00  
% 11.83/2.00  --sat_mode                              false
% 11.83/2.00  --sat_fm_restart_options                ""
% 11.83/2.00  --sat_gr_def                            false
% 11.83/2.00  --sat_epr_types                         true
% 11.83/2.00  --sat_non_cyclic_types                  false
% 11.83/2.00  --sat_finite_models                     false
% 11.83/2.00  --sat_fm_lemmas                         false
% 11.83/2.00  --sat_fm_prep                           false
% 11.83/2.00  --sat_fm_uc_incr                        true
% 11.83/2.00  --sat_out_model                         small
% 11.83/2.00  --sat_out_clauses                       false
% 11.83/2.00  
% 11.83/2.00  ------ QBF Options
% 11.83/2.00  
% 11.83/2.00  --qbf_mode                              false
% 11.83/2.00  --qbf_elim_univ                         false
% 11.83/2.00  --qbf_dom_inst                          none
% 11.83/2.00  --qbf_dom_pre_inst                      false
% 11.83/2.00  --qbf_sk_in                             false
% 11.83/2.00  --qbf_pred_elim                         true
% 11.83/2.00  --qbf_split                             512
% 11.83/2.00  
% 11.83/2.00  ------ BMC1 Options
% 11.83/2.00  
% 11.83/2.00  --bmc1_incremental                      false
% 11.83/2.00  --bmc1_axioms                           reachable_all
% 11.83/2.00  --bmc1_min_bound                        0
% 11.83/2.00  --bmc1_max_bound                        -1
% 11.83/2.00  --bmc1_max_bound_default                -1
% 11.83/2.00  --bmc1_symbol_reachability              true
% 11.83/2.00  --bmc1_property_lemmas                  false
% 11.83/2.00  --bmc1_k_induction                      false
% 11.83/2.00  --bmc1_non_equiv_states                 false
% 11.83/2.00  --bmc1_deadlock                         false
% 11.83/2.00  --bmc1_ucm                              false
% 11.83/2.00  --bmc1_add_unsat_core                   none
% 11.83/2.00  --bmc1_unsat_core_children              false
% 11.83/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.83/2.00  --bmc1_out_stat                         full
% 11.83/2.00  --bmc1_ground_init                      false
% 11.83/2.00  --bmc1_pre_inst_next_state              false
% 11.83/2.00  --bmc1_pre_inst_state                   false
% 11.83/2.00  --bmc1_pre_inst_reach_state             false
% 11.83/2.00  --bmc1_out_unsat_core                   false
% 11.83/2.00  --bmc1_aig_witness_out                  false
% 11.83/2.00  --bmc1_verbose                          false
% 11.83/2.00  --bmc1_dump_clauses_tptp                false
% 11.83/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.83/2.00  --bmc1_dump_file                        -
% 11.83/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.83/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.83/2.00  --bmc1_ucm_extend_mode                  1
% 11.83/2.00  --bmc1_ucm_init_mode                    2
% 11.83/2.00  --bmc1_ucm_cone_mode                    none
% 11.83/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.83/2.00  --bmc1_ucm_relax_model                  4
% 11.83/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.83/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.83/2.00  --bmc1_ucm_layered_model                none
% 11.83/2.00  --bmc1_ucm_max_lemma_size               10
% 11.83/2.00  
% 11.83/2.00  ------ AIG Options
% 11.83/2.00  
% 11.83/2.00  --aig_mode                              false
% 11.83/2.00  
% 11.83/2.00  ------ Instantiation Options
% 11.83/2.00  
% 11.83/2.00  --instantiation_flag                    true
% 11.83/2.00  --inst_sos_flag                         true
% 11.83/2.00  --inst_sos_phase                        true
% 11.83/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel_side                     num_symb
% 11.83/2.00  --inst_solver_per_active                1400
% 11.83/2.00  --inst_solver_calls_frac                1.
% 11.83/2.00  --inst_passive_queue_type               priority_queues
% 11.83/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.83/2.00  --inst_passive_queues_freq              [25;2]
% 11.83/2.00  --inst_dismatching                      true
% 11.83/2.00  --inst_eager_unprocessed_to_passive     true
% 11.83/2.00  --inst_prop_sim_given                   true
% 11.83/2.00  --inst_prop_sim_new                     false
% 11.83/2.00  --inst_subs_new                         false
% 11.83/2.00  --inst_eq_res_simp                      false
% 11.83/2.00  --inst_subs_given                       false
% 11.83/2.00  --inst_orphan_elimination               true
% 11.83/2.00  --inst_learning_loop_flag               true
% 11.83/2.00  --inst_learning_start                   3000
% 11.83/2.00  --inst_learning_factor                  2
% 11.83/2.00  --inst_start_prop_sim_after_learn       3
% 11.83/2.00  --inst_sel_renew                        solver
% 11.83/2.00  --inst_lit_activity_flag                true
% 11.83/2.00  --inst_restr_to_given                   false
% 11.83/2.00  --inst_activity_threshold               500
% 11.83/2.00  --inst_out_proof                        true
% 11.83/2.00  
% 11.83/2.00  ------ Resolution Options
% 11.83/2.00  
% 11.83/2.00  --resolution_flag                       true
% 11.83/2.00  --res_lit_sel                           adaptive
% 11.83/2.00  --res_lit_sel_side                      none
% 11.83/2.00  --res_ordering                          kbo
% 11.83/2.00  --res_to_prop_solver                    active
% 11.83/2.00  --res_prop_simpl_new                    false
% 11.83/2.00  --res_prop_simpl_given                  true
% 11.83/2.00  --res_passive_queue_type                priority_queues
% 11.83/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.83/2.00  --res_passive_queues_freq               [15;5]
% 11.83/2.00  --res_forward_subs                      full
% 11.83/2.00  --res_backward_subs                     full
% 11.83/2.00  --res_forward_subs_resolution           true
% 11.83/2.00  --res_backward_subs_resolution          true
% 11.83/2.00  --res_orphan_elimination                true
% 11.83/2.00  --res_time_limit                        2.
% 11.83/2.00  --res_out_proof                         true
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Options
% 11.83/2.00  
% 11.83/2.00  --superposition_flag                    true
% 11.83/2.00  --sup_passive_queue_type                priority_queues
% 11.83/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.83/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.83/2.00  --demod_completeness_check              fast
% 11.83/2.00  --demod_use_ground                      true
% 11.83/2.00  --sup_to_prop_solver                    passive
% 11.83/2.00  --sup_prop_simpl_new                    true
% 11.83/2.00  --sup_prop_simpl_given                  true
% 11.83/2.00  --sup_fun_splitting                     true
% 11.83/2.00  --sup_smt_interval                      50000
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Simplification Setup
% 11.83/2.00  
% 11.83/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.83/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.83/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.83/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.83/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.83/2.00  --sup_immed_triv                        [TrivRules]
% 11.83/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_bw_main                     []
% 11.83/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.83/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.83/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_input_bw                          []
% 11.83/2.00  
% 11.83/2.00  ------ Combination Options
% 11.83/2.00  
% 11.83/2.00  --comb_res_mult                         3
% 11.83/2.00  --comb_sup_mult                         2
% 11.83/2.00  --comb_inst_mult                        10
% 11.83/2.00  
% 11.83/2.00  ------ Debug Options
% 11.83/2.00  
% 11.83/2.00  --dbg_backtrace                         false
% 11.83/2.00  --dbg_dump_prop_clauses                 false
% 11.83/2.00  --dbg_dump_prop_clauses_file            -
% 11.83/2.00  --dbg_out_stat                          false
% 11.83/2.00  ------ Parsing...
% 11.83/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.83/2.00  ------ Proving...
% 11.83/2.00  ------ Problem Properties 
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  clauses                                 43
% 11.83/2.00  conjectures                             4
% 11.83/2.00  EPR                                     8
% 11.83/2.00  Horn                                    38
% 11.83/2.00  unary                                   7
% 11.83/2.00  binary                                  13
% 11.83/2.00  lits                                    118
% 11.83/2.00  lits eq                                 38
% 11.83/2.00  fd_pure                                 0
% 11.83/2.00  fd_pseudo                               0
% 11.83/2.00  fd_cond                                 4
% 11.83/2.00  fd_pseudo_cond                          1
% 11.83/2.00  AC symbols                              0
% 11.83/2.00  
% 11.83/2.00  ------ Schedule dynamic 5 is on 
% 11.83/2.00  
% 11.83/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  ------ 
% 11.83/2.00  Current options:
% 11.83/2.00  ------ 
% 11.83/2.00  
% 11.83/2.00  ------ Input Options
% 11.83/2.00  
% 11.83/2.00  --out_options                           all
% 11.83/2.00  --tptp_safe_out                         true
% 11.83/2.00  --problem_path                          ""
% 11.83/2.00  --include_path                          ""
% 11.83/2.00  --clausifier                            res/vclausify_rel
% 11.83/2.00  --clausifier_options                    ""
% 11.83/2.00  --stdin                                 false
% 11.83/2.00  --stats_out                             all
% 11.83/2.00  
% 11.83/2.00  ------ General Options
% 11.83/2.00  
% 11.83/2.00  --fof                                   false
% 11.83/2.00  --time_out_real                         305.
% 11.83/2.00  --time_out_virtual                      -1.
% 11.83/2.00  --symbol_type_check                     false
% 11.83/2.00  --clausify_out                          false
% 11.83/2.00  --sig_cnt_out                           false
% 11.83/2.00  --trig_cnt_out                          false
% 11.83/2.00  --trig_cnt_out_tolerance                1.
% 11.83/2.00  --trig_cnt_out_sk_spl                   false
% 11.83/2.00  --abstr_cl_out                          false
% 11.83/2.00  
% 11.83/2.00  ------ Global Options
% 11.83/2.00  
% 11.83/2.00  --schedule                              default
% 11.83/2.00  --add_important_lit                     false
% 11.83/2.00  --prop_solver_per_cl                    1000
% 11.83/2.00  --min_unsat_core                        false
% 11.83/2.00  --soft_assumptions                      false
% 11.83/2.00  --soft_lemma_size                       3
% 11.83/2.00  --prop_impl_unit_size                   0
% 11.83/2.00  --prop_impl_unit                        []
% 11.83/2.00  --share_sel_clauses                     true
% 11.83/2.00  --reset_solvers                         false
% 11.83/2.00  --bc_imp_inh                            [conj_cone]
% 11.83/2.00  --conj_cone_tolerance                   3.
% 11.83/2.00  --extra_neg_conj                        none
% 11.83/2.00  --large_theory_mode                     true
% 11.83/2.00  --prolific_symb_bound                   200
% 11.83/2.00  --lt_threshold                          2000
% 11.83/2.00  --clause_weak_htbl                      true
% 11.83/2.00  --gc_record_bc_elim                     false
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing Options
% 11.83/2.00  
% 11.83/2.00  --preprocessing_flag                    true
% 11.83/2.00  --time_out_prep_mult                    0.1
% 11.83/2.00  --splitting_mode                        input
% 11.83/2.00  --splitting_grd                         true
% 11.83/2.00  --splitting_cvd                         false
% 11.83/2.00  --splitting_cvd_svl                     false
% 11.83/2.00  --splitting_nvd                         32
% 11.83/2.00  --sub_typing                            true
% 11.83/2.00  --prep_gs_sim                           true
% 11.83/2.00  --prep_unflatten                        true
% 11.83/2.00  --prep_res_sim                          true
% 11.83/2.00  --prep_upred                            true
% 11.83/2.00  --prep_sem_filter                       exhaustive
% 11.83/2.00  --prep_sem_filter_out                   false
% 11.83/2.00  --pred_elim                             true
% 11.83/2.00  --res_sim_input                         true
% 11.83/2.00  --eq_ax_congr_red                       true
% 11.83/2.00  --pure_diseq_elim                       true
% 11.83/2.00  --brand_transform                       false
% 11.83/2.00  --non_eq_to_eq                          false
% 11.83/2.00  --prep_def_merge                        true
% 11.83/2.00  --prep_def_merge_prop_impl              false
% 11.83/2.00  --prep_def_merge_mbd                    true
% 11.83/2.00  --prep_def_merge_tr_red                 false
% 11.83/2.00  --prep_def_merge_tr_cl                  false
% 11.83/2.00  --smt_preprocessing                     true
% 11.83/2.00  --smt_ac_axioms                         fast
% 11.83/2.00  --preprocessed_out                      false
% 11.83/2.00  --preprocessed_stats                    false
% 11.83/2.00  
% 11.83/2.00  ------ Abstraction refinement Options
% 11.83/2.00  
% 11.83/2.00  --abstr_ref                             []
% 11.83/2.00  --abstr_ref_prep                        false
% 11.83/2.00  --abstr_ref_until_sat                   false
% 11.83/2.00  --abstr_ref_sig_restrict                funpre
% 11.83/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.83/2.00  --abstr_ref_under                       []
% 11.83/2.00  
% 11.83/2.00  ------ SAT Options
% 11.83/2.00  
% 11.83/2.00  --sat_mode                              false
% 11.83/2.00  --sat_fm_restart_options                ""
% 11.83/2.00  --sat_gr_def                            false
% 11.83/2.00  --sat_epr_types                         true
% 11.83/2.00  --sat_non_cyclic_types                  false
% 11.83/2.00  --sat_finite_models                     false
% 11.83/2.00  --sat_fm_lemmas                         false
% 11.83/2.00  --sat_fm_prep                           false
% 11.83/2.00  --sat_fm_uc_incr                        true
% 11.83/2.00  --sat_out_model                         small
% 11.83/2.00  --sat_out_clauses                       false
% 11.83/2.00  
% 11.83/2.00  ------ QBF Options
% 11.83/2.00  
% 11.83/2.00  --qbf_mode                              false
% 11.83/2.00  --qbf_elim_univ                         false
% 11.83/2.00  --qbf_dom_inst                          none
% 11.83/2.00  --qbf_dom_pre_inst                      false
% 11.83/2.00  --qbf_sk_in                             false
% 11.83/2.00  --qbf_pred_elim                         true
% 11.83/2.00  --qbf_split                             512
% 11.83/2.00  
% 11.83/2.00  ------ BMC1 Options
% 11.83/2.00  
% 11.83/2.00  --bmc1_incremental                      false
% 11.83/2.00  --bmc1_axioms                           reachable_all
% 11.83/2.00  --bmc1_min_bound                        0
% 11.83/2.00  --bmc1_max_bound                        -1
% 11.83/2.00  --bmc1_max_bound_default                -1
% 11.83/2.00  --bmc1_symbol_reachability              true
% 11.83/2.00  --bmc1_property_lemmas                  false
% 11.83/2.00  --bmc1_k_induction                      false
% 11.83/2.00  --bmc1_non_equiv_states                 false
% 11.83/2.00  --bmc1_deadlock                         false
% 11.83/2.00  --bmc1_ucm                              false
% 11.83/2.00  --bmc1_add_unsat_core                   none
% 11.83/2.00  --bmc1_unsat_core_children              false
% 11.83/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.83/2.00  --bmc1_out_stat                         full
% 11.83/2.00  --bmc1_ground_init                      false
% 11.83/2.00  --bmc1_pre_inst_next_state              false
% 11.83/2.00  --bmc1_pre_inst_state                   false
% 11.83/2.00  --bmc1_pre_inst_reach_state             false
% 11.83/2.00  --bmc1_out_unsat_core                   false
% 11.83/2.00  --bmc1_aig_witness_out                  false
% 11.83/2.00  --bmc1_verbose                          false
% 11.83/2.00  --bmc1_dump_clauses_tptp                false
% 11.83/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.83/2.00  --bmc1_dump_file                        -
% 11.83/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.83/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.83/2.00  --bmc1_ucm_extend_mode                  1
% 11.83/2.00  --bmc1_ucm_init_mode                    2
% 11.83/2.00  --bmc1_ucm_cone_mode                    none
% 11.83/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.83/2.00  --bmc1_ucm_relax_model                  4
% 11.83/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.83/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.83/2.00  --bmc1_ucm_layered_model                none
% 11.83/2.00  --bmc1_ucm_max_lemma_size               10
% 11.83/2.00  
% 11.83/2.00  ------ AIG Options
% 11.83/2.00  
% 11.83/2.00  --aig_mode                              false
% 11.83/2.00  
% 11.83/2.00  ------ Instantiation Options
% 11.83/2.00  
% 11.83/2.00  --instantiation_flag                    true
% 11.83/2.00  --inst_sos_flag                         true
% 11.83/2.00  --inst_sos_phase                        true
% 11.83/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel_side                     none
% 11.83/2.00  --inst_solver_per_active                1400
% 11.83/2.00  --inst_solver_calls_frac                1.
% 11.83/2.00  --inst_passive_queue_type               priority_queues
% 11.83/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.83/2.00  --inst_passive_queues_freq              [25;2]
% 11.83/2.00  --inst_dismatching                      true
% 11.83/2.00  --inst_eager_unprocessed_to_passive     true
% 11.83/2.00  --inst_prop_sim_given                   true
% 11.83/2.00  --inst_prop_sim_new                     false
% 11.83/2.00  --inst_subs_new                         false
% 11.83/2.00  --inst_eq_res_simp                      false
% 11.83/2.00  --inst_subs_given                       false
% 11.83/2.00  --inst_orphan_elimination               true
% 11.83/2.00  --inst_learning_loop_flag               true
% 11.83/2.00  --inst_learning_start                   3000
% 11.83/2.00  --inst_learning_factor                  2
% 11.83/2.00  --inst_start_prop_sim_after_learn       3
% 11.83/2.00  --inst_sel_renew                        solver
% 11.83/2.00  --inst_lit_activity_flag                true
% 11.83/2.00  --inst_restr_to_given                   false
% 11.83/2.00  --inst_activity_threshold               500
% 11.83/2.00  --inst_out_proof                        true
% 11.83/2.00  
% 11.83/2.00  ------ Resolution Options
% 11.83/2.00  
% 11.83/2.00  --resolution_flag                       false
% 11.83/2.00  --res_lit_sel                           adaptive
% 11.83/2.00  --res_lit_sel_side                      none
% 11.83/2.00  --res_ordering                          kbo
% 11.83/2.00  --res_to_prop_solver                    active
% 11.83/2.00  --res_prop_simpl_new                    false
% 11.83/2.00  --res_prop_simpl_given                  true
% 11.83/2.00  --res_passive_queue_type                priority_queues
% 11.83/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.83/2.00  --res_passive_queues_freq               [15;5]
% 11.83/2.00  --res_forward_subs                      full
% 11.83/2.00  --res_backward_subs                     full
% 11.83/2.00  --res_forward_subs_resolution           true
% 11.83/2.00  --res_backward_subs_resolution          true
% 11.83/2.00  --res_orphan_elimination                true
% 11.83/2.00  --res_time_limit                        2.
% 11.83/2.00  --res_out_proof                         true
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Options
% 11.83/2.00  
% 11.83/2.00  --superposition_flag                    true
% 11.83/2.00  --sup_passive_queue_type                priority_queues
% 11.83/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.83/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.83/2.00  --demod_completeness_check              fast
% 11.83/2.00  --demod_use_ground                      true
% 11.83/2.00  --sup_to_prop_solver                    passive
% 11.83/2.00  --sup_prop_simpl_new                    true
% 11.83/2.00  --sup_prop_simpl_given                  true
% 11.83/2.00  --sup_fun_splitting                     true
% 11.83/2.00  --sup_smt_interval                      50000
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Simplification Setup
% 11.83/2.00  
% 11.83/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.83/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.83/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.83/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.83/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.83/2.00  --sup_immed_triv                        [TrivRules]
% 11.83/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_bw_main                     []
% 11.83/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.83/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.83/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_input_bw                          []
% 11.83/2.00  
% 11.83/2.00  ------ Combination Options
% 11.83/2.00  
% 11.83/2.00  --comb_res_mult                         3
% 11.83/2.00  --comb_sup_mult                         2
% 11.83/2.00  --comb_inst_mult                        10
% 11.83/2.00  
% 11.83/2.00  ------ Debug Options
% 11.83/2.00  
% 11.83/2.00  --dbg_backtrace                         false
% 11.83/2.00  --dbg_dump_prop_clauses                 false
% 11.83/2.00  --dbg_dump_prop_clauses_file            -
% 11.83/2.00  --dbg_out_stat                          false
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  ------ Proving...
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  % SZS status Theorem for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  fof(f25,conjecture,(
% 11.83/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f26,negated_conjecture,(
% 11.83/2.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.83/2.00    inference(negated_conjecture,[],[f25])).
% 11.83/2.00  
% 11.83/2.00  fof(f55,plain,(
% 11.83/2.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 11.83/2.00    inference(ennf_transformation,[],[f26])).
% 11.83/2.00  
% 11.83/2.00  fof(f56,plain,(
% 11.83/2.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 11.83/2.00    inference(flattening,[],[f55])).
% 11.83/2.00  
% 11.83/2.00  fof(f65,plain,(
% 11.83/2.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f66,plain,(
% 11.83/2.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 11.83/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f65])).
% 11.83/2.00  
% 11.83/2.00  fof(f110,plain,(
% 11.83/2.00    r1_tarski(sK2,sK0)),
% 11.83/2.00    inference(cnf_transformation,[],[f66])).
% 11.83/2.00  
% 11.83/2.00  fof(f1,axiom,(
% 11.83/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f57,plain,(
% 11.83/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.83/2.00    inference(nnf_transformation,[],[f1])).
% 11.83/2.00  
% 11.83/2.00  fof(f58,plain,(
% 11.83/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.83/2.00    inference(flattening,[],[f57])).
% 11.83/2.00  
% 11.83/2.00  fof(f68,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.83/2.00    inference(cnf_transformation,[],[f58])).
% 11.83/2.00  
% 11.83/2.00  fof(f113,plain,(
% 11.83/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.83/2.00    inference(equality_resolution,[],[f68])).
% 11.83/2.00  
% 11.83/2.00  fof(f5,axiom,(
% 11.83/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f61,plain,(
% 11.83/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.83/2.00    inference(nnf_transformation,[],[f5])).
% 11.83/2.00  
% 11.83/2.00  fof(f76,plain,(
% 11.83/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f61])).
% 11.83/2.00  
% 11.83/2.00  fof(f20,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f47,plain,(
% 11.83/2.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f20])).
% 11.83/2.00  
% 11.83/2.00  fof(f95,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f47])).
% 11.83/2.00  
% 11.83/2.00  fof(f8,axiom,(
% 11.83/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f32,plain,(
% 11.83/2.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(ennf_transformation,[],[f8])).
% 11.83/2.00  
% 11.83/2.00  fof(f63,plain,(
% 11.83/2.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(nnf_transformation,[],[f32])).
% 11.83/2.00  
% 11.83/2.00  fof(f80,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f63])).
% 11.83/2.00  
% 11.83/2.00  fof(f10,axiom,(
% 11.83/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f83,plain,(
% 11.83/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f10])).
% 11.83/2.00  
% 11.83/2.00  fof(f2,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f27,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.83/2.00    inference(ennf_transformation,[],[f2])).
% 11.83/2.00  
% 11.83/2.00  fof(f28,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.83/2.00    inference(flattening,[],[f27])).
% 11.83/2.00  
% 11.83/2.00  fof(f70,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f28])).
% 11.83/2.00  
% 11.83/2.00  fof(f22,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f49,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f22])).
% 11.83/2.00  
% 11.83/2.00  fof(f50,plain,(
% 11.83/2.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(flattening,[],[f49])).
% 11.83/2.00  
% 11.83/2.00  fof(f64,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(nnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f97,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f64])).
% 11.83/2.00  
% 11.83/2.00  fof(f108,plain,(
% 11.83/2.00    v1_funct_2(sK3,sK0,sK1)),
% 11.83/2.00    inference(cnf_transformation,[],[f66])).
% 11.83/2.00  
% 11.83/2.00  fof(f109,plain,(
% 11.83/2.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.83/2.00    inference(cnf_transformation,[],[f66])).
% 11.83/2.00  
% 11.83/2.00  fof(f21,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f48,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f21])).
% 11.83/2.00  
% 11.83/2.00  fof(f96,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f48])).
% 11.83/2.00  
% 11.83/2.00  fof(f16,axiom,(
% 11.83/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f41,plain,(
% 11.83/2.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(ennf_transformation,[],[f16])).
% 11.83/2.00  
% 11.83/2.00  fof(f42,plain,(
% 11.83/2.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(flattening,[],[f41])).
% 11.83/2.00  
% 11.83/2.00  fof(f89,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f42])).
% 11.83/2.00  
% 11.83/2.00  fof(f75,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f61])).
% 11.83/2.00  
% 11.83/2.00  fof(f6,axiom,(
% 11.83/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f30,plain,(
% 11.83/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.83/2.00    inference(ennf_transformation,[],[f6])).
% 11.83/2.00  
% 11.83/2.00  fof(f77,plain,(
% 11.83/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f30])).
% 11.83/2.00  
% 11.83/2.00  fof(f15,axiom,(
% 11.83/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f40,plain,(
% 11.83/2.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(ennf_transformation,[],[f15])).
% 11.83/2.00  
% 11.83/2.00  fof(f88,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f40])).
% 11.83/2.00  
% 11.83/2.00  fof(f11,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f34,plain,(
% 11.83/2.00    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 11.83/2.00    inference(ennf_transformation,[],[f11])).
% 11.83/2.00  
% 11.83/2.00  fof(f35,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 11.83/2.00    inference(flattening,[],[f34])).
% 11.83/2.00  
% 11.83/2.00  fof(f84,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f35])).
% 11.83/2.00  
% 11.83/2.00  fof(f9,axiom,(
% 11.83/2.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f33,plain,(
% 11.83/2.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 11.83/2.00    inference(ennf_transformation,[],[f9])).
% 11.83/2.00  
% 11.83/2.00  fof(f82,plain,(
% 11.83/2.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f33])).
% 11.83/2.00  
% 11.83/2.00  fof(f107,plain,(
% 11.83/2.00    v1_funct_1(sK3)),
% 11.83/2.00    inference(cnf_transformation,[],[f66])).
% 11.83/2.00  
% 11.83/2.00  fof(f19,axiom,(
% 11.83/2.00    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f45,plain,(
% 11.83/2.00    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.83/2.00    inference(ennf_transformation,[],[f19])).
% 11.83/2.00  
% 11.83/2.00  fof(f46,plain,(
% 11.83/2.00    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.83/2.00    inference(flattening,[],[f45])).
% 11.83/2.00  
% 11.83/2.00  fof(f93,plain,(
% 11.83/2.00    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f46])).
% 11.83/2.00  
% 11.83/2.00  fof(f18,axiom,(
% 11.83/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f44,plain,(
% 11.83/2.00    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(ennf_transformation,[],[f18])).
% 11.83/2.00  
% 11.83/2.00  fof(f91,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f44])).
% 11.83/2.00  
% 11.83/2.00  fof(f24,axiom,(
% 11.83/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f53,plain,(
% 11.83/2.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.83/2.00    inference(ennf_transformation,[],[f24])).
% 11.83/2.00  
% 11.83/2.00  fof(f54,plain,(
% 11.83/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(flattening,[],[f53])).
% 11.83/2.00  
% 11.83/2.00  fof(f106,plain,(
% 11.83/2.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f23,axiom,(
% 11.83/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f51,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.83/2.00    inference(ennf_transformation,[],[f23])).
% 11.83/2.00  
% 11.83/2.00  fof(f52,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.83/2.00    inference(flattening,[],[f51])).
% 11.83/2.00  
% 11.83/2.00  fof(f103,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f52])).
% 11.83/2.00  
% 11.83/2.00  fof(f105,plain,(
% 11.83/2.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f54])).
% 11.83/2.00  
% 11.83/2.00  fof(f112,plain,(
% 11.83/2.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 11.83/2.00    inference(cnf_transformation,[],[f66])).
% 11.83/2.00  
% 11.83/2.00  fof(f102,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f64])).
% 11.83/2.00  
% 11.83/2.00  fof(f117,plain,(
% 11.83/2.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(equality_resolution,[],[f102])).
% 11.83/2.00  
% 11.83/2.00  fof(f118,plain,(
% 11.83/2.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 11.83/2.00    inference(equality_resolution,[],[f117])).
% 11.83/2.00  
% 11.83/2.00  fof(f4,axiom,(
% 11.83/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f59,plain,(
% 11.83/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.83/2.00    inference(nnf_transformation,[],[f4])).
% 11.83/2.00  
% 11.83/2.00  fof(f60,plain,(
% 11.83/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.83/2.00    inference(flattening,[],[f59])).
% 11.83/2.00  
% 11.83/2.00  fof(f74,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.83/2.00    inference(cnf_transformation,[],[f60])).
% 11.83/2.00  
% 11.83/2.00  fof(f115,plain,(
% 11.83/2.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.83/2.00    inference(equality_resolution,[],[f74])).
% 11.83/2.00  
% 11.83/2.00  fof(f67,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.83/2.00    inference(cnf_transformation,[],[f58])).
% 11.83/2.00  
% 11.83/2.00  fof(f114,plain,(
% 11.83/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.83/2.00    inference(equality_resolution,[],[f67])).
% 11.83/2.00  
% 11.83/2.00  fof(f72,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f60])).
% 11.83/2.00  
% 11.83/2.00  fof(f73,plain,(
% 11.83/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.83/2.00    inference(cnf_transformation,[],[f60])).
% 11.83/2.00  
% 11.83/2.00  fof(f116,plain,(
% 11.83/2.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.83/2.00    inference(equality_resolution,[],[f73])).
% 11.83/2.00  
% 11.83/2.00  fof(f3,axiom,(
% 11.83/2.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f29,plain,(
% 11.83/2.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 11.83/2.00    inference(ennf_transformation,[],[f3])).
% 11.83/2.00  
% 11.83/2.00  fof(f71,plain,(
% 11.83/2.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f29])).
% 11.83/2.00  
% 11.83/2.00  fof(f101,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f64])).
% 11.83/2.00  
% 11.83/2.00  fof(f119,plain,(
% 11.83/2.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 11.83/2.00    inference(equality_resolution,[],[f101])).
% 11.83/2.00  
% 11.83/2.00  fof(f111,plain,(
% 11.83/2.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 11.83/2.00    inference(cnf_transformation,[],[f66])).
% 11.83/2.00  
% 11.83/2.00  fof(f13,axiom,(
% 11.83/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f38,plain,(
% 11.83/2.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(ennf_transformation,[],[f13])).
% 11.83/2.00  
% 11.83/2.00  fof(f86,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f38])).
% 11.83/2.00  
% 11.83/2.00  fof(f69,plain,(
% 11.83/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f58])).
% 11.83/2.00  
% 11.83/2.00  fof(f14,axiom,(
% 11.83/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f39,plain,(
% 11.83/2.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(ennf_transformation,[],[f14])).
% 11.83/2.00  
% 11.83/2.00  fof(f87,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f39])).
% 11.83/2.00  
% 11.83/2.00  cnf(c_42,negated_conjecture,
% 11.83/2.00      ( r1_tarski(sK2,sK0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f110]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2100,plain,
% 11.83/2.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1,plain,
% 11.83/2.00      ( r1_tarski(X0,X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f113]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2122,plain,
% 11.83/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_8,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2119,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.83/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_27,plain,
% 11.83/2.00      ( v5_relat_1(X0,X1)
% 11.83/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.83/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14,plain,
% 11.83/2.00      ( ~ v5_relat_1(X0,X1)
% 11.83/2.00      | r1_tarski(k2_relat_1(X0),X1)
% 11.83/2.00      | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_542,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | r1_tarski(k2_relat_1(X0),X2)
% 11.83/2.00      | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(resolution,[status(thm)],[c_27,c_14]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2096,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3830,plain,
% 11.83/2.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2119,c_2096]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14471,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top
% 11.83/2.00      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2122,c_3830]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_16,plain,
% 11.83/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_118,plain,
% 11.83/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18741,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_14471,c_118]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.83/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2121,plain,
% 11.83/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.83/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.83/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18750,plain,
% 11.83/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(k2_zfmisc_1(X2,X0)),X1) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_18741,c_2121]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_35,plain,
% 11.83/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.83/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.83/2.00      | k1_xboole_0 = X2 ),
% 11.83/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_44,negated_conjecture,
% 11.83/2.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f108]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_794,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.83/2.00      | sK3 != X0
% 11.83/2.00      | sK1 != X2
% 11.83/2.00      | sK0 != X1
% 11.83/2.00      | k1_xboole_0 = X2 ),
% 11.83/2.00      inference(resolution_lifted,[status(thm)],[c_35,c_44]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_795,plain,
% 11.83/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.83/2.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 11.83/2.00      | k1_xboole_0 = sK1 ),
% 11.83/2.00      inference(unflattening,[status(thm)],[c_794]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_43,negated_conjecture,
% 11.83/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.83/2.00      inference(cnf_transformation,[],[f109]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_797,plain,
% 11.83/2.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_795,c_43]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2099,plain,
% 11.83/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_29,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2103,plain,
% 11.83/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3843,plain,
% 11.83/2.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2099,c_2103]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4080,plain,
% 11.83/2.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_797,c_3843]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_22,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.83/2.00      | ~ v1_relat_1(X1)
% 11.83/2.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2108,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 11.83/2.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5835,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 11.83/2.00      | sK1 = k1_xboole_0
% 11.83/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_4080,c_2108]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2114,plain,
% 11.83/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2118,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.83/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3223,plain,
% 11.83/2.00      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2099,c_2118]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_10,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/2.00      | ~ v1_relat_1(X1)
% 11.83/2.00      | v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_336,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.83/2.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_337,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_336]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_409,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.83/2.00      inference(bin_hyper_res,[status(thm)],[c_10,c_337]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2097,plain,
% 11.83/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.83/2.00      | v1_relat_1(X1) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4431,plain,
% 11.83/2.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_3223,c_2097]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5297,plain,
% 11.83/2.00      ( v1_relat_1(sK3) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2114,c_4431]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7446,plain,
% 11.83/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.83/2.00      | sK1 = k1_xboole_0
% 11.83/2.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_5835,c_5297]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7447,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 11.83/2.00      | sK1 = k1_xboole_0
% 11.83/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_7446]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18817,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(k2_zfmisc_1(X0,X1))
% 11.83/2.00      | sK1 = k1_xboole_0
% 11.83/2.00      | r1_tarski(X1,sK0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_18750,c_7447]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_29294,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,sK2)))) = k2_relat_1(k2_zfmisc_1(X0,sK2))
% 11.83/2.00      | sK1 = k1_xboole_0 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2100,c_18817]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_21,plain,
% 11.83/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 11.83/2.00      | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2109,plain,
% 11.83/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4428,plain,
% 11.83/2.00      ( v1_relat_1(X0) != iProver_top
% 11.83/2.00      | v1_relat_1(k1_relat_1(X0)) != iProver_top
% 11.83/2.00      | v1_relat_1(k1_relat_1(k7_relat_1(X0,X1))) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2109,c_2097]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_17,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1)
% 11.83/2.00      | ~ v1_relat_1(X2)
% 11.83/2.00      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2113,plain,
% 11.83/2.00      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
% 11.83/2.00      | r1_tarski(X2,X1) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5994,plain,
% 11.83/2.00      ( k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK2)
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2100,c_2113]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_50370,plain,
% 11.83/2.00      ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(X0,X1)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(X0,X1)),sK2)
% 11.83/2.00      | v1_relat_1(X0) != iProver_top
% 11.83/2.00      | v1_relat_1(k1_relat_1(X0)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_4428,c_5994]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51061,plain,
% 11.83/2.00      ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,sK2))),X1)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,sK2))),X1)),sK2)
% 11.83/2.00      | sK1 = k1_xboole_0
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,k2_relat_1(k2_zfmisc_1(X0,sK2)))) != iProver_top
% 11.83/2.00      | v1_relat_1(k2_relat_1(k2_zfmisc_1(X0,sK2))) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_29294,c_50370]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_15,plain,
% 11.83/2.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2115,plain,
% 11.83/2.00      ( v1_relat_1(X0) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7454,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2100,c_7447]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51055,plain,
% 11.83/2.00      ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)),sK2)
% 11.83/2.00      | sK1 = k1_xboole_0
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
% 11.83/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_7454,c_50370]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_45,negated_conjecture,
% 11.83/2.00      ( v1_funct_1(sK3) ),
% 11.83/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_46,plain,
% 11.83/2.00      ( v1_funct_1(sK3) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3831,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2099,c_2096]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_25,plain,
% 11.83/2.00      ( ~ v1_funct_1(X0)
% 11.83/2.00      | v1_funct_1(k7_relat_1(X0,X1))
% 11.83/2.00      | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2830,plain,
% 11.83/2.00      ( v1_funct_1(k7_relat_1(sK3,X0))
% 11.83/2.00      | ~ v1_funct_1(sK3)
% 11.83/2.00      | ~ v1_relat_1(sK3) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_25]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_27735,plain,
% 11.83/2.00      ( v1_funct_1(k7_relat_1(sK3,sK2))
% 11.83/2.00      | ~ v1_funct_1(sK3)
% 11.83/2.00      | ~ v1_relat_1(sK3) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2830]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_27736,plain,
% 11.83/2.00      ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
% 11.83/2.00      | v1_funct_1(sK3) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_27735]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_24,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 11.83/2.00      | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2106,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5765,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(k7_relat_1(X0,X2)),X1) = iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2106,c_2121]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_37,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 11.83/2.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2101,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7657,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 11.83/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_7454,c_2101]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_36,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.83/2.00      inference(cnf_transformation,[],[f103]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2102,plain,
% 11.83/2.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.83/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6916,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 11.83/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2099,c_2102]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7218,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_6916,c_46]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_38,plain,
% 11.83/2.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 11.83/2.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_40,negated_conjecture,
% 11.83/2.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 11.83/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.83/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f112]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_805,plain,
% 11.83/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.83/2.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | ~ v1_relat_1(X0)
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 11.83/2.00      | k1_relat_1(X0) != sK2
% 11.83/2.00      | sK1 != X1 ),
% 11.83/2.00      inference(resolution_lifted,[status(thm)],[c_38,c_40]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_806,plain,
% 11.83/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.83/2.00      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 11.83/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 11.83/2.00      inference(unflattening,[status(thm)],[c_805]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_818,plain,
% 11.83/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.83/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 11.83/2.00      inference(forward_subsumption_resolution,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_806,c_542]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2087,plain,
% 11.83/2.00      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 11.83/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 11.83/2.00      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7223,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_7218,c_2087]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7664,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_7454,c_7223]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9621,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 11.83/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_7657,c_7664]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_42848,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 11.83/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_5765,c_9621]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51298,plain,
% 11.83/2.00      ( v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
% 11.83/2.00      | sK1 = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_51055,c_46,c_3831,c_5297,c_27736,c_42848]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51299,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_51298]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51302,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2115,c_51299]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51389,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_51061,c_5297,c_51302]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30,plain,
% 11.83/2.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 11.83/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 11.83/2.00      | k1_xboole_0 = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f118]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_621,plain,
% 11.83/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.83/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 11.83/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.83/2.00      | sK2 != X0
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = X0 ),
% 11.83/2.00      inference(resolution_lifted,[status(thm)],[c_30,c_40]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_622,plain,
% 11.83/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.83/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 11.83/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = sK2 ),
% 11.83/2.00      inference(unflattening,[status(thm)],[c_621]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2095,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = sK2
% 11.83/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5,plain,
% 11.83/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f115]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2127,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.83/2.00      | sK2 = k1_xboole_0
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_2095,c_5]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_140,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.83/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_142,plain,
% 11.83/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_140]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2,plain,
% 11.83/2.00      ( r1_tarski(X0,X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f114]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_149,plain,
% 11.83/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_151,plain,
% 11.83/2.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_149]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2748,plain,
% 11.83/2.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | sK2 = k1_xboole_0
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_2127,c_142,c_151]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2749,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.83/2.00      | sK2 = k1_xboole_0
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_2748]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7222,plain,
% 11.83/2.00      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 11.83/2.00      | sK2 = k1_xboole_0
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_7218,c_2749]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7,plain,
% 11.83/2.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = X1 ),
% 11.83/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_143,plain,
% 11.83/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = k1_xboole_0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6,plain,
% 11.83/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f116]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_144,plain,
% 11.83/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_150,plain,
% 11.83/2.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1283,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.83/2.00      theory(equality) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2236,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1)
% 11.83/2.00      | r1_tarski(sK0,k1_xboole_0)
% 11.83/2.00      | sK0 != X0
% 11.83/2.00      | k1_xboole_0 != X1 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1283]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2238,plain,
% 11.83/2.00      ( r1_tarski(sK0,k1_xboole_0)
% 11.83/2.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.83/2.00      | sK0 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2236]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1282,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2186,plain,
% 11.83/2.00      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1282]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2249,plain,
% 11.83/2.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2186]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2216,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 11.83/2.00      | ~ r1_tarski(sK2,X0)
% 11.83/2.00      | r1_tarski(sK2,k1_xboole_0) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2310,plain,
% 11.83/2.00      ( ~ r1_tarski(sK2,sK0)
% 11.83/2.00      | r1_tarski(sK2,k1_xboole_0)
% 11.83/2.00      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2216]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1281,plain,( X0 = X0 ),theory(equality) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2377,plain,
% 11.83/2.00      ( sK2 = sK2 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1281]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2784,plain,
% 11.83/2.00      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_31,plain,
% 11.83/2.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 11.83/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.83/2.00      | k1_xboole_0 = X1
% 11.83/2.00      | k1_xboole_0 = X0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f119]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_673,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.83/2.00      | sK3 != X0
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | sK0 != X1
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = X1 ),
% 11.83/2.00      inference(resolution_lifted,[status(thm)],[c_31,c_44]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_674,plain,
% 11.83/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = sK3
% 11.83/2.00      | k1_xboole_0 = sK0 ),
% 11.83/2.00      inference(unflattening,[status(thm)],[c_673]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2093,plain,
% 11.83/2.00      ( sK1 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = sK3
% 11.83/2.00      | k1_xboole_0 = sK0
% 11.83/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2125,plain,
% 11.83/2.00      ( sK3 = k1_xboole_0
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | sK0 = k1_xboole_0
% 11.83/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_2093,c_5]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_41,negated_conjecture,
% 11.83/2.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 11.83/2.00      inference(cnf_transformation,[],[f111]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2190,plain,
% 11.83/2.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1282]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2254,plain,
% 11.83/2.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2190]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2380,plain,
% 11.83/2.00      ( sK0 = sK0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1281]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2767,plain,
% 11.83/2.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1282]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2768,plain,
% 11.83/2.00      ( sK1 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 = sK1
% 11.83/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2767]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2826,plain,
% 11.83/2.00      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_2125,c_41,c_143,c_144,c_2254,c_2380,c_2768]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2827,plain,
% 11.83/2.00      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_2826]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7439,plain,
% 11.83/2.00      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_7222,c_42,c_143,c_144,c_150,c_2238,c_2249,c_2310,
% 11.83/2.00                 c_2377,c_2784,c_2827]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51607,plain,
% 11.83/2.00      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_51389,c_7439]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51647,plain,
% 11.83/2.00      ( sK2 = k1_xboole_0 ),
% 11.83/2.00      inference(equality_resolution_simp,[status(thm)],[c_51607]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_824,plain,
% 11.83/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.83/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 11.83/2.00      | sK2 != sK0
% 11.83/2.00      | sK1 != sK1 ),
% 11.83/2.00      inference(resolution_lifted,[status(thm)],[c_40,c_44]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_938,plain,
% 11.83/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.83/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 11.83/2.00      | sK2 != sK0 ),
% 11.83/2.00      inference(equality_resolution_simp,[status(thm)],[c_824]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2086,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 11.83/2.00      | sK2 != sK0
% 11.83/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_825,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 11.83/2.00      | sK2 != sK0
% 11.83/2.00      | sK1 != sK1
% 11.83/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_824]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1291,plain,
% 11.83/2.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 11.83/2.00      theory(equality) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2192,plain,
% 11.83/2.00      ( ~ v1_funct_1(X0)
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1291]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2287,plain,
% 11.83/2.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.83/2.00      | ~ v1_funct_1(sK3)
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2192]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2288,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 11.83/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 11.83/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_2287]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2357,plain,
% 11.83/2.00      ( sK1 = sK1 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1281]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2502,plain,
% 11.83/2.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.83/2.00      | sK2 != sK0
% 11.83/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_2086,c_46,c_825,c_2288,c_2357]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2503,plain,
% 11.83/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 11.83/2.00      | sK2 != sK0
% 11.83/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_2502]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7224,plain,
% 11.83/2.00      ( k7_relat_1(sK3,sK2) != sK3
% 11.83/2.00      | sK2 != sK0
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_7218,c_2503]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51609,plain,
% 11.83/2.00      ( k7_relat_1(sK3,sK2) != sK3
% 11.83/2.00      | sK2 != sK0
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_51389,c_7224]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51626,plain,
% 11.83/2.00      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_51389,c_41]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51627,plain,
% 11.83/2.00      ( sK0 = k1_xboole_0 ),
% 11.83/2.00      inference(equality_resolution_simp,[status(thm)],[c_51626]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51645,plain,
% 11.83/2.00      ( k7_relat_1(sK3,sK2) != sK3
% 11.83/2.00      | sK2 != k1_xboole_0
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_51609,c_51627]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51646,plain,
% 11.83/2.00      ( k7_relat_1(sK3,sK2) != sK3
% 11.83/2.00      | sK2 != k1_xboole_0
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_51645,c_5]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51648,plain,
% 11.83/2.00      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 11.83/2.00      | k1_xboole_0 != k1_xboole_0
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_51647,c_51646]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51650,plain,
% 11.83/2.00      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(equality_resolution_simp,[status(thm)],[c_51648]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_19,plain,
% 11.83/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2111,plain,
% 11.83/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2120,plain,
% 11.83/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3414,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2111,c_2120]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5599,plain,
% 11.83/2.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_5297,c_3414]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30767,plain,
% 11.83/2.00      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 11.83/2.00      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_5599,c_2101]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30784,plain,
% 11.83/2.00      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 11.83/2.00      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_30767,c_6]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2831,plain,
% 11.83/2.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 11.83/2.00      | v1_funct_1(sK3) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_2830]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2833,plain,
% 11.83/2.00      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 11.83/2.00      | v1_funct_1(sK3) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2831]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_31198,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 11.83/2.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_30784,c_46,c_2833,c_5297]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_31199,plain,
% 11.83/2.00      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_31198]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_31204,plain,
% 11.83/2.00      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2122,c_31199]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_31209,plain,
% 11.83/2.00      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_31204,c_2118]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_36567,plain,
% 11.83/2.00      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0
% 11.83/2.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_31209,c_2120]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_36587,plain,
% 11.83/2.00      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2115,c_36567]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_36626,plain,
% 11.83/2.00      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_36587,c_5297]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_51651,plain,
% 11.83/2.00      ( sK3 != k1_xboole_0
% 11.83/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_51650,c_36626]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5769,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 11.83/2.00      | r1_tarski(sK1,X0) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_3831,c_2121]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6424,plain,
% 11.83/2.00      ( r1_tarski(sK1,X0) != iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(sK3),X0) = iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_5769,c_5297]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6425,plain,
% 11.83/2.00      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 11.83/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_6424]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_647,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.83/2.00      | ~ r1_tarski(k2_relat_1(X2),X3)
% 11.83/2.00      | ~ v1_funct_1(X2)
% 11.83/2.00      | ~ v1_relat_1(X2)
% 11.83/2.00      | X2 != X0
% 11.83/2.00      | k1_relat_1(X2) != X1
% 11.83/2.00      | k1_xboole_0 != X3
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = X1 ),
% 11.83/2.00      inference(resolution_lifted,[status(thm)],[c_31,c_38]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_648,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 11.83/2.00      | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_relat_1(X0)
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 11.83/2.00      inference(unflattening,[status(thm)],[c_647]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_664,plain,
% 11.83/2.00      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_relat_1(X0)
% 11.83/2.00      | k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 11.83/2.00      inference(forward_subsumption_resolution,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_648,c_37]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2094,plain,
% 11.83/2.00      ( k1_xboole_0 = X0
% 11.83/2.00      | k1_xboole_0 = k1_relat_1(X0)
% 11.83/2.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6439,plain,
% 11.83/2.00      ( k1_relat_1(sK3) = k1_xboole_0
% 11.83/2.00      | sK3 = k1_xboole_0
% 11.83/2.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 11.83/2.00      | v1_funct_1(sK3) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_6425,c_2094]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_0,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.83/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2682,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2683,plain,
% 11.83/2.00      ( sK3 = X0
% 11.83/2.00      | r1_tarski(X0,sK3) != iProver_top
% 11.83/2.00      | r1_tarski(sK3,X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_2682]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2685,plain,
% 11.83/2.00      ( sK3 = k1_xboole_0
% 11.83/2.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 11.83/2.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2683]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_20,plain,
% 11.83/2.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3611,plain,
% 11.83/2.00      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_20]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3612,plain,
% 11.83/2.00      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_3611]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3614,plain,
% 11.83/2.00      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_3612]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2714,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK3) | r1_tarski(X0,sK3) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3704,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,k7_relat_1(sK3,X1))
% 11.83/2.00      | r1_tarski(X0,sK3)
% 11.83/2.00      | ~ r1_tarski(k7_relat_1(sK3,X1),sK3) ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2714]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3705,plain,
% 11.83/2.00      ( r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top
% 11.83/2.00      | r1_tarski(X0,sK3) = iProver_top
% 11.83/2.00      | r1_tarski(k7_relat_1(sK3,X1),sK3) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_3704]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3707,plain,
% 11.83/2.00      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
% 11.83/2.00      | r1_tarski(k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 11.83/2.00      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_3705]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5734,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 11.83/2.00      | v1_funct_1(sK3) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_4080,c_2101]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9509,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_5734,c_46,c_5297]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9515,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_5,c_9509]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2208,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1)
% 11.83/2.00      | r1_tarski(sK1,k1_xboole_0)
% 11.83/2.00      | sK1 != X0
% 11.83/2.00      | k1_xboole_0 != X1 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1283]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2209,plain,
% 11.83/2.00      ( sK1 != X0
% 11.83/2.00      | k1_xboole_0 != X1
% 11.83/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.83/2.00      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2211,plain,
% 11.83/2.00      ( sK1 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 != k1_xboole_0
% 11.83/2.00      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 11.83/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2209]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_5732,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_5,c_2101]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7080,plain,
% 11.83/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 11.83/2.00      | v1_funct_1(sK3) != iProver_top
% 11.83/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_6425,c_5732]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9796,plain,
% 11.83/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_9515,c_46,c_143,c_144,c_151,c_2211,c_5297,c_7080]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9800,plain,
% 11.83/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_6425,c_9796]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_10190,plain,
% 11.83/2.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 11.83/2.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_9800,c_2118]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26113,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1)
% 11.83/2.00      | r1_tarski(X2,k7_relat_1(sK3,X3))
% 11.83/2.00      | X2 != X0
% 11.83/2.00      | k7_relat_1(sK3,X3) != X1 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1283]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26114,plain,
% 11.83/2.00      ( X0 != X1
% 11.83/2.00      | k7_relat_1(sK3,X2) != X3
% 11.83/2.00      | r1_tarski(X1,X3) != iProver_top
% 11.83/2.00      | r1_tarski(X0,k7_relat_1(sK3,X2)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_26113]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26116,plain,
% 11.83/2.00      ( k7_relat_1(sK3,k1_xboole_0) != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 != k1_xboole_0
% 11.83/2.00      | r1_tarski(k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 11.83/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_26114]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_47930,plain,
% 11.83/2.00      ( sK3 = k1_xboole_0 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_6439,c_143,c_144,c_151,c_2685,c_3614,c_3707,c_5297,
% 11.83/2.00                 c_10190,c_26116,c_36587]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_47932,plain,
% 11.83/2.00      ( ~ r1_tarski(sK1,k1_xboole_0) | sK3 = k1_xboole_0 ),
% 11.83/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_47930]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2210,plain,
% 11.83/2.00      ( r1_tarski(sK1,k1_xboole_0)
% 11.83/2.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.83/2.00      | sK1 != k1_xboole_0
% 11.83/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_2208]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(contradiction,plain,
% 11.83/2.00      ( $false ),
% 11.83/2.00      inference(minisat,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_51651,c_51302,c_47932,c_5297,c_2210,c_151,c_150,c_144,
% 11.83/2.00                 c_143,c_142]) ).
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  ------                               Statistics
% 11.83/2.00  
% 11.83/2.00  ------ General
% 11.83/2.00  
% 11.83/2.00  abstr_ref_over_cycles:                  0
% 11.83/2.00  abstr_ref_under_cycles:                 0
% 11.83/2.00  gc_basic_clause_elim:                   0
% 11.83/2.00  forced_gc_time:                         0
% 11.83/2.00  parsing_time:                           0.01
% 11.83/2.00  unif_index_cands_time:                  0.
% 11.83/2.00  unif_index_add_time:                    0.
% 11.83/2.00  orderings_time:                         0.
% 11.83/2.00  out_proof_time:                         0.025
% 11.83/2.00  total_time:                             1.35
% 11.83/2.00  num_of_symbols:                         50
% 11.83/2.00  num_of_terms:                           37621
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing
% 11.83/2.00  
% 11.83/2.00  num_of_splits:                          0
% 11.83/2.00  num_of_split_atoms:                     0
% 11.83/2.00  num_of_reused_defs:                     0
% 11.83/2.00  num_eq_ax_congr_red:                    10
% 11.83/2.00  num_of_sem_filtered_clauses:            1
% 11.83/2.00  num_of_subtypes:                        0
% 11.83/2.00  monotx_restored_types:                  0
% 11.83/2.00  sat_num_of_epr_types:                   0
% 11.83/2.00  sat_num_of_non_cyclic_types:            0
% 11.83/2.00  sat_guarded_non_collapsed_types:        0
% 11.83/2.00  num_pure_diseq_elim:                    0
% 11.83/2.00  simp_replaced_by:                       0
% 11.83/2.00  res_preprocessed:                       199
% 11.83/2.00  prep_upred:                             0
% 11.83/2.00  prep_unflattend:                        43
% 11.83/2.00  smt_new_axioms:                         0
% 11.83/2.00  pred_elim_cands:                        5
% 11.83/2.00  pred_elim:                              2
% 11.83/2.00  pred_elim_cl:                           0
% 11.83/2.00  pred_elim_cycles:                       5
% 11.83/2.00  merged_defs:                            8
% 11.83/2.00  merged_defs_ncl:                        0
% 11.83/2.00  bin_hyper_res:                          9
% 11.83/2.00  prep_cycles:                            4
% 11.83/2.00  pred_elim_time:                         0.011
% 11.83/2.00  splitting_time:                         0.
% 11.83/2.00  sem_filter_time:                        0.
% 11.83/2.00  monotx_time:                            0.001
% 11.83/2.00  subtype_inf_time:                       0.
% 11.83/2.00  
% 11.83/2.00  ------ Problem properties
% 11.83/2.00  
% 11.83/2.00  clauses:                                43
% 11.83/2.00  conjectures:                            4
% 11.83/2.00  epr:                                    8
% 11.83/2.00  horn:                                   38
% 11.83/2.00  ground:                                 12
% 11.83/2.00  unary:                                  7
% 11.83/2.00  binary:                                 13
% 11.83/2.00  lits:                                   118
% 11.83/2.00  lits_eq:                                38
% 11.83/2.00  fd_pure:                                0
% 11.83/2.00  fd_pseudo:                              0
% 11.83/2.00  fd_cond:                                4
% 11.83/2.00  fd_pseudo_cond:                         1
% 11.83/2.00  ac_symbols:                             0
% 11.83/2.00  
% 11.83/2.00  ------ Propositional Solver
% 11.83/2.00  
% 11.83/2.00  prop_solver_calls:                      32
% 11.83/2.00  prop_fast_solver_calls:                 2951
% 11.83/2.00  smt_solver_calls:                       0
% 11.83/2.00  smt_fast_solver_calls:                  0
% 11.83/2.00  prop_num_of_clauses:                    22822
% 11.83/2.00  prop_preprocess_simplified:             35205
% 11.83/2.00  prop_fo_subsumed:                       122
% 11.83/2.00  prop_solver_time:                       0.
% 11.83/2.00  smt_solver_time:                        0.
% 11.83/2.00  smt_fast_solver_time:                   0.
% 11.83/2.00  prop_fast_solver_time:                  0.
% 11.83/2.00  prop_unsat_core_time:                   0.002
% 11.83/2.00  
% 11.83/2.00  ------ QBF
% 11.83/2.00  
% 11.83/2.00  qbf_q_res:                              0
% 11.83/2.00  qbf_num_tautologies:                    0
% 11.83/2.00  qbf_prep_cycles:                        0
% 11.83/2.00  
% 11.83/2.00  ------ BMC1
% 11.83/2.00  
% 11.83/2.00  bmc1_current_bound:                     -1
% 11.83/2.00  bmc1_last_solved_bound:                 -1
% 11.83/2.00  bmc1_unsat_core_size:                   -1
% 11.83/2.00  bmc1_unsat_core_parents_size:           -1
% 11.83/2.00  bmc1_merge_next_fun:                    0
% 11.83/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.83/2.00  
% 11.83/2.00  ------ Instantiation
% 11.83/2.00  
% 11.83/2.00  inst_num_of_clauses:                    4397
% 11.83/2.00  inst_num_in_passive:                    1817
% 11.83/2.00  inst_num_in_active:                     2065
% 11.83/2.00  inst_num_in_unprocessed:                515
% 11.83/2.00  inst_num_of_loops:                      2710
% 11.83/2.00  inst_num_of_learning_restarts:          0
% 11.83/2.00  inst_num_moves_active_passive:          642
% 11.83/2.00  inst_lit_activity:                      0
% 11.83/2.00  inst_lit_activity_moves:                0
% 11.83/2.00  inst_num_tautologies:                   0
% 11.83/2.00  inst_num_prop_implied:                  0
% 11.83/2.00  inst_num_existing_simplified:           0
% 11.83/2.00  inst_num_eq_res_simplified:             0
% 11.83/2.00  inst_num_child_elim:                    0
% 11.83/2.00  inst_num_of_dismatching_blockings:      2620
% 11.83/2.00  inst_num_of_non_proper_insts:           8042
% 11.83/2.00  inst_num_of_duplicates:                 0
% 11.83/2.00  inst_inst_num_from_inst_to_res:         0
% 11.83/2.00  inst_dismatching_checking_time:         0.
% 11.83/2.00  
% 11.83/2.00  ------ Resolution
% 11.83/2.00  
% 11.83/2.00  res_num_of_clauses:                     0
% 11.83/2.00  res_num_in_passive:                     0
% 11.83/2.00  res_num_in_active:                      0
% 11.83/2.00  res_num_of_loops:                       203
% 11.83/2.00  res_forward_subset_subsumed:            220
% 11.83/2.00  res_backward_subset_subsumed:           4
% 11.83/2.00  res_forward_subsumed:                   0
% 11.83/2.00  res_backward_subsumed:                  0
% 11.83/2.00  res_forward_subsumption_resolution:     3
% 11.83/2.00  res_backward_subsumption_resolution:    0
% 11.83/2.00  res_clause_to_clause_subsumption:       11634
% 11.83/2.00  res_orphan_elimination:                 0
% 11.83/2.00  res_tautology_del:                      1036
% 11.83/2.00  res_num_eq_res_simplified:              1
% 11.83/2.00  res_num_sel_changes:                    0
% 11.83/2.00  res_moves_from_active_to_pass:          0
% 11.83/2.00  
% 11.83/2.00  ------ Superposition
% 11.83/2.00  
% 11.83/2.00  sup_time_total:                         0.
% 11.83/2.00  sup_time_generating:                    0.
% 11.83/2.00  sup_time_sim_full:                      0.
% 11.83/2.00  sup_time_sim_immed:                     0.
% 11.83/2.00  
% 11.83/2.00  sup_num_of_clauses:                     1983
% 11.83/2.00  sup_num_in_active:                      188
% 11.83/2.00  sup_num_in_passive:                     1795
% 11.83/2.00  sup_num_of_loops:                       540
% 11.83/2.00  sup_fw_superposition:                   1833
% 11.83/2.00  sup_bw_superposition:                   1858
% 11.83/2.00  sup_immediate_simplified:               1123
% 11.83/2.00  sup_given_eliminated:                   12
% 11.83/2.00  comparisons_done:                       0
% 11.83/2.00  comparisons_avoided:                    190
% 11.83/2.00  
% 11.83/2.00  ------ Simplifications
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  sim_fw_subset_subsumed:                 193
% 11.83/2.00  sim_bw_subset_subsumed:                 248
% 11.83/2.00  sim_fw_subsumed:                        317
% 11.83/2.00  sim_bw_subsumed:                        67
% 11.83/2.00  sim_fw_subsumption_res:                 0
% 11.83/2.00  sim_bw_subsumption_res:                 0
% 11.83/2.00  sim_tautology_del:                      144
% 11.83/2.00  sim_eq_tautology_del:                   279
% 11.83/2.00  sim_eq_res_simp:                        10
% 11.83/2.00  sim_fw_demodulated:                     529
% 11.83/2.00  sim_bw_demodulated:                     256
% 11.83/2.00  sim_light_normalised:                   487
% 11.83/2.00  sim_joinable_taut:                      0
% 11.83/2.00  sim_joinable_simp:                      0
% 11.83/2.00  sim_ac_normalised:                      0
% 11.83/2.00  sim_smt_subsumption:                    0
% 11.83/2.00  
%------------------------------------------------------------------------------
