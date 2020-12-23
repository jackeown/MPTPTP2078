%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:58 EST 2020

% Result     : Theorem 27.57s
% Output     : CNFRefutation 27.57s
% Verified   : 
% Statistics : Number of formulae       :  268 (1437 expanded)
%              Number of clauses        :  180 ( 584 expanded)
%              Number of leaves         :   24 ( 262 expanded)
%              Depth                    :   19
%              Number of atoms          :  821 (6304 expanded)
%              Number of equality atoms :  423 (1979 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f50,plain,
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

fof(f51,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f50])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f87,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f95,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1013,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_86557,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X2)
    | X2 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_98791,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),X1)
    | X0 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_86557])).

cnf(c_111032,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | X0 != sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_98791])).

cnf(c_111034,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_111032])).

cnf(c_16,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_95961,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_93580,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_87317,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_85712,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_85714,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_85712])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1711,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1721,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2761,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_1721])).

cnf(c_1718,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1725,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4335,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_relat_1(X0,X2),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_1725])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1722,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_13])).

cnf(c_1708,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_4302,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_1708])).

cnf(c_11541,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(X0,X3)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4335,c_4302])).

cnf(c_1720,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_82800,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(X0,X3)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11541,c_1720])).

cnf(c_82809,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_82800])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_265,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_266,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_266])).

cnf(c_1709,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_3120,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_1709])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1719,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3254,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3120,c_1719])).

cnf(c_4549,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4550,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4549])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1726,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11536,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k7_relat_1(X0,X3),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4335,c_1725])).

cnf(c_71091,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_11536])).

cnf(c_73114,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_71091,c_3254])).

cnf(c_73115,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_73114])).

cnf(c_73120,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_73115])).

cnf(c_75010,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_73120,c_4302])).

cnf(c_85146,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_82809,c_3254,c_4550,c_75010])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1712,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_636,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_638,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_35])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1715,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3260,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1711,c_1715])).

cnf(c_3649,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_638,c_3260])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1717,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4368,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_1717])).

cnf(c_5704,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4368,c_3254])).

cnf(c_5705,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5704])).

cnf(c_5716,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1712,c_5705])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1713,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5813,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5716,c_1713])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1714,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4581,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_1714])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2098,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4508,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_4799,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4581,c_37,c_35,c_4508])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_646,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_647,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_659,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_647,c_435])).

cnf(c_1699,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_4805,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4799,c_1699])).

cnf(c_5815,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5716,c_4805])).

cnf(c_7001,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5813,c_5815])).

cnf(c_85171,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_85146,c_7001])).

cnf(c_85331,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_85171])).

cnf(c_84955,plain,
    ( r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_84483,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_82102,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_40855,plain,
    ( ~ r1_tarski(X0,k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_40857,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_40855])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2006,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_40372,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_1012,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2145,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_40001,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_40005,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_40001])).

cnf(c_1019,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2106,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k7_relat_1(sK3,X1))
    | X0 != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_7989,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(k7_relat_1(sK3,X0))
    | k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_20173,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_7989])).

cnf(c_4303,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_1708])).

cnf(c_4652,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4303,c_3254])).

cnf(c_4657,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4652,c_1725])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_5115,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_1713])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6631,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5115,c_38,c_3254])).

cnf(c_6640,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_6631])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_113,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_115,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_2224,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_2225,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2224])).

cnf(c_2227,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2225])).

cnf(c_5114,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1713])).

cnf(c_5307,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4657,c_5114])).

cnf(c_7217,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6640,c_38,c_108,c_109,c_115,c_2227,c_3254,c_5307])).

cnf(c_7223,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4657,c_7217])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_36])).

cnf(c_515,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_1705,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_1819,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1705,c_6])).

cnf(c_2293,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2294,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2293])).

cnf(c_2341,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2344,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2341])).

cnf(c_2361,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2362,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2361])).

cnf(c_2364,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_2409,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1819,c_2294,c_2344,c_2364])).

cnf(c_7500,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7223,c_2409])).

cnf(c_7541,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7500])).

cnf(c_7499,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7223,c_1721])).

cnf(c_7540,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7499])).

cnf(c_22,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_462,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_463,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_1707,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1903,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1707,c_6])).

cnf(c_105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_107,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_2352,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1903,c_107,c_115])).

cnf(c_2353,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2352])).

cnf(c_4804,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4799,c_2353])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_114,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2041,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2272,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_2274,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2272])).

cnf(c_2062,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2319,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_1011,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2320,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_2749,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2750,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2749])).

cnf(c_2258,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2941,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_3541,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5419,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4804,c_34,c_33,c_108,c_109,c_114,c_2041,c_2274,c_2319,c_2320,c_2750,c_2941,c_3541])).

cnf(c_3255,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3254])).

cnf(c_2308,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_2226,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2136,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2063,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2064,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_665,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_111034,c_95961,c_93580,c_87317,c_85714,c_85331,c_84955,c_84483,c_82102,c_40857,c_40372,c_40005,c_20173,c_7541,c_7540,c_5419,c_3255,c_2750,c_2320,c_2319,c_2308,c_2226,c_2136,c_2064,c_665,c_114,c_109,c_108,c_33,c_35,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.57/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.57/3.99  
% 27.57/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.57/3.99  
% 27.57/3.99  ------  iProver source info
% 27.57/3.99  
% 27.57/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.57/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.57/3.99  git: non_committed_changes: false
% 27.57/3.99  git: last_make_outside_of_git: false
% 27.57/3.99  
% 27.57/3.99  ------ 
% 27.57/3.99  
% 27.57/3.99  ------ Input Options
% 27.57/3.99  
% 27.57/3.99  --out_options                           all
% 27.57/3.99  --tptp_safe_out                         true
% 27.57/3.99  --problem_path                          ""
% 27.57/3.99  --include_path                          ""
% 27.57/3.99  --clausifier                            res/vclausify_rel
% 27.57/3.99  --clausifier_options                    --mode clausify
% 27.57/3.99  --stdin                                 false
% 27.57/3.99  --stats_out                             all
% 27.57/3.99  
% 27.57/3.99  ------ General Options
% 27.57/3.99  
% 27.57/3.99  --fof                                   false
% 27.57/3.99  --time_out_real                         305.
% 27.57/3.99  --time_out_virtual                      -1.
% 27.57/3.99  --symbol_type_check                     false
% 27.57/3.99  --clausify_out                          false
% 27.57/3.99  --sig_cnt_out                           false
% 27.57/3.99  --trig_cnt_out                          false
% 27.57/3.99  --trig_cnt_out_tolerance                1.
% 27.57/3.99  --trig_cnt_out_sk_spl                   false
% 27.57/3.99  --abstr_cl_out                          false
% 27.57/3.99  
% 27.57/3.99  ------ Global Options
% 27.57/3.99  
% 27.57/3.99  --schedule                              default
% 27.57/3.99  --add_important_lit                     false
% 27.57/3.99  --prop_solver_per_cl                    1000
% 27.57/3.99  --min_unsat_core                        false
% 27.57/3.99  --soft_assumptions                      false
% 27.57/3.99  --soft_lemma_size                       3
% 27.57/3.99  --prop_impl_unit_size                   0
% 27.57/3.99  --prop_impl_unit                        []
% 27.57/3.99  --share_sel_clauses                     true
% 27.57/3.99  --reset_solvers                         false
% 27.57/3.99  --bc_imp_inh                            [conj_cone]
% 27.57/3.99  --conj_cone_tolerance                   3.
% 27.57/3.99  --extra_neg_conj                        none
% 27.57/3.99  --large_theory_mode                     true
% 27.57/3.99  --prolific_symb_bound                   200
% 27.57/3.99  --lt_threshold                          2000
% 27.57/3.99  --clause_weak_htbl                      true
% 27.57/3.99  --gc_record_bc_elim                     false
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing Options
% 27.57/3.99  
% 27.57/3.99  --preprocessing_flag                    true
% 27.57/3.99  --time_out_prep_mult                    0.1
% 27.57/3.99  --splitting_mode                        input
% 27.57/3.99  --splitting_grd                         true
% 27.57/3.99  --splitting_cvd                         false
% 27.57/3.99  --splitting_cvd_svl                     false
% 27.57/3.99  --splitting_nvd                         32
% 27.57/3.99  --sub_typing                            true
% 27.57/3.99  --prep_gs_sim                           true
% 27.57/3.99  --prep_unflatten                        true
% 27.57/3.99  --prep_res_sim                          true
% 27.57/3.99  --prep_upred                            true
% 27.57/3.99  --prep_sem_filter                       exhaustive
% 27.57/3.99  --prep_sem_filter_out                   false
% 27.57/3.99  --pred_elim                             true
% 27.57/3.99  --res_sim_input                         true
% 27.57/3.99  --eq_ax_congr_red                       true
% 27.57/3.99  --pure_diseq_elim                       true
% 27.57/3.99  --brand_transform                       false
% 27.57/3.99  --non_eq_to_eq                          false
% 27.57/3.99  --prep_def_merge                        true
% 27.57/3.99  --prep_def_merge_prop_impl              false
% 27.57/3.99  --prep_def_merge_mbd                    true
% 27.57/3.99  --prep_def_merge_tr_red                 false
% 27.57/3.99  --prep_def_merge_tr_cl                  false
% 27.57/3.99  --smt_preprocessing                     true
% 27.57/3.99  --smt_ac_axioms                         fast
% 27.57/3.99  --preprocessed_out                      false
% 27.57/3.99  --preprocessed_stats                    false
% 27.57/3.99  
% 27.57/3.99  ------ Abstraction refinement Options
% 27.57/3.99  
% 27.57/3.99  --abstr_ref                             []
% 27.57/3.99  --abstr_ref_prep                        false
% 27.57/3.99  --abstr_ref_until_sat                   false
% 27.57/3.99  --abstr_ref_sig_restrict                funpre
% 27.57/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.57/3.99  --abstr_ref_under                       []
% 27.57/3.99  
% 27.57/3.99  ------ SAT Options
% 27.57/3.99  
% 27.57/3.99  --sat_mode                              false
% 27.57/3.99  --sat_fm_restart_options                ""
% 27.57/3.99  --sat_gr_def                            false
% 27.57/3.99  --sat_epr_types                         true
% 27.57/3.99  --sat_non_cyclic_types                  false
% 27.57/3.99  --sat_finite_models                     false
% 27.57/3.99  --sat_fm_lemmas                         false
% 27.57/3.99  --sat_fm_prep                           false
% 27.57/3.99  --sat_fm_uc_incr                        true
% 27.57/3.99  --sat_out_model                         small
% 27.57/3.99  --sat_out_clauses                       false
% 27.57/3.99  
% 27.57/3.99  ------ QBF Options
% 27.57/3.99  
% 27.57/3.99  --qbf_mode                              false
% 27.57/3.99  --qbf_elim_univ                         false
% 27.57/3.99  --qbf_dom_inst                          none
% 27.57/3.99  --qbf_dom_pre_inst                      false
% 27.57/3.99  --qbf_sk_in                             false
% 27.57/3.99  --qbf_pred_elim                         true
% 27.57/3.99  --qbf_split                             512
% 27.57/3.99  
% 27.57/3.99  ------ BMC1 Options
% 27.57/3.99  
% 27.57/3.99  --bmc1_incremental                      false
% 27.57/3.99  --bmc1_axioms                           reachable_all
% 27.57/3.99  --bmc1_min_bound                        0
% 27.57/3.99  --bmc1_max_bound                        -1
% 27.57/3.99  --bmc1_max_bound_default                -1
% 27.57/3.99  --bmc1_symbol_reachability              true
% 27.57/3.99  --bmc1_property_lemmas                  false
% 27.57/3.99  --bmc1_k_induction                      false
% 27.57/3.99  --bmc1_non_equiv_states                 false
% 27.57/3.99  --bmc1_deadlock                         false
% 27.57/3.99  --bmc1_ucm                              false
% 27.57/3.99  --bmc1_add_unsat_core                   none
% 27.57/3.99  --bmc1_unsat_core_children              false
% 27.57/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.57/3.99  --bmc1_out_stat                         full
% 27.57/3.99  --bmc1_ground_init                      false
% 27.57/3.99  --bmc1_pre_inst_next_state              false
% 27.57/3.99  --bmc1_pre_inst_state                   false
% 27.57/3.99  --bmc1_pre_inst_reach_state             false
% 27.57/3.99  --bmc1_out_unsat_core                   false
% 27.57/3.99  --bmc1_aig_witness_out                  false
% 27.57/3.99  --bmc1_verbose                          false
% 27.57/3.99  --bmc1_dump_clauses_tptp                false
% 27.57/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.57/3.99  --bmc1_dump_file                        -
% 27.57/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.57/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.57/3.99  --bmc1_ucm_extend_mode                  1
% 27.57/3.99  --bmc1_ucm_init_mode                    2
% 27.57/3.99  --bmc1_ucm_cone_mode                    none
% 27.57/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.57/3.99  --bmc1_ucm_relax_model                  4
% 27.57/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.57/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.57/3.99  --bmc1_ucm_layered_model                none
% 27.57/3.99  --bmc1_ucm_max_lemma_size               10
% 27.57/3.99  
% 27.57/3.99  ------ AIG Options
% 27.57/3.99  
% 27.57/3.99  --aig_mode                              false
% 27.57/3.99  
% 27.57/3.99  ------ Instantiation Options
% 27.57/3.99  
% 27.57/3.99  --instantiation_flag                    true
% 27.57/3.99  --inst_sos_flag                         false
% 27.57/3.99  --inst_sos_phase                        true
% 27.57/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.57/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.57/3.99  --inst_lit_sel_side                     num_symb
% 27.57/3.99  --inst_solver_per_active                1400
% 27.57/3.99  --inst_solver_calls_frac                1.
% 27.57/3.99  --inst_passive_queue_type               priority_queues
% 27.57/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.57/3.99  --inst_passive_queues_freq              [25;2]
% 27.57/3.99  --inst_dismatching                      true
% 27.57/3.99  --inst_eager_unprocessed_to_passive     true
% 27.57/3.99  --inst_prop_sim_given                   true
% 27.57/3.99  --inst_prop_sim_new                     false
% 27.57/3.99  --inst_subs_new                         false
% 27.57/3.99  --inst_eq_res_simp                      false
% 27.57/3.99  --inst_subs_given                       false
% 27.57/3.99  --inst_orphan_elimination               true
% 27.57/3.99  --inst_learning_loop_flag               true
% 27.57/3.99  --inst_learning_start                   3000
% 27.57/3.99  --inst_learning_factor                  2
% 27.57/3.99  --inst_start_prop_sim_after_learn       3
% 27.57/3.99  --inst_sel_renew                        solver
% 27.57/3.99  --inst_lit_activity_flag                true
% 27.57/3.99  --inst_restr_to_given                   false
% 27.57/3.99  --inst_activity_threshold               500
% 27.57/3.99  --inst_out_proof                        true
% 27.57/3.99  
% 27.57/3.99  ------ Resolution Options
% 27.57/3.99  
% 27.57/3.99  --resolution_flag                       true
% 27.57/3.99  --res_lit_sel                           adaptive
% 27.57/3.99  --res_lit_sel_side                      none
% 27.57/3.99  --res_ordering                          kbo
% 27.57/3.99  --res_to_prop_solver                    active
% 27.57/3.99  --res_prop_simpl_new                    false
% 27.57/3.99  --res_prop_simpl_given                  true
% 27.57/3.99  --res_passive_queue_type                priority_queues
% 27.57/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.57/3.99  --res_passive_queues_freq               [15;5]
% 27.57/3.99  --res_forward_subs                      full
% 27.57/3.99  --res_backward_subs                     full
% 27.57/3.99  --res_forward_subs_resolution           true
% 27.57/3.99  --res_backward_subs_resolution          true
% 27.57/3.99  --res_orphan_elimination                true
% 27.57/3.99  --res_time_limit                        2.
% 27.57/3.99  --res_out_proof                         true
% 27.57/3.99  
% 27.57/3.99  ------ Superposition Options
% 27.57/3.99  
% 27.57/3.99  --superposition_flag                    true
% 27.57/3.99  --sup_passive_queue_type                priority_queues
% 27.57/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.57/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.57/3.99  --demod_completeness_check              fast
% 27.57/3.99  --demod_use_ground                      true
% 27.57/3.99  --sup_to_prop_solver                    passive
% 27.57/3.99  --sup_prop_simpl_new                    true
% 27.57/3.99  --sup_prop_simpl_given                  true
% 27.57/3.99  --sup_fun_splitting                     false
% 27.57/3.99  --sup_smt_interval                      50000
% 27.57/3.99  
% 27.57/3.99  ------ Superposition Simplification Setup
% 27.57/3.99  
% 27.57/3.99  --sup_indices_passive                   []
% 27.57/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.57/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.57/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.57/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.57/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.57/3.99  --sup_full_bw                           [BwDemod]
% 27.57/3.99  --sup_immed_triv                        [TrivRules]
% 27.57/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.57/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.57/3.99  --sup_immed_bw_main                     []
% 27.57/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.57/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.57/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.57/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.57/3.99  
% 27.57/3.99  ------ Combination Options
% 27.57/3.99  
% 27.57/3.99  --comb_res_mult                         3
% 27.57/3.99  --comb_sup_mult                         2
% 27.57/3.99  --comb_inst_mult                        10
% 27.57/3.99  
% 27.57/3.99  ------ Debug Options
% 27.57/3.99  
% 27.57/3.99  --dbg_backtrace                         false
% 27.57/3.99  --dbg_dump_prop_clauses                 false
% 27.57/3.99  --dbg_dump_prop_clauses_file            -
% 27.57/3.99  --dbg_out_stat                          false
% 27.57/3.99  ------ Parsing...
% 27.57/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.57/3.99  ------ Proving...
% 27.57/3.99  ------ Problem Properties 
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  clauses                                 35
% 27.57/3.99  conjectures                             4
% 27.57/3.99  EPR                                     9
% 27.57/3.99  Horn                                    30
% 27.57/3.99  unary                                   8
% 27.57/3.99  binary                                  8
% 27.57/3.99  lits                                    97
% 27.57/3.99  lits eq                                 35
% 27.57/3.99  fd_pure                                 0
% 27.57/3.99  fd_pseudo                               0
% 27.57/3.99  fd_cond                                 4
% 27.57/3.99  fd_pseudo_cond                          1
% 27.57/3.99  AC symbols                              0
% 27.57/3.99  
% 27.57/3.99  ------ Schedule dynamic 5 is on 
% 27.57/3.99  
% 27.57/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  ------ 
% 27.57/3.99  Current options:
% 27.57/3.99  ------ 
% 27.57/3.99  
% 27.57/3.99  ------ Input Options
% 27.57/3.99  
% 27.57/3.99  --out_options                           all
% 27.57/3.99  --tptp_safe_out                         true
% 27.57/3.99  --problem_path                          ""
% 27.57/3.99  --include_path                          ""
% 27.57/3.99  --clausifier                            res/vclausify_rel
% 27.57/3.99  --clausifier_options                    --mode clausify
% 27.57/3.99  --stdin                                 false
% 27.57/3.99  --stats_out                             all
% 27.57/3.99  
% 27.57/3.99  ------ General Options
% 27.57/3.99  
% 27.57/3.99  --fof                                   false
% 27.57/3.99  --time_out_real                         305.
% 27.57/3.99  --time_out_virtual                      -1.
% 27.57/3.99  --symbol_type_check                     false
% 27.57/3.99  --clausify_out                          false
% 27.57/3.99  --sig_cnt_out                           false
% 27.57/3.99  --trig_cnt_out                          false
% 27.57/3.99  --trig_cnt_out_tolerance                1.
% 27.57/3.99  --trig_cnt_out_sk_spl                   false
% 27.57/3.99  --abstr_cl_out                          false
% 27.57/3.99  
% 27.57/3.99  ------ Global Options
% 27.57/3.99  
% 27.57/3.99  --schedule                              default
% 27.57/3.99  --add_important_lit                     false
% 27.57/3.99  --prop_solver_per_cl                    1000
% 27.57/3.99  --min_unsat_core                        false
% 27.57/3.99  --soft_assumptions                      false
% 27.57/3.99  --soft_lemma_size                       3
% 27.57/3.99  --prop_impl_unit_size                   0
% 27.57/3.99  --prop_impl_unit                        []
% 27.57/3.99  --share_sel_clauses                     true
% 27.57/3.99  --reset_solvers                         false
% 27.57/3.99  --bc_imp_inh                            [conj_cone]
% 27.57/3.99  --conj_cone_tolerance                   3.
% 27.57/3.99  --extra_neg_conj                        none
% 27.57/3.99  --large_theory_mode                     true
% 27.57/3.99  --prolific_symb_bound                   200
% 27.57/3.99  --lt_threshold                          2000
% 27.57/3.99  --clause_weak_htbl                      true
% 27.57/3.99  --gc_record_bc_elim                     false
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing Options
% 27.57/3.99  
% 27.57/3.99  --preprocessing_flag                    true
% 27.57/3.99  --time_out_prep_mult                    0.1
% 27.57/3.99  --splitting_mode                        input
% 27.57/3.99  --splitting_grd                         true
% 27.57/3.99  --splitting_cvd                         false
% 27.57/3.99  --splitting_cvd_svl                     false
% 27.57/3.99  --splitting_nvd                         32
% 27.57/3.99  --sub_typing                            true
% 27.57/3.99  --prep_gs_sim                           true
% 27.57/3.99  --prep_unflatten                        true
% 27.57/3.99  --prep_res_sim                          true
% 27.57/3.99  --prep_upred                            true
% 27.57/3.99  --prep_sem_filter                       exhaustive
% 27.57/3.99  --prep_sem_filter_out                   false
% 27.57/3.99  --pred_elim                             true
% 27.57/3.99  --res_sim_input                         true
% 27.57/3.99  --eq_ax_congr_red                       true
% 27.57/3.99  --pure_diseq_elim                       true
% 27.57/3.99  --brand_transform                       false
% 27.57/3.99  --non_eq_to_eq                          false
% 27.57/3.99  --prep_def_merge                        true
% 27.57/3.99  --prep_def_merge_prop_impl              false
% 27.57/3.99  --prep_def_merge_mbd                    true
% 27.57/3.99  --prep_def_merge_tr_red                 false
% 27.57/3.99  --prep_def_merge_tr_cl                  false
% 27.57/3.99  --smt_preprocessing                     true
% 27.57/3.99  --smt_ac_axioms                         fast
% 27.57/3.99  --preprocessed_out                      false
% 27.57/3.99  --preprocessed_stats                    false
% 27.57/3.99  
% 27.57/3.99  ------ Abstraction refinement Options
% 27.57/3.99  
% 27.57/3.99  --abstr_ref                             []
% 27.57/3.99  --abstr_ref_prep                        false
% 27.57/3.99  --abstr_ref_until_sat                   false
% 27.57/3.99  --abstr_ref_sig_restrict                funpre
% 27.57/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.57/3.99  --abstr_ref_under                       []
% 27.57/3.99  
% 27.57/3.99  ------ SAT Options
% 27.57/3.99  
% 27.57/3.99  --sat_mode                              false
% 27.57/3.99  --sat_fm_restart_options                ""
% 27.57/3.99  --sat_gr_def                            false
% 27.57/3.99  --sat_epr_types                         true
% 27.57/3.99  --sat_non_cyclic_types                  false
% 27.57/3.99  --sat_finite_models                     false
% 27.57/3.99  --sat_fm_lemmas                         false
% 27.57/3.99  --sat_fm_prep                           false
% 27.57/3.99  --sat_fm_uc_incr                        true
% 27.57/3.99  --sat_out_model                         small
% 27.57/3.99  --sat_out_clauses                       false
% 27.57/3.99  
% 27.57/3.99  ------ QBF Options
% 27.57/3.99  
% 27.57/3.99  --qbf_mode                              false
% 27.57/3.99  --qbf_elim_univ                         false
% 27.57/3.99  --qbf_dom_inst                          none
% 27.57/3.99  --qbf_dom_pre_inst                      false
% 27.57/3.99  --qbf_sk_in                             false
% 27.57/3.99  --qbf_pred_elim                         true
% 27.57/3.99  --qbf_split                             512
% 27.57/3.99  
% 27.57/3.99  ------ BMC1 Options
% 27.57/3.99  
% 27.57/3.99  --bmc1_incremental                      false
% 27.57/3.99  --bmc1_axioms                           reachable_all
% 27.57/3.99  --bmc1_min_bound                        0
% 27.57/3.99  --bmc1_max_bound                        -1
% 27.57/3.99  --bmc1_max_bound_default                -1
% 27.57/3.99  --bmc1_symbol_reachability              true
% 27.57/3.99  --bmc1_property_lemmas                  false
% 27.57/3.99  --bmc1_k_induction                      false
% 27.57/3.99  --bmc1_non_equiv_states                 false
% 27.57/3.99  --bmc1_deadlock                         false
% 27.57/3.99  --bmc1_ucm                              false
% 27.57/3.99  --bmc1_add_unsat_core                   none
% 27.57/3.99  --bmc1_unsat_core_children              false
% 27.57/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.57/3.99  --bmc1_out_stat                         full
% 27.57/3.99  --bmc1_ground_init                      false
% 27.57/3.99  --bmc1_pre_inst_next_state              false
% 27.57/3.99  --bmc1_pre_inst_state                   false
% 27.57/3.99  --bmc1_pre_inst_reach_state             false
% 27.57/3.99  --bmc1_out_unsat_core                   false
% 27.57/3.99  --bmc1_aig_witness_out                  false
% 27.57/3.99  --bmc1_verbose                          false
% 27.57/3.99  --bmc1_dump_clauses_tptp                false
% 27.57/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.57/3.99  --bmc1_dump_file                        -
% 27.57/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.57/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.57/3.99  --bmc1_ucm_extend_mode                  1
% 27.57/3.99  --bmc1_ucm_init_mode                    2
% 27.57/3.99  --bmc1_ucm_cone_mode                    none
% 27.57/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.57/3.99  --bmc1_ucm_relax_model                  4
% 27.57/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.57/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.57/3.99  --bmc1_ucm_layered_model                none
% 27.57/3.99  --bmc1_ucm_max_lemma_size               10
% 27.57/3.99  
% 27.57/3.99  ------ AIG Options
% 27.57/3.99  
% 27.57/3.99  --aig_mode                              false
% 27.57/3.99  
% 27.57/3.99  ------ Instantiation Options
% 27.57/3.99  
% 27.57/3.99  --instantiation_flag                    true
% 27.57/3.99  --inst_sos_flag                         false
% 27.57/3.99  --inst_sos_phase                        true
% 27.57/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.57/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.57/3.99  --inst_lit_sel_side                     none
% 27.57/3.99  --inst_solver_per_active                1400
% 27.57/3.99  --inst_solver_calls_frac                1.
% 27.57/3.99  --inst_passive_queue_type               priority_queues
% 27.57/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.57/3.99  --inst_passive_queues_freq              [25;2]
% 27.57/3.99  --inst_dismatching                      true
% 27.57/3.99  --inst_eager_unprocessed_to_passive     true
% 27.57/3.99  --inst_prop_sim_given                   true
% 27.57/3.99  --inst_prop_sim_new                     false
% 27.57/3.99  --inst_subs_new                         false
% 27.57/3.99  --inst_eq_res_simp                      false
% 27.57/3.99  --inst_subs_given                       false
% 27.57/3.99  --inst_orphan_elimination               true
% 27.57/3.99  --inst_learning_loop_flag               true
% 27.57/3.99  --inst_learning_start                   3000
% 27.57/3.99  --inst_learning_factor                  2
% 27.57/3.99  --inst_start_prop_sim_after_learn       3
% 27.57/3.99  --inst_sel_renew                        solver
% 27.57/3.99  --inst_lit_activity_flag                true
% 27.57/3.99  --inst_restr_to_given                   false
% 27.57/3.99  --inst_activity_threshold               500
% 27.57/3.99  --inst_out_proof                        true
% 27.57/3.99  
% 27.57/3.99  ------ Resolution Options
% 27.57/3.99  
% 27.57/3.99  --resolution_flag                       false
% 27.57/3.99  --res_lit_sel                           adaptive
% 27.57/3.99  --res_lit_sel_side                      none
% 27.57/3.99  --res_ordering                          kbo
% 27.57/3.99  --res_to_prop_solver                    active
% 27.57/3.99  --res_prop_simpl_new                    false
% 27.57/3.99  --res_prop_simpl_given                  true
% 27.57/3.99  --res_passive_queue_type                priority_queues
% 27.57/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.57/3.99  --res_passive_queues_freq               [15;5]
% 27.57/3.99  --res_forward_subs                      full
% 27.57/3.99  --res_backward_subs                     full
% 27.57/3.99  --res_forward_subs_resolution           true
% 27.57/3.99  --res_backward_subs_resolution          true
% 27.57/3.99  --res_orphan_elimination                true
% 27.57/3.99  --res_time_limit                        2.
% 27.57/3.99  --res_out_proof                         true
% 27.57/3.99  
% 27.57/3.99  ------ Superposition Options
% 27.57/3.99  
% 27.57/3.99  --superposition_flag                    true
% 27.57/3.99  --sup_passive_queue_type                priority_queues
% 27.57/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.57/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.57/3.99  --demod_completeness_check              fast
% 27.57/3.99  --demod_use_ground                      true
% 27.57/3.99  --sup_to_prop_solver                    passive
% 27.57/3.99  --sup_prop_simpl_new                    true
% 27.57/3.99  --sup_prop_simpl_given                  true
% 27.57/3.99  --sup_fun_splitting                     false
% 27.57/3.99  --sup_smt_interval                      50000
% 27.57/3.99  
% 27.57/3.99  ------ Superposition Simplification Setup
% 27.57/3.99  
% 27.57/3.99  --sup_indices_passive                   []
% 27.57/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.57/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.57/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.57/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.57/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.57/3.99  --sup_full_bw                           [BwDemod]
% 27.57/3.99  --sup_immed_triv                        [TrivRules]
% 27.57/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.57/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.57/3.99  --sup_immed_bw_main                     []
% 27.57/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.57/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.57/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.57/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.57/3.99  
% 27.57/3.99  ------ Combination Options
% 27.57/3.99  
% 27.57/3.99  --comb_res_mult                         3
% 27.57/3.99  --comb_sup_mult                         2
% 27.57/3.99  --comb_inst_mult                        10
% 27.57/3.99  
% 27.57/3.99  ------ Debug Options
% 27.57/3.99  
% 27.57/3.99  --dbg_backtrace                         false
% 27.57/3.99  --dbg_dump_prop_clauses                 false
% 27.57/3.99  --dbg_dump_prop_clauses_file            -
% 27.57/3.99  --dbg_out_stat                          false
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  ------ Proving...
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  % SZS status Theorem for theBenchmark.p
% 27.57/3.99  
% 27.57/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.57/3.99  
% 27.57/3.99  fof(f11,axiom,(
% 27.57/3.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f28,plain,(
% 27.57/3.99    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 27.57/3.99    inference(ennf_transformation,[],[f11])).
% 27.57/3.99  
% 27.57/3.99  fof(f68,plain,(
% 27.57/3.99    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f28])).
% 27.57/3.99  
% 27.57/3.99  fof(f9,axiom,(
% 27.57/3.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f27,plain,(
% 27.57/3.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 27.57/3.99    inference(ennf_transformation,[],[f9])).
% 27.57/3.99  
% 27.57/3.99  fof(f66,plain,(
% 27.57/3.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f27])).
% 27.57/3.99  
% 27.57/3.99  fof(f3,axiom,(
% 27.57/3.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f56,plain,(
% 27.57/3.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f3])).
% 27.57/3.99  
% 27.57/3.99  fof(f2,axiom,(
% 27.57/3.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f22,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.57/3.99    inference(ennf_transformation,[],[f2])).
% 27.57/3.99  
% 27.57/3.99  fof(f23,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 27.57/3.99    inference(flattening,[],[f22])).
% 27.57/3.99  
% 27.57/3.99  fof(f55,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f23])).
% 27.57/3.99  
% 27.57/3.99  fof(f19,conjecture,(
% 27.57/3.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f20,negated_conjecture,(
% 27.57/3.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 27.57/3.99    inference(negated_conjecture,[],[f19])).
% 27.57/3.99  
% 27.57/3.99  fof(f41,plain,(
% 27.57/3.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 27.57/3.99    inference(ennf_transformation,[],[f20])).
% 27.57/3.99  
% 27.57/3.99  fof(f42,plain,(
% 27.57/3.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 27.57/3.99    inference(flattening,[],[f41])).
% 27.57/3.99  
% 27.57/3.99  fof(f50,plain,(
% 27.57/3.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 27.57/3.99    introduced(choice_axiom,[])).
% 27.57/3.99  
% 27.57/3.99  fof(f51,plain,(
% 27.57/3.99    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 27.57/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f50])).
% 27.57/3.99  
% 27.57/3.99  fof(f86,plain,(
% 27.57/3.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.57/3.99    inference(cnf_transformation,[],[f51])).
% 27.57/3.99  
% 27.57/3.99  fof(f6,axiom,(
% 27.57/3.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f47,plain,(
% 27.57/3.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.57/3.99    inference(nnf_transformation,[],[f6])).
% 27.57/3.99  
% 27.57/3.99  fof(f61,plain,(
% 27.57/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.57/3.99    inference(cnf_transformation,[],[f47])).
% 27.57/3.99  
% 27.57/3.99  fof(f62,plain,(
% 27.57/3.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f47])).
% 27.57/3.99  
% 27.57/3.99  fof(f14,axiom,(
% 27.57/3.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f21,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 27.57/3.99    inference(pure_predicate_removal,[],[f14])).
% 27.57/3.99  
% 27.57/3.99  fof(f33,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.57/3.99    inference(ennf_transformation,[],[f21])).
% 27.57/3.99  
% 27.57/3.99  fof(f72,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.57/3.99    inference(cnf_transformation,[],[f33])).
% 27.57/3.99  
% 27.57/3.99  fof(f8,axiom,(
% 27.57/3.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f26,plain,(
% 27.57/3.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.57/3.99    inference(ennf_transformation,[],[f8])).
% 27.57/3.99  
% 27.57/3.99  fof(f48,plain,(
% 27.57/3.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 27.57/3.99    inference(nnf_transformation,[],[f26])).
% 27.57/3.99  
% 27.57/3.99  fof(f64,plain,(
% 27.57/3.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f48])).
% 27.57/3.99  
% 27.57/3.99  fof(f7,axiom,(
% 27.57/3.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f25,plain,(
% 27.57/3.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.57/3.99    inference(ennf_transformation,[],[f7])).
% 27.57/3.99  
% 27.57/3.99  fof(f63,plain,(
% 27.57/3.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f25])).
% 27.57/3.99  
% 27.57/3.99  fof(f10,axiom,(
% 27.57/3.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f67,plain,(
% 27.57/3.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.57/3.99    inference(cnf_transformation,[],[f10])).
% 27.57/3.99  
% 27.57/3.99  fof(f1,axiom,(
% 27.57/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f43,plain,(
% 27.57/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.57/3.99    inference(nnf_transformation,[],[f1])).
% 27.57/3.99  
% 27.57/3.99  fof(f44,plain,(
% 27.57/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.57/3.99    inference(flattening,[],[f43])).
% 27.57/3.99  
% 27.57/3.99  fof(f53,plain,(
% 27.57/3.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 27.57/3.99    inference(cnf_transformation,[],[f44])).
% 27.57/3.99  
% 27.57/3.99  fof(f90,plain,(
% 27.57/3.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.57/3.99    inference(equality_resolution,[],[f53])).
% 27.57/3.99  
% 27.57/3.99  fof(f87,plain,(
% 27.57/3.99    r1_tarski(sK2,sK0)),
% 27.57/3.99    inference(cnf_transformation,[],[f51])).
% 27.57/3.99  
% 27.57/3.99  fof(f16,axiom,(
% 27.57/3.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f35,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.57/3.99    inference(ennf_transformation,[],[f16])).
% 27.57/3.99  
% 27.57/3.99  fof(f36,plain,(
% 27.57/3.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.57/3.99    inference(flattening,[],[f35])).
% 27.57/3.99  
% 27.57/3.99  fof(f49,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.57/3.99    inference(nnf_transformation,[],[f36])).
% 27.57/3.99  
% 27.57/3.99  fof(f74,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.57/3.99    inference(cnf_transformation,[],[f49])).
% 27.57/3.99  
% 27.57/3.99  fof(f85,plain,(
% 27.57/3.99    v1_funct_2(sK3,sK0,sK1)),
% 27.57/3.99    inference(cnf_transformation,[],[f51])).
% 27.57/3.99  
% 27.57/3.99  fof(f15,axiom,(
% 27.57/3.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f34,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.57/3.99    inference(ennf_transformation,[],[f15])).
% 27.57/3.99  
% 27.57/3.99  fof(f73,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.57/3.99    inference(cnf_transformation,[],[f34])).
% 27.57/3.99  
% 27.57/3.99  fof(f12,axiom,(
% 27.57/3.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f29,plain,(
% 27.57/3.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 27.57/3.99    inference(ennf_transformation,[],[f12])).
% 27.57/3.99  
% 27.57/3.99  fof(f30,plain,(
% 27.57/3.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 27.57/3.99    inference(flattening,[],[f29])).
% 27.57/3.99  
% 27.57/3.99  fof(f69,plain,(
% 27.57/3.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f30])).
% 27.57/3.99  
% 27.57/3.99  fof(f18,axiom,(
% 27.57/3.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f39,plain,(
% 27.57/3.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 27.57/3.99    inference(ennf_transformation,[],[f18])).
% 27.57/3.99  
% 27.57/3.99  fof(f40,plain,(
% 27.57/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.57/3.99    inference(flattening,[],[f39])).
% 27.57/3.99  
% 27.57/3.99  fof(f83,plain,(
% 27.57/3.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f40])).
% 27.57/3.99  
% 27.57/3.99  fof(f17,axiom,(
% 27.57/3.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f37,plain,(
% 27.57/3.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 27.57/3.99    inference(ennf_transformation,[],[f17])).
% 27.57/3.99  
% 27.57/3.99  fof(f38,plain,(
% 27.57/3.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 27.57/3.99    inference(flattening,[],[f37])).
% 27.57/3.99  
% 27.57/3.99  fof(f80,plain,(
% 27.57/3.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f38])).
% 27.57/3.99  
% 27.57/3.99  fof(f84,plain,(
% 27.57/3.99    v1_funct_1(sK3)),
% 27.57/3.99    inference(cnf_transformation,[],[f51])).
% 27.57/3.99  
% 27.57/3.99  fof(f82,plain,(
% 27.57/3.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f40])).
% 27.57/3.99  
% 27.57/3.99  fof(f89,plain,(
% 27.57/3.99    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 27.57/3.99    inference(cnf_transformation,[],[f51])).
% 27.57/3.99  
% 27.57/3.99  fof(f54,plain,(
% 27.57/3.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f44])).
% 27.57/3.99  
% 27.57/3.99  fof(f13,axiom,(
% 27.57/3.99    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f31,plain,(
% 27.57/3.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.57/3.99    inference(ennf_transformation,[],[f13])).
% 27.57/3.99  
% 27.57/3.99  fof(f32,plain,(
% 27.57/3.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.57/3.99    inference(flattening,[],[f31])).
% 27.57/3.99  
% 27.57/3.99  fof(f71,plain,(
% 27.57/3.99    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f32])).
% 27.57/3.99  
% 27.57/3.99  fof(f5,axiom,(
% 27.57/3.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f45,plain,(
% 27.57/3.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 27.57/3.99    inference(nnf_transformation,[],[f5])).
% 27.57/3.99  
% 27.57/3.99  fof(f46,plain,(
% 27.57/3.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 27.57/3.99    inference(flattening,[],[f45])).
% 27.57/3.99  
% 27.57/3.99  fof(f60,plain,(
% 27.57/3.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 27.57/3.99    inference(cnf_transformation,[],[f46])).
% 27.57/3.99  
% 27.57/3.99  fof(f92,plain,(
% 27.57/3.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 27.57/3.99    inference(equality_resolution,[],[f60])).
% 27.57/3.99  
% 27.57/3.99  fof(f58,plain,(
% 27.57/3.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f46])).
% 27.57/3.99  
% 27.57/3.99  fof(f59,plain,(
% 27.57/3.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 27.57/3.99    inference(cnf_transformation,[],[f46])).
% 27.57/3.99  
% 27.57/3.99  fof(f93,plain,(
% 27.57/3.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 27.57/3.99    inference(equality_resolution,[],[f59])).
% 27.57/3.99  
% 27.57/3.99  fof(f78,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.57/3.99    inference(cnf_transformation,[],[f49])).
% 27.57/3.99  
% 27.57/3.99  fof(f96,plain,(
% 27.57/3.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 27.57/3.99    inference(equality_resolution,[],[f78])).
% 27.57/3.99  
% 27.57/3.99  fof(f79,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.57/3.99    inference(cnf_transformation,[],[f49])).
% 27.57/3.99  
% 27.57/3.99  fof(f94,plain,(
% 27.57/3.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.57/3.99    inference(equality_resolution,[],[f79])).
% 27.57/3.99  
% 27.57/3.99  fof(f95,plain,(
% 27.57/3.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 27.57/3.99    inference(equality_resolution,[],[f94])).
% 27.57/3.99  
% 27.57/3.99  fof(f88,plain,(
% 27.57/3.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 27.57/3.99    inference(cnf_transformation,[],[f51])).
% 27.57/3.99  
% 27.57/3.99  fof(f4,axiom,(
% 27.57/3.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f24,plain,(
% 27.57/3.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 27.57/3.99    inference(ennf_transformation,[],[f4])).
% 27.57/3.99  
% 27.57/3.99  fof(f57,plain,(
% 27.57/3.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f24])).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1013,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.57/3.99      theory(equality) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_86557,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1)
% 27.57/3.99      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X2)
% 27.57/3.99      | X2 != X1
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1013]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_98791,plain,
% 27.57/3.99      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 27.57/3.99      | ~ r1_tarski(k7_relat_1(sK3,sK2),X1)
% 27.57/3.99      | X0 != X1
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_86557]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_111032,plain,
% 27.57/3.99      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 27.57/3.99      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 27.57/3.99      | X0 != sK3
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_98791]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_111034,plain,
% 27.57/3.99      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 27.57/3.99      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 27.57/3.99      | k1_xboole_0 != sK3 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_111032]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_16,plain,
% 27.57/3.99      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f68]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_95961,plain,
% 27.57/3.99      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~ v1_relat_1(sK3) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_16]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_14,plain,
% 27.57/3.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f66]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_93580,plain,
% 27.57/3.99      ( v1_relat_1(k7_relat_1(sK3,sK2)) | ~ v1_relat_1(sK3) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_14]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f56]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_87317,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 27.57/3.99      inference(cnf_transformation,[],[f55]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_85712,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
% 27.57/3.99      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 27.57/3.99      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_3]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_85714,plain,
% 27.57/3.99      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 27.57/3.99      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 27.57/3.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_85712]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_35,negated_conjecture,
% 27.57/3.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.57/3.99      inference(cnf_transformation,[],[f86]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1711,plain,
% 27.57/3.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_10,plain,
% 27.57/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1721,plain,
% 27.57/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.57/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2761,plain,
% 27.57/3.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_1711,c_1721]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1718,plain,
% 27.57/3.99      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1725,plain,
% 27.57/3.99      ( r1_tarski(X0,X1) != iProver_top
% 27.57/3.99      | r1_tarski(X1,X2) != iProver_top
% 27.57/3.99      | r1_tarski(X0,X2) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4335,plain,
% 27.57/3.99      ( r1_tarski(X0,X1) != iProver_top
% 27.57/3.99      | r1_tarski(k7_relat_1(X0,X2),X1) = iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_1718,c_1725]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_9,plain,
% 27.57/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1722,plain,
% 27.57/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 27.57/3.99      | r1_tarski(X0,X1) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_20,plain,
% 27.57/3.99      ( v5_relat_1(X0,X1)
% 27.57/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 27.57/3.99      inference(cnf_transformation,[],[f72]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_13,plain,
% 27.57/3.99      ( ~ v5_relat_1(X0,X1)
% 27.57/3.99      | r1_tarski(k2_relat_1(X0),X1)
% 27.57/3.99      | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f64]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_435,plain,
% 27.57/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.57/3.99      | r1_tarski(k2_relat_1(X0),X2)
% 27.57/3.99      | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(resolution,[status(thm)],[c_20,c_13]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1708,plain,
% 27.57/3.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4302,plain,
% 27.57/3.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_1722,c_1708]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_11541,plain,
% 27.57/3.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(k7_relat_1(X0,X3)),X2) = iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top
% 27.57/3.99      | v1_relat_1(k7_relat_1(X0,X3)) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4335,c_4302]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1720,plain,
% 27.57/3.99      ( v1_relat_1(X0) != iProver_top
% 27.57/3.99      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_82800,plain,
% 27.57/3.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(k7_relat_1(X0,X3)),X2) = iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(forward_subsumption_resolution,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_11541,c_1720]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_82809,plain,
% 27.57/3.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 27.57/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_2761,c_82800]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_11,plain,
% 27.57/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.57/3.99      | ~ v1_relat_1(X1)
% 27.57/3.99      | v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f63]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_265,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.57/3.99      inference(prop_impl,[status(thm)],[c_9]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_266,plain,
% 27.57/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_265]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_328,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 27.57/3.99      inference(bin_hyper_res,[status(thm)],[c_11,c_266]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1709,plain,
% 27.57/3.99      ( r1_tarski(X0,X1) != iProver_top
% 27.57/3.99      | v1_relat_1(X1) != iProver_top
% 27.57/3.99      | v1_relat_1(X0) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3120,plain,
% 27.57/3.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 27.57/3.99      | v1_relat_1(sK3) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_2761,c_1709]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_15,plain,
% 27.57/3.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f67]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1719,plain,
% 27.57/3.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3254,plain,
% 27.57/3.99      ( v1_relat_1(sK3) = iProver_top ),
% 27.57/3.99      inference(forward_subsumption_resolution,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_3120,c_1719]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4549,plain,
% 27.57/3.99      ( v1_relat_1(k7_relat_1(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_14]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4550,plain,
% 27.57/3.99      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 27.57/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_4549]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1,plain,
% 27.57/3.99      ( r1_tarski(X0,X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f90]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1726,plain,
% 27.57/3.99      ( r1_tarski(X0,X0) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_11536,plain,
% 27.57/3.99      ( r1_tarski(X0,X1) != iProver_top
% 27.57/3.99      | r1_tarski(X1,X2) != iProver_top
% 27.57/3.99      | r1_tarski(k7_relat_1(X0,X3),X2) = iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4335,c_1725]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_71091,plain,
% 27.57/3.99      ( r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top
% 27.57/3.99      | r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top
% 27.57/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_2761,c_11536]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_73114,plain,
% 27.57/3.99      ( r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top
% 27.57/3.99      | r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_71091,c_3254]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_73115,plain,
% 27.57/3.99      ( r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top
% 27.57/3.99      | r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_73114]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_73120,plain,
% 27.57/3.99      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_1726,c_73115]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_75010,plain,
% 27.57/3.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 27.57/3.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_73120,c_4302]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_85146,plain,
% 27.57/3.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_82809,c_3254,c_4550,c_75010]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_34,negated_conjecture,
% 27.57/3.99      ( r1_tarski(sK2,sK0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f87]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1712,plain,
% 27.57/3.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_27,plain,
% 27.57/3.99      ( ~ v1_funct_2(X0,X1,X2)
% 27.57/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.57/3.99      | k1_relset_1(X1,X2,X0) = X1
% 27.57/3.99      | k1_xboole_0 = X2 ),
% 27.57/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_36,negated_conjecture,
% 27.57/3.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f85]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_635,plain,
% 27.57/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.57/3.99      | k1_relset_1(X1,X2,X0) = X1
% 27.57/3.99      | sK3 != X0
% 27.57/3.99      | sK1 != X2
% 27.57/3.99      | sK0 != X1
% 27.57/3.99      | k1_xboole_0 = X2 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_636,plain,
% 27.57/3.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.57/3.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 27.57/3.99      | k1_xboole_0 = sK1 ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_635]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_638,plain,
% 27.57/3.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_636,c_35]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_21,plain,
% 27.57/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.57/3.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1715,plain,
% 27.57/3.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 27.57/3.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3260,plain,
% 27.57/3.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_1711,c_1715]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3649,plain,
% 27.57/3.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_638,c_3260]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_17,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 27.57/3.99      | ~ v1_relat_1(X1)
% 27.57/3.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 27.57/3.99      inference(cnf_transformation,[],[f69]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1717,plain,
% 27.57/3.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 27.57/3.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4368,plain,
% 27.57/3.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 27.57/3.99      | sK1 = k1_xboole_0
% 27.57/3.99      | r1_tarski(X0,sK0) != iProver_top
% 27.57/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_3649,c_1717]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5704,plain,
% 27.57/3.99      ( r1_tarski(X0,sK0) != iProver_top
% 27.57/3.99      | sK1 = k1_xboole_0
% 27.57/3.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_4368,c_3254]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5705,plain,
% 27.57/3.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 27.57/3.99      | sK1 = k1_xboole_0
% 27.57/3.99      | r1_tarski(X0,sK0) != iProver_top ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_5704]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5716,plain,
% 27.57/3.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_1712,c_5705]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_29,plain,
% 27.57/3.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 27.57/3.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 27.57/3.99      | ~ v1_funct_1(X0)
% 27.57/3.99      | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f83]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1713,plain,
% 27.57/3.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 27.57/3.99      | v1_funct_1(X0) != iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5813,plain,
% 27.57/3.99      ( sK1 = k1_xboole_0
% 27.57/3.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 27.57/3.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 27.57/3.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_5716,c_1713]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_28,plain,
% 27.57/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.57/3.99      | ~ v1_funct_1(X0)
% 27.57/3.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 27.57/3.99      inference(cnf_transformation,[],[f80]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1714,plain,
% 27.57/3.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 27.57/3.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.57/3.99      | v1_funct_1(X2) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4581,plain,
% 27.57/3.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 27.57/3.99      | v1_funct_1(sK3) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_1711,c_1714]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_37,negated_conjecture,
% 27.57/3.99      ( v1_funct_1(sK3) ),
% 27.57/3.99      inference(cnf_transformation,[],[f84]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2098,plain,
% 27.57/3.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.57/3.99      | ~ v1_funct_1(sK3)
% 27.57/3.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_28]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4508,plain,
% 27.57/3.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.57/3.99      | ~ v1_funct_1(sK3)
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2098]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4799,plain,
% 27.57/3.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_4581,c_37,c_35,c_4508]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_30,plain,
% 27.57/3.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 27.57/3.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 27.57/3.99      | ~ v1_funct_1(X0)
% 27.57/3.99      | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f82]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_32,negated_conjecture,
% 27.57/3.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 27.57/3.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.57/3.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f89]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_646,plain,
% 27.57/3.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.57/3.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 27.57/3.99      | ~ v1_funct_1(X0)
% 27.57/3.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/3.99      | ~ v1_relat_1(X0)
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 27.57/3.99      | k1_relat_1(X0) != sK2
% 27.57/3.99      | sK1 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_647,plain,
% 27.57/3.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.57/3.99      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 27.57/3.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/3.99      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/3.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_646]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_659,plain,
% 27.57/3.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.57/3.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/3.99      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/3.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 27.57/3.99      inference(forward_subsumption_resolution,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_647,c_435]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1699,plain,
% 27.57/3.99      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 27.57/3.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.57/3.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 27.57/3.99      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4805,plain,
% 27.57/3.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 27.57/3.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.57/3.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 27.57/3.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 27.57/3.99      inference(demodulation,[status(thm)],[c_4799,c_1699]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5815,plain,
% 27.57/3.99      ( sK1 = k1_xboole_0
% 27.57/3.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.57/3.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 27.57/3.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_5716,c_4805]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_7001,plain,
% 27.57/3.99      ( sK1 = k1_xboole_0
% 27.57/3.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 27.57/3.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 27.57/3.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_5813,c_5815]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_85171,plain,
% 27.57/3.99      ( sK1 = k1_xboole_0
% 27.57/3.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 27.57/3.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_85146,c_7001]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_85331,plain,
% 27.57/3.99      ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
% 27.57/3.99      | ~ v1_relat_1(k7_relat_1(sK3,sK2))
% 27.57/3.99      | sK1 = k1_xboole_0 ),
% 27.57/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_85171]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_84955,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_84483,plain,
% 27.57/3.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.57/3.99      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_9]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_82102,plain,
% 27.57/3.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.57/3.99      | ~ v1_funct_1(sK3)
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_28]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_0,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.57/3.99      inference(cnf_transformation,[],[f54]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_40855,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/3.99      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_40857,plain,
% 27.57/3.99      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 27.57/3.99      | ~ r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_40855]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_18,plain,
% 27.57/3.99      ( ~ v1_funct_1(X0)
% 27.57/3.99      | v1_funct_1(k7_relat_1(X0,X1))
% 27.57/3.99      | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f71]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2006,plain,
% 27.57/3.99      ( v1_funct_1(k7_relat_1(sK3,X0))
% 27.57/3.99      | ~ v1_funct_1(sK3)
% 27.57/3.99      | ~ v1_relat_1(sK3) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_18]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_40372,plain,
% 27.57/3.99      ( v1_funct_1(k7_relat_1(sK3,sK2))
% 27.57/3.99      | ~ v1_funct_1(sK3)
% 27.57/3.99      | ~ v1_relat_1(sK3) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2006]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1012,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2145,plain,
% 27.57/3.99      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1012]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_40001,plain,
% 27.57/3.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 27.57/3.99      | sK3 != X0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2145]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_40005,plain,
% 27.57/3.99      ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 27.57/3.99      | sK3 != k1_xboole_0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_40001]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1019,plain,
% 27.57/3.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 27.57/3.99      theory(equality) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2106,plain,
% 27.57/3.99      ( v1_funct_1(X0)
% 27.57/3.99      | ~ v1_funct_1(k7_relat_1(sK3,X1))
% 27.57/3.99      | X0 != k7_relat_1(sK3,X1) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1019]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_7989,plain,
% 27.57/3.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 27.57/3.99      | ~ v1_funct_1(k7_relat_1(sK3,X0))
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2106]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_20173,plain,
% 27.57/3.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/3.99      | ~ v1_funct_1(k7_relat_1(sK3,sK2))
% 27.57/3.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_7989]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4303,plain,
% 27.57/3.99      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 27.57/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_1711,c_1708]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4652,plain,
% 27.57/3.99      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_4303,c_3254]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4657,plain,
% 27.57/3.99      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 27.57/3.99      | r1_tarski(sK1,X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4652,c_1725]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_6,plain,
% 27.57/3.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.57/3.99      inference(cnf_transformation,[],[f92]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5115,plain,
% 27.57/3.99      ( sK1 = k1_xboole_0
% 27.57/3.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 27.57/3.99      | v1_funct_1(sK3) != iProver_top
% 27.57/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_3649,c_1713]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_38,plain,
% 27.57/3.99      ( v1_funct_1(sK3) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_6631,plain,
% 27.57/3.99      ( sK1 = k1_xboole_0
% 27.57/3.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_5115,c_38,c_3254]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_6640,plain,
% 27.57/3.99      ( sK1 = k1_xboole_0
% 27.57/3.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_6,c_6631]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_8,plain,
% 27.57/3.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 27.57/3.99      | k1_xboole_0 = X0
% 27.57/3.99      | k1_xboole_0 = X1 ),
% 27.57/3.99      inference(cnf_transformation,[],[f58]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_108,plain,
% 27.57/3.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 27.57/3.99      | k1_xboole_0 = k1_xboole_0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_8]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_7,plain,
% 27.57/3.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.57/3.99      inference(cnf_transformation,[],[f93]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_109,plain,
% 27.57/3.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_7]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_113,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_115,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_113]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2224,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1)
% 27.57/3.99      | r1_tarski(sK1,k1_xboole_0)
% 27.57/3.99      | sK1 != X0
% 27.57/3.99      | k1_xboole_0 != X1 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1013]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2225,plain,
% 27.57/3.99      ( sK1 != X0
% 27.57/3.99      | k1_xboole_0 != X1
% 27.57/3.99      | r1_tarski(X0,X1) != iProver_top
% 27.57/3.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_2224]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2227,plain,
% 27.57/3.99      ( sK1 != k1_xboole_0
% 27.57/3.99      | k1_xboole_0 != k1_xboole_0
% 27.57/3.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 27.57/3.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2225]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5114,plain,
% 27.57/3.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 27.57/3.99      | v1_funct_1(X0) != iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_6,c_1713]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5307,plain,
% 27.57/3.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 27.57/3.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 27.57/3.99      | v1_funct_1(sK3) != iProver_top
% 27.57/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4657,c_5114]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_7217,plain,
% 27.57/3.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 27.57/3.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_6640,c_38,c_108,c_109,c_115,c_2227,c_3254,c_5307]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_7223,plain,
% 27.57/3.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 27.57/3.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4657,c_7217]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23,plain,
% 27.57/3.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 27.57/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 27.57/3.99      | k1_xboole_0 = X1
% 27.57/3.99      | k1_xboole_0 = X0 ),
% 27.57/3.99      inference(cnf_transformation,[],[f96]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_514,plain,
% 27.57/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 27.57/3.99      | sK3 != X0
% 27.57/3.99      | sK1 != k1_xboole_0
% 27.57/3.99      | sK0 != X1
% 27.57/3.99      | k1_xboole_0 = X0
% 27.57/3.99      | k1_xboole_0 = X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_23,c_36]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_515,plain,
% 27.57/3.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 27.57/3.99      | sK1 != k1_xboole_0
% 27.57/3.99      | k1_xboole_0 = sK3
% 27.57/3.99      | k1_xboole_0 = sK0 ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_514]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1705,plain,
% 27.57/3.99      ( sK1 != k1_xboole_0
% 27.57/3.99      | k1_xboole_0 = sK3
% 27.57/3.99      | k1_xboole_0 = sK0
% 27.57/3.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1819,plain,
% 27.57/3.99      ( sK3 = k1_xboole_0
% 27.57/3.99      | sK1 != k1_xboole_0
% 27.57/3.99      | sK0 = k1_xboole_0
% 27.57/3.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 27.57/3.99      inference(demodulation,[status(thm)],[c_1705,c_6]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2293,plain,
% 27.57/3.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 27.57/3.99      | r1_tarski(sK3,k1_xboole_0) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_10]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2294,plain,
% 27.57/3.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 27.57/3.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_2293]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2341,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,sK3) ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_4]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2344,plain,
% 27.57/4.00      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 27.57/4.00      inference(predicate_to_equality,[status(thm)],[c_2341]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2361,plain,
% 27.57/4.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2362,plain,
% 27.57/4.00      ( sK3 = X0
% 27.57/4.00      | r1_tarski(X0,sK3) != iProver_top
% 27.57/4.00      | r1_tarski(sK3,X0) != iProver_top ),
% 27.57/4.00      inference(predicate_to_equality,[status(thm)],[c_2361]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2364,plain,
% 27.57/4.00      ( sK3 = k1_xboole_0
% 27.57/4.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 27.57/4.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_2362]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2409,plain,
% 27.57/4.00      ( sK3 = k1_xboole_0
% 27.57/4.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 27.57/4.00      inference(global_propositional_subsumption,
% 27.57/4.00                [status(thm)],
% 27.57/4.00                [c_1819,c_2294,c_2344,c_2364]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_7500,plain,
% 27.57/4.00      ( sK3 = k1_xboole_0 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 27.57/4.00      inference(superposition,[status(thm)],[c_7223,c_2409]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_7541,plain,
% 27.57/4.00      ( ~ r1_tarski(sK1,k1_xboole_0) | sK3 = k1_xboole_0 ),
% 27.57/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_7500]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_7499,plain,
% 27.57/4.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 27.57/4.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 27.57/4.00      inference(superposition,[status(thm)],[c_7223,c_1721]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_7540,plain,
% 27.57/4.00      ( r1_tarski(sK3,k1_xboole_0) | ~ r1_tarski(sK1,k1_xboole_0) ),
% 27.57/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_7499]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_22,plain,
% 27.57/4.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 27.57/4.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 27.57/4.00      | k1_xboole_0 = X0 ),
% 27.57/4.00      inference(cnf_transformation,[],[f95]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_462,plain,
% 27.57/4.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.57/4.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 27.57/4.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/4.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 27.57/4.00      | sK2 != X0
% 27.57/4.00      | sK1 != k1_xboole_0
% 27.57/4.00      | k1_xboole_0 = X0 ),
% 27.57/4.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_463,plain,
% 27.57/4.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.57/4.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 27.57/4.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/4.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 27.57/4.00      | sK1 != k1_xboole_0
% 27.57/4.00      | k1_xboole_0 = sK2 ),
% 27.57/4.00      inference(unflattening,[status(thm)],[c_462]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_1707,plain,
% 27.57/4.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 27.57/4.00      | sK1 != k1_xboole_0
% 27.57/4.00      | k1_xboole_0 = sK2
% 27.57/4.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.57/4.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 27.57/4.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 27.57/4.00      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_1903,plain,
% 27.57/4.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 27.57/4.00      | sK2 = k1_xboole_0
% 27.57/4.00      | sK1 != k1_xboole_0
% 27.57/4.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.57/4.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 27.57/4.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 27.57/4.00      inference(demodulation,[status(thm)],[c_1707,c_6]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_105,plain,
% 27.57/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 27.57/4.00      | r1_tarski(X0,X1) != iProver_top ),
% 27.57/4.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_107,plain,
% 27.57/4.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 27.57/4.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_105]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2352,plain,
% 27.57/4.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.57/4.00      | sK1 != k1_xboole_0
% 27.57/4.00      | sK2 = k1_xboole_0
% 27.57/4.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 27.57/4.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 27.57/4.00      inference(global_propositional_subsumption,
% 27.57/4.00                [status(thm)],
% 27.57/4.00                [c_1903,c_107,c_115]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2353,plain,
% 27.57/4.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 27.57/4.00      | sK2 = k1_xboole_0
% 27.57/4.00      | sK1 != k1_xboole_0
% 27.57/4.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.57/4.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 27.57/4.00      inference(renaming,[status(thm)],[c_2352]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_4804,plain,
% 27.57/4.00      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 27.57/4.00      | sK2 = k1_xboole_0
% 27.57/4.00      | sK1 != k1_xboole_0
% 27.57/4.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.57/4.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 27.57/4.00      inference(demodulation,[status(thm)],[c_4799,c_2353]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_33,negated_conjecture,
% 27.57/4.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 27.57/4.00      inference(cnf_transformation,[],[f88]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_114,plain,
% 27.57/4.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_4]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2041,plain,
% 27.57/4.00      ( ~ r1_tarski(sK2,k1_xboole_0)
% 27.57/4.00      | ~ r1_tarski(k1_xboole_0,sK2)
% 27.57/4.00      | sK2 = k1_xboole_0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2272,plain,
% 27.57/4.00      ( ~ r1_tarski(X0,X1)
% 27.57/4.00      | r1_tarski(sK0,k1_xboole_0)
% 27.57/4.00      | sK0 != X0
% 27.57/4.00      | k1_xboole_0 != X1 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_1013]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2274,plain,
% 27.57/4.00      ( r1_tarski(sK0,k1_xboole_0)
% 27.57/4.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 27.57/4.00      | sK0 != k1_xboole_0
% 27.57/4.00      | k1_xboole_0 != k1_xboole_0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_2272]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2062,plain,
% 27.57/4.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2319,plain,
% 27.57/4.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_2062]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_1011,plain,( X0 = X0 ),theory(equality) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2320,plain,
% 27.57/4.00      ( sK0 = sK0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2749,plain,
% 27.57/4.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2750,plain,
% 27.57/4.00      ( sK1 != k1_xboole_0
% 27.57/4.00      | k1_xboole_0 = sK1
% 27.57/4.00      | k1_xboole_0 != k1_xboole_0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_2749]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2258,plain,
% 27.57/4.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 27.57/4.00      | ~ r1_tarski(sK2,X0)
% 27.57/4.00      | r1_tarski(sK2,k1_xboole_0) ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_3]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2941,plain,
% 27.57/4.00      ( ~ r1_tarski(sK2,sK0)
% 27.57/4.00      | r1_tarski(sK2,k1_xboole_0)
% 27.57/4.00      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_2258]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_3541,plain,
% 27.57/4.00      ( r1_tarski(k1_xboole_0,sK2) ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_4]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_5419,plain,
% 27.57/4.00      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 27.57/4.00      inference(global_propositional_subsumption,
% 27.57/4.00                [status(thm)],
% 27.57/4.00                [c_4804,c_34,c_33,c_108,c_109,c_114,c_2041,c_2274,c_2319,
% 27.57/4.00                 c_2320,c_2750,c_2941,c_3541]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_3255,plain,
% 27.57/4.00      ( v1_relat_1(sK3) ),
% 27.57/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_3254]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2308,plain,
% 27.57/4.00      ( sK1 = sK1 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2226,plain,
% 27.57/4.00      ( r1_tarski(sK1,k1_xboole_0)
% 27.57/4.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 27.57/4.00      | sK1 != k1_xboole_0
% 27.57/4.00      | k1_xboole_0 != k1_xboole_0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_2224]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_5,plain,
% 27.57/4.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 27.57/4.00      inference(cnf_transformation,[],[f57]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2136,plain,
% 27.57/4.00      ( ~ r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK3 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_5]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2063,plain,
% 27.57/4.00      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_2064,plain,
% 27.57/4.00      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 27.57/4.00      inference(instantiation,[status(thm)],[c_2063]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(c_665,plain,
% 27.57/4.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.57/4.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 27.57/4.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 27.57/4.00      | sK2 != sK0
% 27.57/4.00      | sK1 != sK1 ),
% 27.57/4.00      inference(resolution_lifted,[status(thm)],[c_32,c_36]) ).
% 27.57/4.00  
% 27.57/4.00  cnf(contradiction,plain,
% 27.57/4.00      ( $false ),
% 27.57/4.00      inference(minisat,
% 27.57/4.00                [status(thm)],
% 27.57/4.00                [c_111034,c_95961,c_93580,c_87317,c_85714,c_85331,
% 27.57/4.00                 c_84955,c_84483,c_82102,c_40857,c_40372,c_40005,c_20173,
% 27.57/4.00                 c_7541,c_7540,c_5419,c_3255,c_2750,c_2320,c_2319,c_2308,
% 27.57/4.00                 c_2226,c_2136,c_2064,c_665,c_114,c_109,c_108,c_33,c_35,
% 27.57/4.00                 c_37]) ).
% 27.57/4.00  
% 27.57/4.00  
% 27.57/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.57/4.00  
% 27.57/4.00  ------                               Statistics
% 27.57/4.00  
% 27.57/4.00  ------ General
% 27.57/4.00  
% 27.57/4.00  abstr_ref_over_cycles:                  0
% 27.57/4.00  abstr_ref_under_cycles:                 0
% 27.57/4.00  gc_basic_clause_elim:                   0
% 27.57/4.00  forced_gc_time:                         0
% 27.57/4.00  parsing_time:                           0.011
% 27.57/4.00  unif_index_cands_time:                  0.
% 27.57/4.00  unif_index_add_time:                    0.
% 27.57/4.00  orderings_time:                         0.
% 27.57/4.00  out_proof_time:                         0.024
% 27.57/4.00  total_time:                             3.478
% 27.57/4.00  num_of_symbols:                         49
% 27.57/4.00  num_of_terms:                           61831
% 27.57/4.00  
% 27.57/4.00  ------ Preprocessing
% 27.57/4.00  
% 27.57/4.00  num_of_splits:                          0
% 27.57/4.00  num_of_split_atoms:                     0
% 27.57/4.00  num_of_reused_defs:                     0
% 27.57/4.00  num_eq_ax_congr_red:                    13
% 27.57/4.00  num_of_sem_filtered_clauses:            1
% 27.57/4.00  num_of_subtypes:                        0
% 27.57/4.00  monotx_restored_types:                  0
% 27.57/4.00  sat_num_of_epr_types:                   0
% 27.57/4.00  sat_num_of_non_cyclic_types:            0
% 27.57/4.00  sat_guarded_non_collapsed_types:        0
% 27.57/4.00  num_pure_diseq_elim:                    0
% 27.57/4.00  simp_replaced_by:                       0
% 27.57/4.00  res_preprocessed:                       163
% 27.57/4.00  prep_upred:                             0
% 27.57/4.00  prep_unflattend:                        43
% 27.57/4.00  smt_new_axioms:                         0
% 27.57/4.00  pred_elim_cands:                        4
% 27.57/4.00  pred_elim:                              2
% 27.57/4.00  pred_elim_cl:                           0
% 27.57/4.00  pred_elim_cycles:                       4
% 27.57/4.00  merged_defs:                            8
% 27.57/4.00  merged_defs_ncl:                        0
% 27.57/4.00  bin_hyper_res:                          9
% 27.57/4.00  prep_cycles:                            4
% 27.57/4.00  pred_elim_time:                         0.009
% 27.57/4.00  splitting_time:                         0.
% 27.57/4.00  sem_filter_time:                        0.
% 27.57/4.00  monotx_time:                            0.001
% 27.57/4.00  subtype_inf_time:                       0.
% 27.57/4.00  
% 27.57/4.00  ------ Problem properties
% 27.57/4.00  
% 27.57/4.00  clauses:                                35
% 27.57/4.00  conjectures:                            4
% 27.57/4.00  epr:                                    9
% 27.57/4.00  horn:                                   30
% 27.57/4.00  ground:                                 12
% 27.57/4.00  unary:                                  8
% 27.57/4.00  binary:                                 8
% 27.57/4.00  lits:                                   97
% 27.57/4.00  lits_eq:                                35
% 27.57/4.00  fd_pure:                                0
% 27.57/4.00  fd_pseudo:                              0
% 27.57/4.00  fd_cond:                                4
% 27.57/4.00  fd_pseudo_cond:                         1
% 27.57/4.00  ac_symbols:                             0
% 27.57/4.00  
% 27.57/4.00  ------ Propositional Solver
% 27.57/4.00  
% 27.57/4.00  prop_solver_calls:                      38
% 27.57/4.00  prop_fast_solver_calls:                 4119
% 27.57/4.00  smt_solver_calls:                       0
% 27.57/4.00  smt_fast_solver_calls:                  0
% 27.57/4.00  prop_num_of_clauses:                    34312
% 27.57/4.00  prop_preprocess_simplified:             43306
% 27.57/4.00  prop_fo_subsumed:                       412
% 27.57/4.00  prop_solver_time:                       0.
% 27.57/4.00  smt_solver_time:                        0.
% 27.57/4.00  smt_fast_solver_time:                   0.
% 27.57/4.00  prop_fast_solver_time:                  0.
% 27.57/4.00  prop_unsat_core_time:                   0.004
% 27.57/4.00  
% 27.57/4.00  ------ QBF
% 27.57/4.00  
% 27.57/4.00  qbf_q_res:                              0
% 27.57/4.00  qbf_num_tautologies:                    0
% 27.57/4.00  qbf_prep_cycles:                        0
% 27.57/4.00  
% 27.57/4.00  ------ BMC1
% 27.57/4.00  
% 27.57/4.00  bmc1_current_bound:                     -1
% 27.57/4.00  bmc1_last_solved_bound:                 -1
% 27.57/4.00  bmc1_unsat_core_size:                   -1
% 27.57/4.00  bmc1_unsat_core_parents_size:           -1
% 27.57/4.00  bmc1_merge_next_fun:                    0
% 27.57/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.57/4.00  
% 27.57/4.00  ------ Instantiation
% 27.57/4.00  
% 27.57/4.00  inst_num_of_clauses:                    1208
% 27.57/4.00  inst_num_in_passive:                    212
% 27.57/4.00  inst_num_in_active:                     3044
% 27.57/4.00  inst_num_in_unprocessed:                429
% 27.57/4.00  inst_num_of_loops:                      3754
% 27.57/4.00  inst_num_of_learning_restarts:          1
% 27.57/4.00  inst_num_moves_active_passive:          703
% 27.57/4.00  inst_lit_activity:                      0
% 27.57/4.00  inst_lit_activity_moves:                0
% 27.57/4.00  inst_num_tautologies:                   0
% 27.57/4.00  inst_num_prop_implied:                  0
% 27.57/4.00  inst_num_existing_simplified:           0
% 27.57/4.00  inst_num_eq_res_simplified:             0
% 27.57/4.00  inst_num_child_elim:                    0
% 27.57/4.00  inst_num_of_dismatching_blockings:      4047
% 27.57/4.00  inst_num_of_non_proper_insts:           9785
% 27.57/4.00  inst_num_of_duplicates:                 0
% 27.57/4.00  inst_inst_num_from_inst_to_res:         0
% 27.57/4.00  inst_dismatching_checking_time:         0.
% 27.57/4.00  
% 27.57/4.00  ------ Resolution
% 27.57/4.00  
% 27.57/4.00  res_num_of_clauses:                     46
% 27.57/4.00  res_num_in_passive:                     46
% 27.57/4.00  res_num_in_active:                      0
% 27.57/4.00  res_num_of_loops:                       167
% 27.57/4.00  res_forward_subset_subsumed:            292
% 27.57/4.00  res_backward_subset_subsumed:           6
% 27.57/4.00  res_forward_subsumed:                   0
% 27.57/4.00  res_backward_subsumed:                  0
% 27.57/4.00  res_forward_subsumption_resolution:     3
% 27.57/4.00  res_backward_subsumption_resolution:    0
% 27.57/4.00  res_clause_to_clause_subsumption:       29004
% 27.57/4.00  res_orphan_elimination:                 0
% 27.57/4.00  res_tautology_del:                      755
% 27.57/4.00  res_num_eq_res_simplified:              1
% 27.57/4.00  res_num_sel_changes:                    0
% 27.57/4.00  res_moves_from_active_to_pass:          0
% 27.57/4.00  
% 27.57/4.00  ------ Superposition
% 27.57/4.00  
% 27.57/4.00  sup_time_total:                         0.
% 27.57/4.00  sup_time_generating:                    0.
% 27.57/4.00  sup_time_sim_full:                      0.
% 27.57/4.00  sup_time_sim_immed:                     0.
% 27.57/4.00  
% 27.57/4.00  sup_num_of_clauses:                     3267
% 27.57/4.00  sup_num_in_active:                      178
% 27.57/4.00  sup_num_in_passive:                     3089
% 27.57/4.00  sup_num_of_loops:                       750
% 27.57/4.00  sup_fw_superposition:                   2929
% 27.57/4.00  sup_bw_superposition:                   3972
% 27.57/4.00  sup_immediate_simplified:               2018
% 27.57/4.00  sup_given_eliminated:                   43
% 27.57/4.00  comparisons_done:                       0
% 27.57/4.00  comparisons_avoided:                    370
% 27.57/4.00  
% 27.57/4.00  ------ Simplifications
% 27.57/4.00  
% 27.57/4.00  
% 27.57/4.00  sim_fw_subset_subsumed:                 389
% 27.57/4.00  sim_bw_subset_subsumed:                 656
% 27.57/4.00  sim_fw_subsumed:                        629
% 27.57/4.00  sim_bw_subsumed:                        344
% 27.57/4.00  sim_fw_subsumption_res:                 16
% 27.57/4.00  sim_bw_subsumption_res:                 11
% 27.57/4.00  sim_tautology_del:                      132
% 27.57/4.00  sim_eq_tautology_del:                   186
% 27.57/4.00  sim_eq_res_simp:                        4
% 27.57/4.00  sim_fw_demodulated:                     575
% 27.57/4.00  sim_bw_demodulated:                     685
% 27.57/4.00  sim_light_normalised:                   648
% 27.57/4.00  sim_joinable_taut:                      0
% 27.57/4.00  sim_joinable_simp:                      0
% 27.57/4.00  sim_ac_normalised:                      0
% 27.57/4.00  sim_smt_subsumption:                    0
% 27.57/4.00  
%------------------------------------------------------------------------------
