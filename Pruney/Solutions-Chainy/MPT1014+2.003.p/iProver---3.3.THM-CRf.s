%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:46 EST 2020

% Result     : Theorem 23.54s
% Output     : CNFRefutation 23.54s
% Verified   : 
% Statistics : Number of formulae       :  193 (1442 expanded)
%              Number of clauses        :  111 ( 394 expanded)
%              Number of leaves         :   24 ( 341 expanded)
%              Depth                    :   23
%              Number of atoms          :  614 (8199 expanded)
%              Number of equality atoms :  290 (1669 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( k2_relset_1(X0,X0,X1) = X0
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k6_partfun1(X0))
        & k2_relset_1(X0,X0,X1) = X0
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & k2_relset_1(X0,X0,X1) = X0
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & k2_relset_1(sK0,sK0,sK1) = sK0
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f49,f48])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X2 = X3
              | k5_relat_1(X1,X2) != k5_relat_1(X1,X3)
              | k1_relat_1(X3) != X0
              | k1_relat_1(X2) != X0
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X2 = X3
              | k5_relat_1(X1,X2) != k5_relat_1(X1,X3)
              | k1_relat_1(X3) != X0
              | k1_relat_1(X2) != X0
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | k5_relat_1(X1,X2) != k5_relat_1(X1,X3)
      | k1_relat_1(X3) != X0
      | k1_relat_1(X2) != X0
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X2,X3,X1] :
      ( X2 = X3
      | k5_relat_1(X1,X2) != k5_relat_1(X1,X3)
      | k1_relat_1(X2) != k1_relat_1(X3)
      | k2_relat_1(X1) != k1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f89,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f64,f76])).

fof(f65,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f65,f76])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f83,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_655,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_51985,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5486,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_13929,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0 != sK2
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_5486])).

cnf(c_19764,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_13929])).

cnf(c_19766,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_19764])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2190,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_1265])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1267,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2260,plain,
    ( k3_xboole_0(sK2,k2_zfmisc_1(sK0,sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_2190,c_1267])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1248,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1251,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4759,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_1251])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4959,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4759,c_34])).

cnf(c_4960,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4959])).

cnf(c_4969,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_4960])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_396,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_30])).

cnf(c_1245,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1314,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1547,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_31,c_30,c_29,c_28,c_394,c_1314])).

cnf(c_4970,plain,
    ( k5_relat_1(sK1,sK2) = sK1
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4969,c_1547])).

cnf(c_32,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5537,plain,
    ( k5_relat_1(sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4970,c_32])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1263,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5539,plain,
    ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5537,c_1263])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1254,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3078,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1248,c_1254])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3079,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3078,c_26])).

cnf(c_5547,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5539,c_3079])).

cnf(c_33,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1381,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1382,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_1384,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1392,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_1394,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_5558,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5547,c_33,c_35,c_1384,c_1394])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1269,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5563,plain,
    ( k2_relat_1(sK2) = sK0
    | r1_tarski(k2_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5558,c_1269])).

cnf(c_3077,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1250,c_1254])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1255,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3625,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3077,c_1255])).

cnf(c_3802,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3625,c_35])).

cnf(c_3806,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3802,c_1265])).

cnf(c_3897,plain,
    ( k2_relat_1(sK2) = sK0
    | r1_tarski(sK0,k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3806,c_1269])).

cnf(c_6258,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5563,c_33,c_35,c_1384,c_1394,c_3897,c_5547])).

cnf(c_1256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2356,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_1256])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1260,plain,
    ( k3_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2572,plain,
    ( k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2))) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2356,c_1260])).

cnf(c_6269,plain,
    ( k3_xboole_0(sK2,k2_zfmisc_1(X0,sK0)) = k7_relat_1(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_6258,c_2572])).

cnf(c_11755,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_2260,c_6269])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1257,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5540,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5537,c_1257])).

cnf(c_5546,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5540,c_3079])).

cnf(c_5681,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5546,c_32,c_33,c_34,c_35,c_1384,c_1394])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1261,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5688,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5681,c_1261])).

cnf(c_6313,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5688,c_35,c_1384])).

cnf(c_11807,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_11755,c_6313])).

cnf(c_9,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k5_relat_1(X2,X0) != k5_relat_1(X2,X1)
    | k1_relat_1(X0) != k1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1258,plain,
    ( X0 = X1
    | k5_relat_1(X2,X0) != k5_relat_1(X2,X1)
    | k1_relat_1(X0) != k1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X2)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5541,plain,
    ( k5_relat_1(sK1,X0) != sK1
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | sK2 = X0
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5537,c_1258])).

cnf(c_5545,plain,
    ( k5_relat_1(sK1,X0) != sK1
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | k1_relat_1(sK2) != sK0
    | sK2 = X0
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5541,c_3079])).

cnf(c_5912,plain,
    ( k5_relat_1(sK1,X0) != sK1
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | k1_relat_1(sK2) != sK0
    | sK2 = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5545,c_32,c_33,c_34,c_35,c_1384,c_1394])).

cnf(c_5918,plain,
    ( k5_relat_1(sK1,k6_partfun1(X0)) != sK1
    | k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) != sK0
    | k6_partfun1(X0) = sK2
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_5912])).

cnf(c_14,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_13,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5923,plain,
    ( ~ v1_funct_1(k6_partfun1(X0))
    | ~ v1_relat_1(k6_partfun1(X0))
    | k5_relat_1(sK1,k6_partfun1(X0)) != sK1
    | k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) != sK0
    | k6_partfun1(X0) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5918])).

cnf(c_6668,plain,
    ( k5_relat_1(sK1,k6_partfun1(X0)) != sK1
    | k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) != sK0
    | k6_partfun1(X0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5918,c_14,c_13,c_5923])).

cnf(c_6670,plain,
    ( k5_relat_1(sK1,k6_partfun1(sK0)) != sK1
    | k1_relat_1(sK2) != sK0
    | k6_partfun1(sK0) = sK2 ),
    inference(instantiation,[status(thm)],[c_6668])).

cnf(c_2357,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_1256])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1262,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2577,plain,
    ( k5_relat_1(sK1,k6_partfun1(k2_relat_1(sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2357,c_1262])).

cnf(c_3086,plain,
    ( k5_relat_1(sK1,k6_partfun1(sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3079,c_2577])).

cnf(c_1438,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_656,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1309,plain,
    ( k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_1361,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_20,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_384,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51985,c_19766,c_11807,c_6670,c_3086,c_1438,c_1361,c_384,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.30  % Computer   : n010.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 10:33:59 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 23.54/3.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.54/3.47  
% 23.54/3.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.54/3.47  
% 23.54/3.47  ------  iProver source info
% 23.54/3.47  
% 23.54/3.47  git: date: 2020-06-30 10:37:57 +0100
% 23.54/3.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.54/3.47  git: non_committed_changes: false
% 23.54/3.47  git: last_make_outside_of_git: false
% 23.54/3.47  
% 23.54/3.47  ------ 
% 23.54/3.47  
% 23.54/3.47  ------ Input Options
% 23.54/3.47  
% 23.54/3.47  --out_options                           all
% 23.54/3.47  --tptp_safe_out                         true
% 23.54/3.47  --problem_path                          ""
% 23.54/3.47  --include_path                          ""
% 23.54/3.47  --clausifier                            res/vclausify_rel
% 23.54/3.47  --clausifier_options                    ""
% 23.54/3.47  --stdin                                 false
% 23.54/3.47  --stats_out                             all
% 23.54/3.47  
% 23.54/3.47  ------ General Options
% 23.54/3.47  
% 23.54/3.47  --fof                                   false
% 23.54/3.47  --time_out_real                         305.
% 23.54/3.47  --time_out_virtual                      -1.
% 23.54/3.47  --symbol_type_check                     false
% 23.54/3.47  --clausify_out                          false
% 23.54/3.47  --sig_cnt_out                           false
% 23.54/3.47  --trig_cnt_out                          false
% 23.54/3.47  --trig_cnt_out_tolerance                1.
% 23.54/3.47  --trig_cnt_out_sk_spl                   false
% 23.54/3.47  --abstr_cl_out                          false
% 23.54/3.47  
% 23.54/3.47  ------ Global Options
% 23.54/3.47  
% 23.54/3.47  --schedule                              default
% 23.54/3.47  --add_important_lit                     false
% 23.54/3.47  --prop_solver_per_cl                    1000
% 23.54/3.47  --min_unsat_core                        false
% 23.54/3.47  --soft_assumptions                      false
% 23.54/3.47  --soft_lemma_size                       3
% 23.54/3.47  --prop_impl_unit_size                   0
% 23.54/3.47  --prop_impl_unit                        []
% 23.54/3.47  --share_sel_clauses                     true
% 23.54/3.47  --reset_solvers                         false
% 23.54/3.47  --bc_imp_inh                            [conj_cone]
% 23.54/3.47  --conj_cone_tolerance                   3.
% 23.54/3.47  --extra_neg_conj                        none
% 23.54/3.47  --large_theory_mode                     true
% 23.54/3.47  --prolific_symb_bound                   200
% 23.54/3.47  --lt_threshold                          2000
% 23.54/3.47  --clause_weak_htbl                      true
% 23.54/3.47  --gc_record_bc_elim                     false
% 23.54/3.47  
% 23.54/3.47  ------ Preprocessing Options
% 23.54/3.47  
% 23.54/3.47  --preprocessing_flag                    true
% 23.54/3.47  --time_out_prep_mult                    0.1
% 23.54/3.47  --splitting_mode                        input
% 23.54/3.47  --splitting_grd                         true
% 23.54/3.47  --splitting_cvd                         false
% 23.54/3.47  --splitting_cvd_svl                     false
% 23.54/3.47  --splitting_nvd                         32
% 23.54/3.47  --sub_typing                            true
% 23.54/3.47  --prep_gs_sim                           true
% 23.54/3.47  --prep_unflatten                        true
% 23.54/3.47  --prep_res_sim                          true
% 23.54/3.47  --prep_upred                            true
% 23.54/3.47  --prep_sem_filter                       exhaustive
% 23.54/3.47  --prep_sem_filter_out                   false
% 23.54/3.47  --pred_elim                             true
% 23.54/3.47  --res_sim_input                         true
% 23.54/3.47  --eq_ax_congr_red                       true
% 23.54/3.47  --pure_diseq_elim                       true
% 23.54/3.47  --brand_transform                       false
% 23.54/3.47  --non_eq_to_eq                          false
% 23.54/3.47  --prep_def_merge                        true
% 23.54/3.47  --prep_def_merge_prop_impl              false
% 23.54/3.47  --prep_def_merge_mbd                    true
% 23.54/3.47  --prep_def_merge_tr_red                 false
% 23.54/3.47  --prep_def_merge_tr_cl                  false
% 23.54/3.47  --smt_preprocessing                     true
% 23.54/3.47  --smt_ac_axioms                         fast
% 23.54/3.47  --preprocessed_out                      false
% 23.54/3.47  --preprocessed_stats                    false
% 23.54/3.47  
% 23.54/3.47  ------ Abstraction refinement Options
% 23.54/3.47  
% 23.54/3.47  --abstr_ref                             []
% 23.54/3.47  --abstr_ref_prep                        false
% 23.54/3.47  --abstr_ref_until_sat                   false
% 23.54/3.47  --abstr_ref_sig_restrict                funpre
% 23.54/3.47  --abstr_ref_af_restrict_to_split_sk     false
% 23.54/3.47  --abstr_ref_under                       []
% 23.54/3.47  
% 23.54/3.47  ------ SAT Options
% 23.54/3.47  
% 23.54/3.47  --sat_mode                              false
% 23.54/3.47  --sat_fm_restart_options                ""
% 23.54/3.47  --sat_gr_def                            false
% 23.54/3.47  --sat_epr_types                         true
% 23.54/3.47  --sat_non_cyclic_types                  false
% 23.54/3.47  --sat_finite_models                     false
% 23.54/3.47  --sat_fm_lemmas                         false
% 23.54/3.47  --sat_fm_prep                           false
% 23.54/3.47  --sat_fm_uc_incr                        true
% 23.54/3.47  --sat_out_model                         small
% 23.54/3.47  --sat_out_clauses                       false
% 23.54/3.47  
% 23.54/3.47  ------ QBF Options
% 23.54/3.47  
% 23.54/3.47  --qbf_mode                              false
% 23.54/3.47  --qbf_elim_univ                         false
% 23.54/3.47  --qbf_dom_inst                          none
% 23.54/3.47  --qbf_dom_pre_inst                      false
% 23.54/3.47  --qbf_sk_in                             false
% 23.54/3.47  --qbf_pred_elim                         true
% 23.54/3.47  --qbf_split                             512
% 23.54/3.47  
% 23.54/3.47  ------ BMC1 Options
% 23.54/3.47  
% 23.54/3.47  --bmc1_incremental                      false
% 23.54/3.47  --bmc1_axioms                           reachable_all
% 23.54/3.47  --bmc1_min_bound                        0
% 23.54/3.47  --bmc1_max_bound                        -1
% 23.54/3.47  --bmc1_max_bound_default                -1
% 23.54/3.47  --bmc1_symbol_reachability              true
% 23.54/3.47  --bmc1_property_lemmas                  false
% 23.54/3.47  --bmc1_k_induction                      false
% 23.54/3.47  --bmc1_non_equiv_states                 false
% 23.54/3.47  --bmc1_deadlock                         false
% 23.54/3.47  --bmc1_ucm                              false
% 23.54/3.47  --bmc1_add_unsat_core                   none
% 23.54/3.47  --bmc1_unsat_core_children              false
% 23.54/3.47  --bmc1_unsat_core_extrapolate_axioms    false
% 23.54/3.47  --bmc1_out_stat                         full
% 23.54/3.47  --bmc1_ground_init                      false
% 23.54/3.47  --bmc1_pre_inst_next_state              false
% 23.54/3.47  --bmc1_pre_inst_state                   false
% 23.54/3.47  --bmc1_pre_inst_reach_state             false
% 23.54/3.47  --bmc1_out_unsat_core                   false
% 23.54/3.47  --bmc1_aig_witness_out                  false
% 23.54/3.47  --bmc1_verbose                          false
% 23.54/3.47  --bmc1_dump_clauses_tptp                false
% 23.54/3.47  --bmc1_dump_unsat_core_tptp             false
% 23.54/3.47  --bmc1_dump_file                        -
% 23.54/3.47  --bmc1_ucm_expand_uc_limit              128
% 23.54/3.47  --bmc1_ucm_n_expand_iterations          6
% 23.54/3.47  --bmc1_ucm_extend_mode                  1
% 23.54/3.47  --bmc1_ucm_init_mode                    2
% 23.54/3.47  --bmc1_ucm_cone_mode                    none
% 23.54/3.47  --bmc1_ucm_reduced_relation_type        0
% 23.54/3.47  --bmc1_ucm_relax_model                  4
% 23.54/3.47  --bmc1_ucm_full_tr_after_sat            true
% 23.54/3.47  --bmc1_ucm_expand_neg_assumptions       false
% 23.54/3.47  --bmc1_ucm_layered_model                none
% 23.54/3.47  --bmc1_ucm_max_lemma_size               10
% 23.54/3.47  
% 23.54/3.47  ------ AIG Options
% 23.54/3.47  
% 23.54/3.47  --aig_mode                              false
% 23.54/3.47  
% 23.54/3.47  ------ Instantiation Options
% 23.54/3.47  
% 23.54/3.47  --instantiation_flag                    true
% 23.54/3.47  --inst_sos_flag                         true
% 23.54/3.47  --inst_sos_phase                        true
% 23.54/3.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.54/3.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.54/3.47  --inst_lit_sel_side                     num_symb
% 23.54/3.47  --inst_solver_per_active                1400
% 23.54/3.47  --inst_solver_calls_frac                1.
% 23.54/3.47  --inst_passive_queue_type               priority_queues
% 23.54/3.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.54/3.47  --inst_passive_queues_freq              [25;2]
% 23.54/3.47  --inst_dismatching                      true
% 23.54/3.47  --inst_eager_unprocessed_to_passive     true
% 23.54/3.47  --inst_prop_sim_given                   true
% 23.54/3.47  --inst_prop_sim_new                     false
% 23.54/3.47  --inst_subs_new                         false
% 23.54/3.47  --inst_eq_res_simp                      false
% 23.54/3.47  --inst_subs_given                       false
% 23.54/3.47  --inst_orphan_elimination               true
% 23.54/3.47  --inst_learning_loop_flag               true
% 23.54/3.47  --inst_learning_start                   3000
% 23.54/3.47  --inst_learning_factor                  2
% 23.54/3.47  --inst_start_prop_sim_after_learn       3
% 23.54/3.47  --inst_sel_renew                        solver
% 23.54/3.47  --inst_lit_activity_flag                true
% 23.54/3.47  --inst_restr_to_given                   false
% 23.54/3.47  --inst_activity_threshold               500
% 23.54/3.47  --inst_out_proof                        true
% 23.54/3.47  
% 23.54/3.47  ------ Resolution Options
% 23.54/3.47  
% 23.54/3.47  --resolution_flag                       true
% 23.54/3.47  --res_lit_sel                           adaptive
% 23.54/3.47  --res_lit_sel_side                      none
% 23.54/3.47  --res_ordering                          kbo
% 23.54/3.47  --res_to_prop_solver                    active
% 23.54/3.47  --res_prop_simpl_new                    false
% 23.54/3.47  --res_prop_simpl_given                  true
% 23.54/3.47  --res_passive_queue_type                priority_queues
% 23.54/3.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.54/3.47  --res_passive_queues_freq               [15;5]
% 23.54/3.47  --res_forward_subs                      full
% 23.54/3.47  --res_backward_subs                     full
% 23.54/3.47  --res_forward_subs_resolution           true
% 23.54/3.47  --res_backward_subs_resolution          true
% 23.54/3.47  --res_orphan_elimination                true
% 23.54/3.47  --res_time_limit                        2.
% 23.54/3.47  --res_out_proof                         true
% 23.54/3.47  
% 23.54/3.47  ------ Superposition Options
% 23.54/3.47  
% 23.54/3.47  --superposition_flag                    true
% 23.54/3.47  --sup_passive_queue_type                priority_queues
% 23.54/3.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.54/3.47  --sup_passive_queues_freq               [8;1;4]
% 23.54/3.47  --demod_completeness_check              fast
% 23.54/3.47  --demod_use_ground                      true
% 23.54/3.47  --sup_to_prop_solver                    passive
% 23.54/3.47  --sup_prop_simpl_new                    true
% 23.54/3.47  --sup_prop_simpl_given                  true
% 23.54/3.47  --sup_fun_splitting                     true
% 23.54/3.47  --sup_smt_interval                      50000
% 23.54/3.47  
% 23.54/3.47  ------ Superposition Simplification Setup
% 23.54/3.47  
% 23.54/3.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.54/3.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.54/3.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.54/3.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.54/3.47  --sup_full_triv                         [TrivRules;PropSubs]
% 23.54/3.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.54/3.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.54/3.47  --sup_immed_triv                        [TrivRules]
% 23.54/3.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.47  --sup_immed_bw_main                     []
% 23.54/3.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.54/3.47  --sup_input_triv                        [Unflattening;TrivRules]
% 23.54/3.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.47  --sup_input_bw                          []
% 23.54/3.47  
% 23.54/3.47  ------ Combination Options
% 23.54/3.47  
% 23.54/3.47  --comb_res_mult                         3
% 23.54/3.47  --comb_sup_mult                         2
% 23.54/3.47  --comb_inst_mult                        10
% 23.54/3.47  
% 23.54/3.47  ------ Debug Options
% 23.54/3.47  
% 23.54/3.47  --dbg_backtrace                         false
% 23.54/3.47  --dbg_dump_prop_clauses                 false
% 23.54/3.47  --dbg_dump_prop_clauses_file            -
% 23.54/3.47  --dbg_out_stat                          false
% 23.54/3.47  ------ Parsing...
% 23.54/3.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.54/3.47  
% 23.54/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.54/3.47  
% 23.54/3.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.54/3.47  
% 23.54/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.54/3.47  ------ Proving...
% 23.54/3.47  ------ Problem Properties 
% 23.54/3.47  
% 23.54/3.47  
% 23.54/3.47  clauses                                 29
% 23.54/3.47  conjectures                             5
% 23.54/3.47  EPR                                     4
% 23.54/3.47  Horn                                    29
% 23.54/3.47  unary                                   10
% 23.54/3.47  binary                                  11
% 23.54/3.47  lits                                    72
% 23.54/3.47  lits eq                                 19
% 23.54/3.47  fd_pure                                 0
% 23.54/3.47  fd_pseudo                               0
% 23.54/3.47  fd_cond                                 0
% 23.54/3.47  fd_pseudo_cond                          2
% 23.54/3.47  AC symbols                              0
% 23.54/3.47  
% 23.54/3.47  ------ Schedule dynamic 5 is on 
% 23.54/3.47  
% 23.54/3.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.54/3.47  
% 23.54/3.47  
% 23.54/3.47  ------ 
% 23.54/3.47  Current options:
% 23.54/3.47  ------ 
% 23.54/3.47  
% 23.54/3.47  ------ Input Options
% 23.54/3.47  
% 23.54/3.47  --out_options                           all
% 23.54/3.47  --tptp_safe_out                         true
% 23.54/3.47  --problem_path                          ""
% 23.54/3.47  --include_path                          ""
% 23.54/3.47  --clausifier                            res/vclausify_rel
% 23.54/3.47  --clausifier_options                    ""
% 23.54/3.47  --stdin                                 false
% 23.54/3.47  --stats_out                             all
% 23.54/3.47  
% 23.54/3.47  ------ General Options
% 23.54/3.47  
% 23.54/3.47  --fof                                   false
% 23.54/3.47  --time_out_real                         305.
% 23.54/3.47  --time_out_virtual                      -1.
% 23.54/3.47  --symbol_type_check                     false
% 23.54/3.47  --clausify_out                          false
% 23.54/3.47  --sig_cnt_out                           false
% 23.54/3.47  --trig_cnt_out                          false
% 23.54/3.47  --trig_cnt_out_tolerance                1.
% 23.54/3.47  --trig_cnt_out_sk_spl                   false
% 23.54/3.47  --abstr_cl_out                          false
% 23.54/3.47  
% 23.54/3.47  ------ Global Options
% 23.54/3.47  
% 23.54/3.47  --schedule                              default
% 23.54/3.47  --add_important_lit                     false
% 23.54/3.47  --prop_solver_per_cl                    1000
% 23.54/3.47  --min_unsat_core                        false
% 23.54/3.47  --soft_assumptions                      false
% 23.54/3.47  --soft_lemma_size                       3
% 23.54/3.47  --prop_impl_unit_size                   0
% 23.54/3.47  --prop_impl_unit                        []
% 23.54/3.47  --share_sel_clauses                     true
% 23.54/3.47  --reset_solvers                         false
% 23.54/3.47  --bc_imp_inh                            [conj_cone]
% 23.54/3.47  --conj_cone_tolerance                   3.
% 23.54/3.47  --extra_neg_conj                        none
% 23.54/3.47  --large_theory_mode                     true
% 23.54/3.47  --prolific_symb_bound                   200
% 23.54/3.47  --lt_threshold                          2000
% 23.54/3.47  --clause_weak_htbl                      true
% 23.54/3.47  --gc_record_bc_elim                     false
% 23.54/3.47  
% 23.54/3.47  ------ Preprocessing Options
% 23.54/3.47  
% 23.54/3.47  --preprocessing_flag                    true
% 23.54/3.47  --time_out_prep_mult                    0.1
% 23.54/3.47  --splitting_mode                        input
% 23.54/3.47  --splitting_grd                         true
% 23.54/3.47  --splitting_cvd                         false
% 23.54/3.47  --splitting_cvd_svl                     false
% 23.54/3.47  --splitting_nvd                         32
% 23.54/3.47  --sub_typing                            true
% 23.54/3.47  --prep_gs_sim                           true
% 23.54/3.47  --prep_unflatten                        true
% 23.54/3.47  --prep_res_sim                          true
% 23.54/3.47  --prep_upred                            true
% 23.54/3.47  --prep_sem_filter                       exhaustive
% 23.54/3.47  --prep_sem_filter_out                   false
% 23.54/3.47  --pred_elim                             true
% 23.54/3.47  --res_sim_input                         true
% 23.54/3.47  --eq_ax_congr_red                       true
% 23.54/3.47  --pure_diseq_elim                       true
% 23.54/3.47  --brand_transform                       false
% 23.54/3.47  --non_eq_to_eq                          false
% 23.54/3.47  --prep_def_merge                        true
% 23.54/3.47  --prep_def_merge_prop_impl              false
% 23.54/3.47  --prep_def_merge_mbd                    true
% 23.54/3.47  --prep_def_merge_tr_red                 false
% 23.54/3.47  --prep_def_merge_tr_cl                  false
% 23.54/3.47  --smt_preprocessing                     true
% 23.54/3.47  --smt_ac_axioms                         fast
% 23.54/3.47  --preprocessed_out                      false
% 23.54/3.47  --preprocessed_stats                    false
% 23.54/3.47  
% 23.54/3.47  ------ Abstraction refinement Options
% 23.54/3.47  
% 23.54/3.47  --abstr_ref                             []
% 23.54/3.47  --abstr_ref_prep                        false
% 23.54/3.47  --abstr_ref_until_sat                   false
% 23.54/3.47  --abstr_ref_sig_restrict                funpre
% 23.54/3.47  --abstr_ref_af_restrict_to_split_sk     false
% 23.54/3.47  --abstr_ref_under                       []
% 23.54/3.47  
% 23.54/3.47  ------ SAT Options
% 23.54/3.47  
% 23.54/3.47  --sat_mode                              false
% 23.54/3.47  --sat_fm_restart_options                ""
% 23.54/3.47  --sat_gr_def                            false
% 23.54/3.47  --sat_epr_types                         true
% 23.54/3.47  --sat_non_cyclic_types                  false
% 23.54/3.47  --sat_finite_models                     false
% 23.54/3.47  --sat_fm_lemmas                         false
% 23.54/3.47  --sat_fm_prep                           false
% 23.54/3.47  --sat_fm_uc_incr                        true
% 23.54/3.47  --sat_out_model                         small
% 23.54/3.47  --sat_out_clauses                       false
% 23.54/3.47  
% 23.54/3.47  ------ QBF Options
% 23.54/3.47  
% 23.54/3.47  --qbf_mode                              false
% 23.54/3.47  --qbf_elim_univ                         false
% 23.54/3.47  --qbf_dom_inst                          none
% 23.54/3.47  --qbf_dom_pre_inst                      false
% 23.54/3.47  --qbf_sk_in                             false
% 23.54/3.47  --qbf_pred_elim                         true
% 23.54/3.47  --qbf_split                             512
% 23.54/3.47  
% 23.54/3.47  ------ BMC1 Options
% 23.54/3.47  
% 23.54/3.47  --bmc1_incremental                      false
% 23.54/3.47  --bmc1_axioms                           reachable_all
% 23.54/3.47  --bmc1_min_bound                        0
% 23.54/3.47  --bmc1_max_bound                        -1
% 23.54/3.47  --bmc1_max_bound_default                -1
% 23.54/3.47  --bmc1_symbol_reachability              true
% 23.54/3.47  --bmc1_property_lemmas                  false
% 23.54/3.47  --bmc1_k_induction                      false
% 23.54/3.47  --bmc1_non_equiv_states                 false
% 23.54/3.47  --bmc1_deadlock                         false
% 23.54/3.47  --bmc1_ucm                              false
% 23.54/3.47  --bmc1_add_unsat_core                   none
% 23.54/3.47  --bmc1_unsat_core_children              false
% 23.54/3.47  --bmc1_unsat_core_extrapolate_axioms    false
% 23.54/3.47  --bmc1_out_stat                         full
% 23.54/3.47  --bmc1_ground_init                      false
% 23.54/3.47  --bmc1_pre_inst_next_state              false
% 23.54/3.47  --bmc1_pre_inst_state                   false
% 23.54/3.47  --bmc1_pre_inst_reach_state             false
% 23.54/3.47  --bmc1_out_unsat_core                   false
% 23.54/3.47  --bmc1_aig_witness_out                  false
% 23.54/3.47  --bmc1_verbose                          false
% 23.54/3.47  --bmc1_dump_clauses_tptp                false
% 23.54/3.47  --bmc1_dump_unsat_core_tptp             false
% 23.54/3.47  --bmc1_dump_file                        -
% 23.54/3.47  --bmc1_ucm_expand_uc_limit              128
% 23.54/3.47  --bmc1_ucm_n_expand_iterations          6
% 23.54/3.47  --bmc1_ucm_extend_mode                  1
% 23.54/3.47  --bmc1_ucm_init_mode                    2
% 23.54/3.47  --bmc1_ucm_cone_mode                    none
% 23.54/3.47  --bmc1_ucm_reduced_relation_type        0
% 23.54/3.47  --bmc1_ucm_relax_model                  4
% 23.54/3.47  --bmc1_ucm_full_tr_after_sat            true
% 23.54/3.47  --bmc1_ucm_expand_neg_assumptions       false
% 23.54/3.47  --bmc1_ucm_layered_model                none
% 23.54/3.47  --bmc1_ucm_max_lemma_size               10
% 23.54/3.47  
% 23.54/3.47  ------ AIG Options
% 23.54/3.47  
% 23.54/3.47  --aig_mode                              false
% 23.54/3.47  
% 23.54/3.47  ------ Instantiation Options
% 23.54/3.47  
% 23.54/3.47  --instantiation_flag                    true
% 23.54/3.47  --inst_sos_flag                         true
% 23.54/3.47  --inst_sos_phase                        true
% 23.54/3.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.54/3.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.54/3.47  --inst_lit_sel_side                     none
% 23.54/3.47  --inst_solver_per_active                1400
% 23.54/3.47  --inst_solver_calls_frac                1.
% 23.54/3.47  --inst_passive_queue_type               priority_queues
% 23.54/3.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.54/3.47  --inst_passive_queues_freq              [25;2]
% 23.54/3.47  --inst_dismatching                      true
% 23.54/3.47  --inst_eager_unprocessed_to_passive     true
% 23.54/3.47  --inst_prop_sim_given                   true
% 23.54/3.47  --inst_prop_sim_new                     false
% 23.54/3.47  --inst_subs_new                         false
% 23.54/3.47  --inst_eq_res_simp                      false
% 23.54/3.47  --inst_subs_given                       false
% 23.54/3.47  --inst_orphan_elimination               true
% 23.54/3.47  --inst_learning_loop_flag               true
% 23.54/3.47  --inst_learning_start                   3000
% 23.54/3.47  --inst_learning_factor                  2
% 23.54/3.47  --inst_start_prop_sim_after_learn       3
% 23.54/3.47  --inst_sel_renew                        solver
% 23.54/3.47  --inst_lit_activity_flag                true
% 23.54/3.47  --inst_restr_to_given                   false
% 23.54/3.47  --inst_activity_threshold               500
% 23.54/3.47  --inst_out_proof                        true
% 23.54/3.47  
% 23.54/3.47  ------ Resolution Options
% 23.54/3.47  
% 23.54/3.47  --resolution_flag                       false
% 23.54/3.47  --res_lit_sel                           adaptive
% 23.54/3.47  --res_lit_sel_side                      none
% 23.54/3.47  --res_ordering                          kbo
% 23.54/3.47  --res_to_prop_solver                    active
% 23.54/3.47  --res_prop_simpl_new                    false
% 23.54/3.47  --res_prop_simpl_given                  true
% 23.54/3.47  --res_passive_queue_type                priority_queues
% 23.54/3.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.54/3.47  --res_passive_queues_freq               [15;5]
% 23.54/3.47  --res_forward_subs                      full
% 23.54/3.47  --res_backward_subs                     full
% 23.54/3.47  --res_forward_subs_resolution           true
% 23.54/3.47  --res_backward_subs_resolution          true
% 23.54/3.47  --res_orphan_elimination                true
% 23.54/3.47  --res_time_limit                        2.
% 23.54/3.47  --res_out_proof                         true
% 23.54/3.47  
% 23.54/3.47  ------ Superposition Options
% 23.54/3.47  
% 23.54/3.47  --superposition_flag                    true
% 23.54/3.47  --sup_passive_queue_type                priority_queues
% 23.54/3.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.54/3.47  --sup_passive_queues_freq               [8;1;4]
% 23.54/3.47  --demod_completeness_check              fast
% 23.54/3.47  --demod_use_ground                      true
% 23.54/3.47  --sup_to_prop_solver                    passive
% 23.54/3.47  --sup_prop_simpl_new                    true
% 23.54/3.47  --sup_prop_simpl_given                  true
% 23.54/3.47  --sup_fun_splitting                     true
% 23.54/3.47  --sup_smt_interval                      50000
% 23.54/3.47  
% 23.54/3.47  ------ Superposition Simplification Setup
% 23.54/3.47  
% 23.54/3.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.54/3.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.54/3.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.54/3.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.54/3.47  --sup_full_triv                         [TrivRules;PropSubs]
% 23.54/3.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.54/3.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.54/3.47  --sup_immed_triv                        [TrivRules]
% 23.54/3.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.47  --sup_immed_bw_main                     []
% 23.54/3.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.54/3.47  --sup_input_triv                        [Unflattening;TrivRules]
% 23.54/3.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.47  --sup_input_bw                          []
% 23.54/3.47  
% 23.54/3.47  ------ Combination Options
% 23.54/3.47  
% 23.54/3.47  --comb_res_mult                         3
% 23.54/3.47  --comb_sup_mult                         2
% 23.54/3.47  --comb_inst_mult                        10
% 23.54/3.47  
% 23.54/3.47  ------ Debug Options
% 23.54/3.47  
% 23.54/3.47  --dbg_backtrace                         false
% 23.54/3.47  --dbg_dump_prop_clauses                 false
% 23.54/3.47  --dbg_dump_prop_clauses_file            -
% 23.54/3.47  --dbg_out_stat                          false
% 23.54/3.47  
% 23.54/3.47  
% 23.54/3.47  
% 23.54/3.47  
% 23.54/3.47  ------ Proving...
% 23.54/3.47  
% 23.54/3.47  
% 23.54/3.47  % SZS status Theorem for theBenchmark.p
% 23.54/3.47  
% 23.54/3.47  % SZS output start CNFRefutation for theBenchmark.p
% 23.54/3.47  
% 23.54/3.47  fof(f20,conjecture,(
% 23.54/3.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f21,negated_conjecture,(
% 23.54/3.47    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 23.54/3.47    inference(negated_conjecture,[],[f20])).
% 23.54/3.47  
% 23.54/3.47  fof(f22,plain,(
% 23.54/3.47    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 23.54/3.47    inference(pure_predicate_removal,[],[f21])).
% 23.54/3.47  
% 23.54/3.47  fof(f42,plain,(
% 23.54/3.47    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 23.54/3.47    inference(ennf_transformation,[],[f22])).
% 23.54/3.47  
% 23.54/3.47  fof(f43,plain,(
% 23.54/3.47    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 23.54/3.47    inference(flattening,[],[f42])).
% 23.54/3.47  
% 23.54/3.47  fof(f49,plain,(
% 23.54/3.47    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(sK2))) )),
% 23.54/3.47    introduced(choice_axiom,[])).
% 23.54/3.47  
% 23.54/3.47  fof(f48,plain,(
% 23.54/3.47    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 23.54/3.47    introduced(choice_axiom,[])).
% 23.54/3.47  
% 23.54/3.47  fof(f50,plain,(
% 23.54/3.47    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 23.54/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f49,f48])).
% 23.54/3.47  
% 23.54/3.47  fof(f80,plain,(
% 23.54/3.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 23.54/3.47    inference(cnf_transformation,[],[f50])).
% 23.54/3.47  
% 23.54/3.47  fof(f3,axiom,(
% 23.54/3.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f46,plain,(
% 23.54/3.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.54/3.47    inference(nnf_transformation,[],[f3])).
% 23.54/3.47  
% 23.54/3.47  fof(f55,plain,(
% 23.54/3.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.54/3.47    inference(cnf_transformation,[],[f46])).
% 23.54/3.47  
% 23.54/3.47  fof(f2,axiom,(
% 23.54/3.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f23,plain,(
% 23.54/3.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.54/3.47    inference(ennf_transformation,[],[f2])).
% 23.54/3.47  
% 23.54/3.47  fof(f54,plain,(
% 23.54/3.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f23])).
% 23.54/3.47  
% 23.54/3.47  fof(f78,plain,(
% 23.54/3.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 23.54/3.47    inference(cnf_transformation,[],[f50])).
% 23.54/3.47  
% 23.54/3.47  fof(f18,axiom,(
% 23.54/3.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f40,plain,(
% 23.54/3.47    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 23.54/3.47    inference(ennf_transformation,[],[f18])).
% 23.54/3.47  
% 23.54/3.47  fof(f41,plain,(
% 23.54/3.47    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 23.54/3.47    inference(flattening,[],[f40])).
% 23.54/3.47  
% 23.54/3.47  fof(f75,plain,(
% 23.54/3.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f41])).
% 23.54/3.47  
% 23.54/3.47  fof(f79,plain,(
% 23.54/3.47    v1_funct_1(sK2)),
% 23.54/3.47    inference(cnf_transformation,[],[f50])).
% 23.54/3.47  
% 23.54/3.47  fof(f16,axiom,(
% 23.54/3.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f36,plain,(
% 23.54/3.47    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 23.54/3.47    inference(ennf_transformation,[],[f16])).
% 23.54/3.47  
% 23.54/3.47  fof(f37,plain,(
% 23.54/3.47    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.54/3.47    inference(flattening,[],[f36])).
% 23.54/3.47  
% 23.54/3.47  fof(f47,plain,(
% 23.54/3.47    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.54/3.47    inference(nnf_transformation,[],[f37])).
% 23.54/3.47  
% 23.54/3.47  fof(f71,plain,(
% 23.54/3.47    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.54/3.47    inference(cnf_transformation,[],[f47])).
% 23.54/3.47  
% 23.54/3.47  fof(f81,plain,(
% 23.54/3.47    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 23.54/3.47    inference(cnf_transformation,[],[f50])).
% 23.54/3.47  
% 23.54/3.47  fof(f77,plain,(
% 23.54/3.47    v1_funct_1(sK1)),
% 23.54/3.47    inference(cnf_transformation,[],[f50])).
% 23.54/3.47  
% 23.54/3.47  fof(f17,axiom,(
% 23.54/3.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f38,plain,(
% 23.54/3.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 23.54/3.47    inference(ennf_transformation,[],[f17])).
% 23.54/3.47  
% 23.54/3.47  fof(f39,plain,(
% 23.54/3.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 23.54/3.47    inference(flattening,[],[f38])).
% 23.54/3.47  
% 23.54/3.47  fof(f74,plain,(
% 23.54/3.47    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f39])).
% 23.54/3.47  
% 23.54/3.47  fof(f5,axiom,(
% 23.54/3.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f24,plain,(
% 23.54/3.47    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.54/3.47    inference(ennf_transformation,[],[f5])).
% 23.54/3.47  
% 23.54/3.47  fof(f58,plain,(
% 23.54/3.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f24])).
% 23.54/3.47  
% 23.54/3.47  fof(f15,axiom,(
% 23.54/3.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f35,plain,(
% 23.54/3.47    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.54/3.47    inference(ennf_transformation,[],[f15])).
% 23.54/3.47  
% 23.54/3.47  fof(f70,plain,(
% 23.54/3.47    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.54/3.47    inference(cnf_transformation,[],[f35])).
% 23.54/3.47  
% 23.54/3.47  fof(f82,plain,(
% 23.54/3.47    k2_relset_1(sK0,sK0,sK1) = sK0),
% 23.54/3.47    inference(cnf_transformation,[],[f50])).
% 23.54/3.47  
% 23.54/3.47  fof(f13,axiom,(
% 23.54/3.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f33,plain,(
% 23.54/3.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.54/3.47    inference(ennf_transformation,[],[f13])).
% 23.54/3.47  
% 23.54/3.47  fof(f68,plain,(
% 23.54/3.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.54/3.47    inference(cnf_transformation,[],[f33])).
% 23.54/3.47  
% 23.54/3.47  fof(f1,axiom,(
% 23.54/3.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f44,plain,(
% 23.54/3.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.54/3.47    inference(nnf_transformation,[],[f1])).
% 23.54/3.47  
% 23.54/3.47  fof(f45,plain,(
% 23.54/3.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.54/3.47    inference(flattening,[],[f44])).
% 23.54/3.47  
% 23.54/3.47  fof(f53,plain,(
% 23.54/3.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f45])).
% 23.54/3.47  
% 23.54/3.47  fof(f14,axiom,(
% 23.54/3.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f34,plain,(
% 23.54/3.47    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.54/3.47    inference(ennf_transformation,[],[f14])).
% 23.54/3.47  
% 23.54/3.47  fof(f69,plain,(
% 23.54/3.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.54/3.47    inference(cnf_transformation,[],[f34])).
% 23.54/3.47  
% 23.54/3.47  fof(f9,axiom,(
% 23.54/3.47    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f28,plain,(
% 23.54/3.47    ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.54/3.47    inference(ennf_transformation,[],[f9])).
% 23.54/3.47  
% 23.54/3.47  fof(f63,plain,(
% 23.54/3.47    ( ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f28])).
% 23.54/3.47  
% 23.54/3.47  fof(f12,axiom,(
% 23.54/3.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f31,plain,(
% 23.54/3.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.54/3.47    inference(ennf_transformation,[],[f12])).
% 23.54/3.47  
% 23.54/3.47  fof(f32,plain,(
% 23.54/3.47    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.54/3.47    inference(flattening,[],[f31])).
% 23.54/3.47  
% 23.54/3.47  fof(f67,plain,(
% 23.54/3.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f32])).
% 23.54/3.47  
% 23.54/3.47  fof(f8,axiom,(
% 23.54/3.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f26,plain,(
% 23.54/3.47    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 23.54/3.47    inference(ennf_transformation,[],[f8])).
% 23.54/3.47  
% 23.54/3.47  fof(f27,plain,(
% 23.54/3.47    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.54/3.47    inference(flattening,[],[f26])).
% 23.54/3.47  
% 23.54/3.47  fof(f62,plain,(
% 23.54/3.47    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f27])).
% 23.54/3.47  
% 23.54/3.47  fof(f6,axiom,(
% 23.54/3.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f59,plain,(
% 23.54/3.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 23.54/3.47    inference(cnf_transformation,[],[f6])).
% 23.54/3.47  
% 23.54/3.47  fof(f19,axiom,(
% 23.54/3.47    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f76,plain,(
% 23.54/3.47    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f19])).
% 23.54/3.47  
% 23.54/3.47  fof(f86,plain,(
% 23.54/3.47    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 23.54/3.47    inference(definition_unfolding,[],[f59,f76])).
% 23.54/3.47  
% 23.54/3.47  fof(f11,axiom,(
% 23.54/3.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f29,plain,(
% 23.54/3.47    ! [X0,X1] : (! [X2] : (! [X3] : ((X2 = X3 | (k5_relat_1(X1,X2) != k5_relat_1(X1,X3) | k1_relat_1(X3) != X0 | k1_relat_1(X2) != X0 | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.54/3.47    inference(ennf_transformation,[],[f11])).
% 23.54/3.47  
% 23.54/3.47  fof(f30,plain,(
% 23.54/3.47    ! [X0,X1] : (! [X2] : (! [X3] : (X2 = X3 | k5_relat_1(X1,X2) != k5_relat_1(X1,X3) | k1_relat_1(X3) != X0 | k1_relat_1(X2) != X0 | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.54/3.47    inference(flattening,[],[f29])).
% 23.54/3.47  
% 23.54/3.47  fof(f66,plain,(
% 23.54/3.47    ( ! [X2,X0,X3,X1] : (X2 = X3 | k5_relat_1(X1,X2) != k5_relat_1(X1,X3) | k1_relat_1(X3) != X0 | k1_relat_1(X2) != X0 | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f30])).
% 23.54/3.47  
% 23.54/3.47  fof(f92,plain,(
% 23.54/3.47    ( ! [X2,X3,X1] : (X2 = X3 | k5_relat_1(X1,X2) != k5_relat_1(X1,X3) | k1_relat_1(X2) != k1_relat_1(X3) | k2_relat_1(X1) != k1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.54/3.47    inference(equality_resolution,[],[f66])).
% 23.54/3.47  
% 23.54/3.47  fof(f10,axiom,(
% 23.54/3.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f64,plain,(
% 23.54/3.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 23.54/3.47    inference(cnf_transformation,[],[f10])).
% 23.54/3.47  
% 23.54/3.47  fof(f89,plain,(
% 23.54/3.47    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 23.54/3.47    inference(definition_unfolding,[],[f64,f76])).
% 23.54/3.47  
% 23.54/3.47  fof(f65,plain,(
% 23.54/3.47    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 23.54/3.47    inference(cnf_transformation,[],[f10])).
% 23.54/3.47  
% 23.54/3.47  fof(f88,plain,(
% 23.54/3.47    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 23.54/3.47    inference(definition_unfolding,[],[f65,f76])).
% 23.54/3.47  
% 23.54/3.47  fof(f7,axiom,(
% 23.54/3.47    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 23.54/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.54/3.47  
% 23.54/3.47  fof(f25,plain,(
% 23.54/3.47    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 23.54/3.47    inference(ennf_transformation,[],[f7])).
% 23.54/3.47  
% 23.54/3.47  fof(f61,plain,(
% 23.54/3.47    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 23.54/3.47    inference(cnf_transformation,[],[f25])).
% 23.54/3.47  
% 23.54/3.47  fof(f87,plain,(
% 23.54/3.47    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 23.54/3.47    inference(definition_unfolding,[],[f61,f76])).
% 23.54/3.47  
% 23.54/3.47  fof(f72,plain,(
% 23.54/3.47    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.54/3.47    inference(cnf_transformation,[],[f47])).
% 23.54/3.47  
% 23.54/3.47  fof(f93,plain,(
% 23.54/3.47    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.54/3.47    inference(equality_resolution,[],[f72])).
% 23.54/3.47  
% 23.54/3.47  fof(f83,plain,(
% 23.54/3.47    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 23.54/3.47    inference(cnf_transformation,[],[f50])).
% 23.54/3.47  
% 23.54/3.47  cnf(c_655,plain,( X0 = X0 ),theory(equality) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_51985,plain,
% 23.54/3.47      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_655]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_660,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.54/3.47      theory(equality) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5486,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,X1)
% 23.54/3.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 23.54/3.47      | X2 != X0
% 23.54/3.47      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_660]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_13929,plain,
% 23.54/3.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | X0 != sK2
% 23.54/3.47      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_5486]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_19764,plain,
% 23.54/3.47      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.54/3.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | k6_partfun1(sK0) != sK2
% 23.54/3.47      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_13929]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_19766,plain,
% 23.54/3.47      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | k6_partfun1(sK0) != sK2
% 23.54/3.47      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_19764]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_28,negated_conjecture,
% 23.54/3.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 23.54/3.47      inference(cnf_transformation,[],[f80]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1250,plain,
% 23.54/3.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.54/3.47      inference(cnf_transformation,[],[f55]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1265,plain,
% 23.54/3.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.54/3.47      | r1_tarski(X0,X1) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_2190,plain,
% 23.54/3.47      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_1250,c_1265]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3,plain,
% 23.54/3.47      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.54/3.47      inference(cnf_transformation,[],[f54]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1267,plain,
% 23.54/3.47      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_2260,plain,
% 23.54/3.47      ( k3_xboole_0(sK2,k2_zfmisc_1(sK0,sK0)) = sK2 ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_2190,c_1267]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_30,negated_conjecture,
% 23.54/3.47      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 23.54/3.47      inference(cnf_transformation,[],[f78]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1248,plain,
% 23.54/3.47      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_24,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.54/3.47      | ~ v1_funct_1(X0)
% 23.54/3.47      | ~ v1_funct_1(X3)
% 23.54/3.47      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 23.54/3.47      inference(cnf_transformation,[],[f75]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1251,plain,
% 23.54/3.47      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 23.54/3.47      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 23.54/3.47      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.54/3.47      | v1_funct_1(X5) != iProver_top
% 23.54/3.47      | v1_funct_1(X4) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_4759,plain,
% 23.54/3.47      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
% 23.54/3.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.54/3.47      | v1_funct_1(X2) != iProver_top
% 23.54/3.47      | v1_funct_1(sK2) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_1250,c_1251]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_29,negated_conjecture,
% 23.54/3.47      ( v1_funct_1(sK2) ),
% 23.54/3.47      inference(cnf_transformation,[],[f79]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_34,plain,
% 23.54/3.47      ( v1_funct_1(sK2) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_4959,plain,
% 23.54/3.47      ( v1_funct_1(X2) != iProver_top
% 23.54/3.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.54/3.47      | k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2) ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_4759,c_34]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_4960,plain,
% 23.54/3.47      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
% 23.54/3.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.54/3.47      | v1_funct_1(X2) != iProver_top ),
% 23.54/3.47      inference(renaming,[status(thm)],[c_4959]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_4969,plain,
% 23.54/3.47      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 23.54/3.47      | v1_funct_1(sK1) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_1248,c_4960]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_21,plain,
% 23.54/3.47      ( ~ r2_relset_1(X0,X1,X2,X3)
% 23.54/3.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.54/3.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.54/3.47      | X3 = X2 ),
% 23.54/3.47      inference(cnf_transformation,[],[f71]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_27,negated_conjecture,
% 23.54/3.47      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
% 23.54/3.47      inference(cnf_transformation,[],[f81]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_393,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | X3 = X0
% 23.54/3.47      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
% 23.54/3.47      | sK1 != X3
% 23.54/3.47      | sK0 != X2
% 23.54/3.47      | sK0 != X1 ),
% 23.54/3.47      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_394,plain,
% 23.54/3.47      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 23.54/3.47      inference(unflattening,[status(thm)],[c_393]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_396,plain,
% 23.54/3.47      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_394,c_30]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1245,plain,
% 23.54/3.47      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 23.54/3.47      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_31,negated_conjecture,
% 23.54/3.47      ( v1_funct_1(sK1) ),
% 23.54/3.47      inference(cnf_transformation,[],[f77]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_22,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.54/3.47      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.54/3.47      | ~ v1_funct_1(X0)
% 23.54/3.47      | ~ v1_funct_1(X3) ),
% 23.54/3.47      inference(cnf_transformation,[],[f74]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1314,plain,
% 23.54/3.47      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | ~ v1_funct_1(sK1)
% 23.54/3.47      | ~ v1_funct_1(sK2) ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_22]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1547,plain,
% 23.54/3.47      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_1245,c_31,c_30,c_29,c_28,c_394,c_1314]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_4970,plain,
% 23.54/3.47      ( k5_relat_1(sK1,sK2) = sK1 | v1_funct_1(sK1) != iProver_top ),
% 23.54/3.47      inference(light_normalisation,[status(thm)],[c_4969,c_1547]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_32,plain,
% 23.54/3.47      ( v1_funct_1(sK1) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5537,plain,
% 23.54/3.47      ( k5_relat_1(sK1,sK2) = sK1 ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_4970,c_32]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_7,plain,
% 23.54/3.47      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 23.54/3.47      | ~ v1_relat_1(X1)
% 23.54/3.47      | ~ v1_relat_1(X0) ),
% 23.54/3.47      inference(cnf_transformation,[],[f58]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1263,plain,
% 23.54/3.47      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 23.54/3.47      | v1_relat_1(X0) != iProver_top
% 23.54/3.47      | v1_relat_1(X1) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5539,plain,
% 23.54/3.47      ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK2)) = iProver_top
% 23.54/3.47      | v1_relat_1(sK1) != iProver_top
% 23.54/3.47      | v1_relat_1(sK2) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_5537,c_1263]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_19,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 23.54/3.47      inference(cnf_transformation,[],[f70]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1254,plain,
% 23.54/3.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 23.54/3.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3078,plain,
% 23.54/3.47      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_1248,c_1254]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_26,negated_conjecture,
% 23.54/3.47      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 23.54/3.47      inference(cnf_transformation,[],[f82]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3079,plain,
% 23.54/3.47      ( k2_relat_1(sK1) = sK0 ),
% 23.54/3.47      inference(light_normalisation,[status(thm)],[c_3078,c_26]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5547,plain,
% 23.54/3.47      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top
% 23.54/3.47      | v1_relat_1(sK1) != iProver_top
% 23.54/3.47      | v1_relat_1(sK2) != iProver_top ),
% 23.54/3.47      inference(light_normalisation,[status(thm)],[c_5539,c_3079]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_33,plain,
% 23.54/3.47      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_35,plain,
% 23.54/3.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_17,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | v1_relat_1(X0) ),
% 23.54/3.47      inference(cnf_transformation,[],[f68]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1381,plain,
% 23.54/3.47      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.54/3.47      | v1_relat_1(sK2) ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_17]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1382,plain,
% 23.54/3.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.54/3.47      | v1_relat_1(sK2) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1384,plain,
% 23.54/3.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 23.54/3.47      | v1_relat_1(sK2) = iProver_top ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_1382]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1391,plain,
% 23.54/3.47      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.54/3.47      | v1_relat_1(sK1) ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_17]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1392,plain,
% 23.54/3.47      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.54/3.47      | v1_relat_1(sK1) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1394,plain,
% 23.54/3.47      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 23.54/3.47      | v1_relat_1(sK1) = iProver_top ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_1392]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5558,plain,
% 23.54/3.47      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_5547,c_33,c_35,c_1384,c_1394]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_0,plain,
% 23.54/3.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.54/3.47      inference(cnf_transformation,[],[f53]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1269,plain,
% 23.54/3.47      ( X0 = X1
% 23.54/3.47      | r1_tarski(X0,X1) != iProver_top
% 23.54/3.47      | r1_tarski(X1,X0) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5563,plain,
% 23.54/3.47      ( k2_relat_1(sK2) = sK0
% 23.54/3.47      | r1_tarski(k2_relat_1(sK2),sK0) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_5558,c_1269]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3077,plain,
% 23.54/3.47      ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_1250,c_1254]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_18,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 23.54/3.47      inference(cnf_transformation,[],[f69]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1255,plain,
% 23.54/3.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.54/3.47      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3625,plain,
% 23.54/3.47      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
% 23.54/3.47      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_3077,c_1255]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3802,plain,
% 23.54/3.47      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_3625,c_35]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3806,plain,
% 23.54/3.47      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_3802,c_1265]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3897,plain,
% 23.54/3.47      ( k2_relat_1(sK2) = sK0
% 23.54/3.47      | r1_tarski(sK0,k2_relat_1(sK2)) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_3806,c_1269]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_6258,plain,
% 23.54/3.47      ( k2_relat_1(sK2) = sK0 ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_5563,c_33,c_35,c_1384,c_1394,c_3897,c_5547]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1256,plain,
% 23.54/3.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.54/3.47      | v1_relat_1(X0) = iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_2356,plain,
% 23.54/3.47      ( v1_relat_1(sK2) = iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_1250,c_1256]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_12,plain,
% 23.54/3.47      ( ~ v1_relat_1(X0)
% 23.54/3.47      | k3_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k7_relat_1(X0,X1) ),
% 23.54/3.47      inference(cnf_transformation,[],[f63]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1260,plain,
% 23.54/3.47      ( k3_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k7_relat_1(X0,X1)
% 23.54/3.47      | v1_relat_1(X0) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_2572,plain,
% 23.54/3.47      ( k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2))) = k7_relat_1(sK2,X0) ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_2356,c_1260]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_6269,plain,
% 23.54/3.47      ( k3_xboole_0(sK2,k2_zfmisc_1(X0,sK0)) = k7_relat_1(sK2,X0) ),
% 23.54/3.47      inference(demodulation,[status(thm)],[c_6258,c_2572]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_11755,plain,
% 23.54/3.47      ( k7_relat_1(sK2,sK0) = sK2 ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_2260,c_6269]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_16,plain,
% 23.54/3.47      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 23.54/3.47      | ~ v1_funct_1(X0)
% 23.54/3.47      | ~ v1_funct_1(X1)
% 23.54/3.47      | ~ v1_relat_1(X0)
% 23.54/3.47      | ~ v1_relat_1(X1)
% 23.54/3.47      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 23.54/3.47      inference(cnf_transformation,[],[f67]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1257,plain,
% 23.54/3.47      ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
% 23.54/3.47      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 23.54/3.47      | v1_funct_1(X0) != iProver_top
% 23.54/3.47      | v1_funct_1(X1) != iProver_top
% 23.54/3.47      | v1_relat_1(X0) != iProver_top
% 23.54/3.47      | v1_relat_1(X1) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5540,plain,
% 23.54/3.47      ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) = iProver_top
% 23.54/3.47      | v1_funct_1(sK1) != iProver_top
% 23.54/3.47      | v1_funct_1(sK2) != iProver_top
% 23.54/3.47      | v1_relat_1(sK1) != iProver_top
% 23.54/3.47      | v1_relat_1(sK2) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_5537,c_1257]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5546,plain,
% 23.54/3.47      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 23.54/3.47      | v1_funct_1(sK1) != iProver_top
% 23.54/3.47      | v1_funct_1(sK2) != iProver_top
% 23.54/3.47      | v1_relat_1(sK1) != iProver_top
% 23.54/3.47      | v1_relat_1(sK2) != iProver_top ),
% 23.54/3.47      inference(light_normalisation,[status(thm)],[c_5540,c_3079]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5681,plain,
% 23.54/3.47      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_5546,c_32,c_33,c_34,c_35,c_1384,c_1394]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_11,plain,
% 23.54/3.47      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 23.54/3.47      | ~ v1_relat_1(X1)
% 23.54/3.47      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 23.54/3.47      inference(cnf_transformation,[],[f62]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1261,plain,
% 23.54/3.47      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 23.54/3.47      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 23.54/3.47      | v1_relat_1(X0) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5688,plain,
% 23.54/3.47      ( k1_relat_1(k7_relat_1(sK2,sK0)) = sK0
% 23.54/3.47      | v1_relat_1(sK2) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_5681,c_1261]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_6313,plain,
% 23.54/3.47      ( k1_relat_1(k7_relat_1(sK2,sK0)) = sK0 ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_5688,c_35,c_1384]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_11807,plain,
% 23.54/3.47      ( k1_relat_1(sK2) = sK0 ),
% 23.54/3.47      inference(demodulation,[status(thm)],[c_11755,c_6313]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_9,plain,
% 23.54/3.47      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 23.54/3.47      inference(cnf_transformation,[],[f86]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_15,plain,
% 23.54/3.47      ( ~ v1_funct_1(X0)
% 23.54/3.47      | ~ v1_funct_1(X1)
% 23.54/3.47      | ~ v1_funct_1(X2)
% 23.54/3.47      | ~ v1_relat_1(X2)
% 23.54/3.47      | ~ v1_relat_1(X0)
% 23.54/3.47      | ~ v1_relat_1(X1)
% 23.54/3.47      | X0 = X1
% 23.54/3.47      | k5_relat_1(X2,X0) != k5_relat_1(X2,X1)
% 23.54/3.47      | k1_relat_1(X0) != k1_relat_1(X1)
% 23.54/3.47      | k1_relat_1(X0) != k2_relat_1(X2) ),
% 23.54/3.47      inference(cnf_transformation,[],[f92]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1258,plain,
% 23.54/3.47      ( X0 = X1
% 23.54/3.47      | k5_relat_1(X2,X0) != k5_relat_1(X2,X1)
% 23.54/3.47      | k1_relat_1(X0) != k1_relat_1(X1)
% 23.54/3.47      | k1_relat_1(X0) != k2_relat_1(X2)
% 23.54/3.47      | v1_funct_1(X0) != iProver_top
% 23.54/3.47      | v1_funct_1(X1) != iProver_top
% 23.54/3.47      | v1_funct_1(X2) != iProver_top
% 23.54/3.47      | v1_relat_1(X0) != iProver_top
% 23.54/3.47      | v1_relat_1(X1) != iProver_top
% 23.54/3.47      | v1_relat_1(X2) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5541,plain,
% 23.54/3.47      ( k5_relat_1(sK1,X0) != sK1
% 23.54/3.47      | k1_relat_1(X0) != k1_relat_1(sK2)
% 23.54/3.47      | k1_relat_1(sK2) != k2_relat_1(sK1)
% 23.54/3.47      | sK2 = X0
% 23.54/3.47      | v1_funct_1(X0) != iProver_top
% 23.54/3.47      | v1_funct_1(sK1) != iProver_top
% 23.54/3.47      | v1_funct_1(sK2) != iProver_top
% 23.54/3.47      | v1_relat_1(X0) != iProver_top
% 23.54/3.47      | v1_relat_1(sK1) != iProver_top
% 23.54/3.47      | v1_relat_1(sK2) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_5537,c_1258]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5545,plain,
% 23.54/3.47      ( k5_relat_1(sK1,X0) != sK1
% 23.54/3.47      | k1_relat_1(X0) != k1_relat_1(sK2)
% 23.54/3.47      | k1_relat_1(sK2) != sK0
% 23.54/3.47      | sK2 = X0
% 23.54/3.47      | v1_funct_1(X0) != iProver_top
% 23.54/3.47      | v1_funct_1(sK1) != iProver_top
% 23.54/3.47      | v1_funct_1(sK2) != iProver_top
% 23.54/3.47      | v1_relat_1(X0) != iProver_top
% 23.54/3.47      | v1_relat_1(sK1) != iProver_top
% 23.54/3.47      | v1_relat_1(sK2) != iProver_top ),
% 23.54/3.47      inference(light_normalisation,[status(thm)],[c_5541,c_3079]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5912,plain,
% 23.54/3.47      ( k5_relat_1(sK1,X0) != sK1
% 23.54/3.47      | k1_relat_1(X0) != k1_relat_1(sK2)
% 23.54/3.47      | k1_relat_1(sK2) != sK0
% 23.54/3.47      | sK2 = X0
% 23.54/3.47      | v1_funct_1(X0) != iProver_top
% 23.54/3.47      | v1_relat_1(X0) != iProver_top ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_5545,c_32,c_33,c_34,c_35,c_1384,c_1394]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5918,plain,
% 23.54/3.47      ( k5_relat_1(sK1,k6_partfun1(X0)) != sK1
% 23.54/3.47      | k1_relat_1(sK2) != X0
% 23.54/3.47      | k1_relat_1(sK2) != sK0
% 23.54/3.47      | k6_partfun1(X0) = sK2
% 23.54/3.47      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 23.54/3.47      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_9,c_5912]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_14,plain,
% 23.54/3.47      ( v1_relat_1(k6_partfun1(X0)) ),
% 23.54/3.47      inference(cnf_transformation,[],[f89]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_13,plain,
% 23.54/3.47      ( v1_funct_1(k6_partfun1(X0)) ),
% 23.54/3.47      inference(cnf_transformation,[],[f88]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_5923,plain,
% 23.54/3.47      ( ~ v1_funct_1(k6_partfun1(X0))
% 23.54/3.47      | ~ v1_relat_1(k6_partfun1(X0))
% 23.54/3.47      | k5_relat_1(sK1,k6_partfun1(X0)) != sK1
% 23.54/3.47      | k1_relat_1(sK2) != X0
% 23.54/3.47      | k1_relat_1(sK2) != sK0
% 23.54/3.47      | k6_partfun1(X0) = sK2 ),
% 23.54/3.47      inference(predicate_to_equality_rev,[status(thm)],[c_5918]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_6668,plain,
% 23.54/3.47      ( k5_relat_1(sK1,k6_partfun1(X0)) != sK1
% 23.54/3.47      | k1_relat_1(sK2) != X0
% 23.54/3.47      | k1_relat_1(sK2) != sK0
% 23.54/3.47      | k6_partfun1(X0) = sK2 ),
% 23.54/3.47      inference(global_propositional_subsumption,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_5918,c_14,c_13,c_5923]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_6670,plain,
% 23.54/3.47      ( k5_relat_1(sK1,k6_partfun1(sK0)) != sK1
% 23.54/3.47      | k1_relat_1(sK2) != sK0
% 23.54/3.47      | k6_partfun1(sK0) = sK2 ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_6668]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_2357,plain,
% 23.54/3.47      ( v1_relat_1(sK1) = iProver_top ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_1248,c_1256]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_10,plain,
% 23.54/3.47      ( ~ v1_relat_1(X0)
% 23.54/3.47      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 23.54/3.47      inference(cnf_transformation,[],[f87]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1262,plain,
% 23.54/3.47      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 23.54/3.47      | v1_relat_1(X0) != iProver_top ),
% 23.54/3.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_2577,plain,
% 23.54/3.47      ( k5_relat_1(sK1,k6_partfun1(k2_relat_1(sK1))) = sK1 ),
% 23.54/3.47      inference(superposition,[status(thm)],[c_2357,c_1262]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_3086,plain,
% 23.54/3.47      ( k5_relat_1(sK1,k6_partfun1(sK0)) = sK1 ),
% 23.54/3.47      inference(demodulation,[status(thm)],[c_3079,c_2577]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1438,plain,
% 23.54/3.47      ( sK2 = sK2 ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_655]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_656,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1309,plain,
% 23.54/3.47      ( k6_partfun1(sK0) != X0 | sK2 != X0 | sK2 = k6_partfun1(sK0) ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_656]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_1361,plain,
% 23.54/3.47      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 23.54/3.47      inference(instantiation,[status(thm)],[c_1309]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_20,plain,
% 23.54/3.47      ( r2_relset_1(X0,X1,X2,X2)
% 23.54/3.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 23.54/3.47      inference(cnf_transformation,[],[f93]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_25,negated_conjecture,
% 23.54/3.47      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 23.54/3.47      inference(cnf_transformation,[],[f83]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_383,plain,
% 23.54/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.54/3.47      | k6_partfun1(sK0) != X0
% 23.54/3.47      | sK2 != X0
% 23.54/3.47      | sK0 != X2
% 23.54/3.47      | sK0 != X1 ),
% 23.54/3.47      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(c_384,plain,
% 23.54/3.47      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.54/3.47      | sK2 != k6_partfun1(sK0) ),
% 23.54/3.47      inference(unflattening,[status(thm)],[c_383]) ).
% 23.54/3.47  
% 23.54/3.47  cnf(contradiction,plain,
% 23.54/3.47      ( $false ),
% 23.54/3.47      inference(minisat,
% 23.54/3.47                [status(thm)],
% 23.54/3.47                [c_51985,c_19766,c_11807,c_6670,c_3086,c_1438,c_1361,
% 23.54/3.47                 c_384,c_28]) ).
% 23.54/3.47  
% 23.54/3.47  
% 23.54/3.47  % SZS output end CNFRefutation for theBenchmark.p
% 23.54/3.47  
% 23.54/3.47  ------                               Statistics
% 23.54/3.47  
% 23.54/3.47  ------ General
% 23.54/3.47  
% 23.54/3.47  abstr_ref_over_cycles:                  0
% 23.54/3.47  abstr_ref_under_cycles:                 0
% 23.54/3.47  gc_basic_clause_elim:                   0
% 23.54/3.47  forced_gc_time:                         0
% 23.54/3.47  parsing_time:                           0.011
% 23.54/3.47  unif_index_cands_time:                  0.
% 23.54/3.47  unif_index_add_time:                    0.
% 23.54/3.47  orderings_time:                         0.
% 23.54/3.47  out_proof_time:                         0.038
% 23.54/3.47  total_time:                             2.594
% 23.54/3.47  num_of_symbols:                         49
% 23.54/3.47  num_of_terms:                           66695
% 23.54/3.47  
% 23.54/3.47  ------ Preprocessing
% 23.54/3.47  
% 23.54/3.47  num_of_splits:                          0
% 23.54/3.47  num_of_split_atoms:                     0
% 23.54/3.47  num_of_reused_defs:                     0
% 23.54/3.47  num_eq_ax_congr_red:                    12
% 23.54/3.47  num_of_sem_filtered_clauses:            1
% 23.54/3.47  num_of_subtypes:                        0
% 23.54/3.47  monotx_restored_types:                  0
% 23.54/3.47  sat_num_of_epr_types:                   0
% 23.54/3.47  sat_num_of_non_cyclic_types:            0
% 23.54/3.47  sat_guarded_non_collapsed_types:        0
% 23.54/3.47  num_pure_diseq_elim:                    0
% 23.54/3.47  simp_replaced_by:                       0
% 23.54/3.47  res_preprocessed:                       148
% 23.54/3.47  prep_upred:                             0
% 23.54/3.47  prep_unflattend:                        11
% 23.54/3.47  smt_new_axioms:                         0
% 23.54/3.47  pred_elim_cands:                        4
% 23.54/3.47  pred_elim:                              1
% 23.54/3.47  pred_elim_cl:                           1
% 23.54/3.47  pred_elim_cycles:                       3
% 23.54/3.47  merged_defs:                            8
% 23.54/3.47  merged_defs_ncl:                        0
% 23.54/3.47  bin_hyper_res:                          8
% 23.54/3.47  prep_cycles:                            4
% 23.54/3.47  pred_elim_time:                         0.003
% 23.54/3.47  splitting_time:                         0.
% 23.54/3.47  sem_filter_time:                        0.
% 23.54/3.47  monotx_time:                            0.001
% 23.54/3.47  subtype_inf_time:                       0.
% 23.54/3.47  
% 23.54/3.47  ------ Problem properties
% 23.54/3.47  
% 23.54/3.47  clauses:                                29
% 23.54/3.47  conjectures:                            5
% 23.54/3.47  epr:                                    4
% 23.54/3.47  horn:                                   29
% 23.54/3.47  ground:                                 8
% 23.54/3.47  unary:                                  10
% 23.54/3.47  binary:                                 11
% 23.54/3.47  lits:                                   72
% 23.54/3.47  lits_eq:                                19
% 23.54/3.47  fd_pure:                                0
% 23.54/3.47  fd_pseudo:                              0
% 23.54/3.47  fd_cond:                                0
% 23.54/3.47  fd_pseudo_cond:                         2
% 23.54/3.47  ac_symbols:                             0
% 23.54/3.47  
% 23.54/3.47  ------ Propositional Solver
% 23.54/3.47  
% 23.54/3.47  prop_solver_calls:                      41
% 23.54/3.47  prop_fast_solver_calls:                 2871
% 23.54/3.47  smt_solver_calls:                       0
% 23.54/3.47  smt_fast_solver_calls:                  0
% 23.54/3.47  prop_num_of_clauses:                    26284
% 23.54/3.47  prop_preprocess_simplified:             46122
% 23.54/3.47  prop_fo_subsumed:                       384
% 23.54/3.47  prop_solver_time:                       0.
% 23.54/3.47  smt_solver_time:                        0.
% 23.54/3.47  smt_fast_solver_time:                   0.
% 23.54/3.47  prop_fast_solver_time:                  0.
% 23.54/3.47  prop_unsat_core_time:                   0.005
% 23.54/3.47  
% 23.54/3.47  ------ QBF
% 23.54/3.47  
% 23.54/3.47  qbf_q_res:                              0
% 23.54/3.47  qbf_num_tautologies:                    0
% 23.54/3.47  qbf_prep_cycles:                        0
% 23.54/3.47  
% 23.54/3.47  ------ BMC1
% 23.54/3.47  
% 23.54/3.47  bmc1_current_bound:                     -1
% 23.54/3.47  bmc1_last_solved_bound:                 -1
% 23.54/3.47  bmc1_unsat_core_size:                   -1
% 23.54/3.47  bmc1_unsat_core_parents_size:           -1
% 23.54/3.47  bmc1_merge_next_fun:                    0
% 23.54/3.47  bmc1_unsat_core_clauses_time:           0.
% 23.54/3.47  
% 23.54/3.47  ------ Instantiation
% 23.54/3.47  
% 23.54/3.47  inst_num_of_clauses:                    148
% 23.54/3.47  inst_num_in_passive:                    24
% 23.54/3.47  inst_num_in_active:                     2600
% 23.54/3.47  inst_num_in_unprocessed:                58
% 23.54/3.47  inst_num_of_loops:                      3067
% 23.54/3.47  inst_num_of_learning_restarts:          1
% 23.54/3.47  inst_num_moves_active_passive:          462
% 23.54/3.47  inst_lit_activity:                      0
% 23.54/3.47  inst_lit_activity_moves:                2
% 23.54/3.47  inst_num_tautologies:                   0
% 23.54/3.47  inst_num_prop_implied:                  0
% 23.54/3.47  inst_num_existing_simplified:           0
% 23.54/3.47  inst_num_eq_res_simplified:             0
% 23.54/3.47  inst_num_child_elim:                    0
% 23.54/3.47  inst_num_of_dismatching_blockings:      4909
% 23.54/3.47  inst_num_of_non_proper_insts:           8484
% 23.54/3.47  inst_num_of_duplicates:                 0
% 23.54/3.47  inst_inst_num_from_inst_to_res:         0
% 23.54/3.47  inst_dismatching_checking_time:         0.
% 23.54/3.47  
% 23.54/3.47  ------ Resolution
% 23.54/3.47  
% 23.54/3.47  res_num_of_clauses:                     44
% 23.54/3.47  res_num_in_passive:                     44
% 23.54/3.47  res_num_in_active:                      0
% 23.54/3.47  res_num_of_loops:                       152
% 23.54/3.47  res_forward_subset_subsumed:            775
% 23.54/3.47  res_backward_subset_subsumed:           0
% 23.54/3.47  res_forward_subsumed:                   0
% 23.54/3.47  res_backward_subsumed:                  0
% 23.54/3.47  res_forward_subsumption_resolution:     0
% 23.54/3.47  res_backward_subsumption_resolution:    0
% 23.54/3.47  res_clause_to_clause_subsumption:       4333
% 23.54/3.47  res_orphan_elimination:                 0
% 23.54/3.47  res_tautology_del:                      390
% 23.54/3.47  res_num_eq_res_simplified:              0
% 23.54/3.47  res_num_sel_changes:                    0
% 23.54/3.47  res_moves_from_active_to_pass:          0
% 23.54/3.47  
% 23.54/3.47  ------ Superposition
% 23.54/3.47  
% 23.54/3.47  sup_time_total:                         0.
% 23.54/3.47  sup_time_generating:                    0.
% 23.54/3.47  sup_time_sim_full:                      0.
% 23.54/3.47  sup_time_sim_immed:                     0.
% 23.54/3.47  
% 23.54/3.47  sup_num_of_clauses:                     1493
% 23.54/3.47  sup_num_in_active:                      562
% 23.54/3.47  sup_num_in_passive:                     931
% 23.54/3.47  sup_num_of_loops:                       612
% 23.54/3.47  sup_fw_superposition:                   1221
% 23.54/3.47  sup_bw_superposition:                   1021
% 23.54/3.47  sup_immediate_simplified:               685
% 23.54/3.47  sup_given_eliminated:                   2
% 23.54/3.47  comparisons_done:                       0
% 23.54/3.47  comparisons_avoided:                    0
% 23.54/3.47  
% 23.54/3.47  ------ Simplifications
% 23.54/3.47  
% 23.54/3.47  
% 23.54/3.47  sim_fw_subset_subsumed:                 28
% 23.54/3.47  sim_bw_subset_subsumed:                 48
% 23.54/3.47  sim_fw_subsumed:                        115
% 23.54/3.47  sim_bw_subsumed:                        3
% 23.54/3.47  sim_fw_subsumption_res:                 0
% 23.54/3.47  sim_bw_subsumption_res:                 0
% 23.54/3.47  sim_tautology_del:                      2
% 23.54/3.47  sim_eq_tautology_del:                   178
% 23.54/3.47  sim_eq_res_simp:                        43
% 23.54/3.47  sim_fw_demodulated:                     211
% 23.54/3.47  sim_bw_demodulated:                     42
% 23.54/3.47  sim_light_normalised:                   492
% 23.54/3.47  sim_joinable_taut:                      0
% 23.54/3.47  sim_joinable_simp:                      0
% 23.54/3.47  sim_ac_normalised:                      0
% 23.54/3.47  sim_smt_subsumption:                    0
% 23.54/3.47  
%------------------------------------------------------------------------------
