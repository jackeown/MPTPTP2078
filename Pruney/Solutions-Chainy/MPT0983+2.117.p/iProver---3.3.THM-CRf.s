%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:10 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  213 (1269 expanded)
%              Number of clauses        :  120 ( 382 expanded)
%              Number of leaves         :   27 ( 315 expanded)
%              Depth                    :   23
%              Number of atoms          :  647 (7923 expanded)
%              Number of equality atoms :  243 ( 653 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f54,f53])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f21,axiom,(
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

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f95,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f75,f85])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1154,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3968,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1154])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4287,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3968,c_42])).

cnf(c_4288,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4287])).

cnf(c_4298,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_4288])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1762,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_2256,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_3386,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2256])).

cnf(c_4409,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4298,c_38,c_36,c_35,c_33,c_3386])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1152,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4415,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4409,c_1152])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_31,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_413,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_414,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_467,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_414])).

cnf(c_468,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_478,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_468,c_2])).

cnf(c_479,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2788,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1162])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1161,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2894,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2788,c_1161])).

cnf(c_2789,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1162])).

cnf(c_2949,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2789,c_1161])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_13])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_2594,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1143])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1166,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2806,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2594,c_1166])).

cnf(c_2952,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2806,c_2894])).

cnf(c_2953,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2952])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_396,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_27,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_404,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_396,c_27])).

cnf(c_1144,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_4412,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4409,c_1144])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1157,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4928,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4409,c_1157])).

cnf(c_5285,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4412,c_39,c_41,c_42,c_44,c_4928])).

cnf(c_15,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1160,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5289,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5285,c_1160])).

cnf(c_16,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_5290,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5289,c_16])).

cnf(c_15482,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4415,c_39,c_40,c_41,c_42,c_43,c_44,c_479,c_2806,c_2894,c_2949,c_5290])).

cnf(c_15483,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15482])).

cnf(c_15486,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15483,c_5285])).

cnf(c_18,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1159,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15489,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15486,c_1159])).

cnf(c_15576,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15489,c_1148])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_15584,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15576,c_8])).

cnf(c_676,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7107,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_7109,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7107])).

cnf(c_667,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2664,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_5222,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2664])).

cnf(c_5223,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5222])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1155,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2368,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1155])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1163,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3354,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2368,c_1163])).

cnf(c_2895,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2894])).

cnf(c_1960,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1961,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1960])).

cnf(c_1963,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1961])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1693,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0))
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1697,plain,
    ( k1_xboole_0 = k6_partfun1(X0)
    | v1_xboole_0(k6_partfun1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_1699,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | v1_xboole_0(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_666,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1606,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1543,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1547,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1543])).

cnf(c_1397,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1399,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
    | v2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_110,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_107,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_109,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_104,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_106,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15584,c_7109,c_5290,c_5223,c_3354,c_2953,c_2949,c_2895,c_2894,c_1963,c_1699,c_1606,c_1547,c_1399,c_478,c_112,c_109,c_106,c_84])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.54/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/1.01  
% 3.54/1.01  ------  iProver source info
% 3.54/1.01  
% 3.54/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.54/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/1.01  git: non_committed_changes: false
% 3.54/1.01  git: last_make_outside_of_git: false
% 3.54/1.01  
% 3.54/1.01  ------ 
% 3.54/1.01  
% 3.54/1.01  ------ Input Options
% 3.54/1.01  
% 3.54/1.01  --out_options                           all
% 3.54/1.01  --tptp_safe_out                         true
% 3.54/1.01  --problem_path                          ""
% 3.54/1.01  --include_path                          ""
% 3.54/1.01  --clausifier                            res/vclausify_rel
% 3.54/1.01  --clausifier_options                    --mode clausify
% 3.54/1.01  --stdin                                 false
% 3.54/1.01  --stats_out                             all
% 3.54/1.01  
% 3.54/1.01  ------ General Options
% 3.54/1.01  
% 3.54/1.01  --fof                                   false
% 3.54/1.01  --time_out_real                         305.
% 3.54/1.01  --time_out_virtual                      -1.
% 3.54/1.01  --symbol_type_check                     false
% 3.54/1.01  --clausify_out                          false
% 3.54/1.01  --sig_cnt_out                           false
% 3.54/1.01  --trig_cnt_out                          false
% 3.54/1.01  --trig_cnt_out_tolerance                1.
% 3.54/1.01  --trig_cnt_out_sk_spl                   false
% 3.54/1.01  --abstr_cl_out                          false
% 3.54/1.01  
% 3.54/1.01  ------ Global Options
% 3.54/1.01  
% 3.54/1.01  --schedule                              default
% 3.54/1.01  --add_important_lit                     false
% 3.54/1.01  --prop_solver_per_cl                    1000
% 3.54/1.01  --min_unsat_core                        false
% 3.54/1.01  --soft_assumptions                      false
% 3.54/1.01  --soft_lemma_size                       3
% 3.54/1.01  --prop_impl_unit_size                   0
% 3.54/1.01  --prop_impl_unit                        []
% 3.54/1.01  --share_sel_clauses                     true
% 3.54/1.01  --reset_solvers                         false
% 3.54/1.01  --bc_imp_inh                            [conj_cone]
% 3.54/1.01  --conj_cone_tolerance                   3.
% 3.54/1.01  --extra_neg_conj                        none
% 3.54/1.01  --large_theory_mode                     true
% 3.54/1.01  --prolific_symb_bound                   200
% 3.54/1.01  --lt_threshold                          2000
% 3.54/1.01  --clause_weak_htbl                      true
% 3.54/1.01  --gc_record_bc_elim                     false
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing Options
% 3.54/1.01  
% 3.54/1.01  --preprocessing_flag                    true
% 3.54/1.01  --time_out_prep_mult                    0.1
% 3.54/1.01  --splitting_mode                        input
% 3.54/1.01  --splitting_grd                         true
% 3.54/1.01  --splitting_cvd                         false
% 3.54/1.01  --splitting_cvd_svl                     false
% 3.54/1.01  --splitting_nvd                         32
% 3.54/1.01  --sub_typing                            true
% 3.54/1.01  --prep_gs_sim                           true
% 3.54/1.01  --prep_unflatten                        true
% 3.54/1.01  --prep_res_sim                          true
% 3.54/1.01  --prep_upred                            true
% 3.54/1.01  --prep_sem_filter                       exhaustive
% 3.54/1.01  --prep_sem_filter_out                   false
% 3.54/1.01  --pred_elim                             true
% 3.54/1.01  --res_sim_input                         true
% 3.54/1.01  --eq_ax_congr_red                       true
% 3.54/1.01  --pure_diseq_elim                       true
% 3.54/1.01  --brand_transform                       false
% 3.54/1.01  --non_eq_to_eq                          false
% 3.54/1.01  --prep_def_merge                        true
% 3.54/1.01  --prep_def_merge_prop_impl              false
% 3.54/1.01  --prep_def_merge_mbd                    true
% 3.54/1.01  --prep_def_merge_tr_red                 false
% 3.54/1.01  --prep_def_merge_tr_cl                  false
% 3.54/1.01  --smt_preprocessing                     true
% 3.54/1.01  --smt_ac_axioms                         fast
% 3.54/1.01  --preprocessed_out                      false
% 3.54/1.01  --preprocessed_stats                    false
% 3.54/1.01  
% 3.54/1.01  ------ Abstraction refinement Options
% 3.54/1.01  
% 3.54/1.01  --abstr_ref                             []
% 3.54/1.01  --abstr_ref_prep                        false
% 3.54/1.01  --abstr_ref_until_sat                   false
% 3.54/1.01  --abstr_ref_sig_restrict                funpre
% 3.54/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/1.01  --abstr_ref_under                       []
% 3.54/1.01  
% 3.54/1.01  ------ SAT Options
% 3.54/1.01  
% 3.54/1.01  --sat_mode                              false
% 3.54/1.01  --sat_fm_restart_options                ""
% 3.54/1.01  --sat_gr_def                            false
% 3.54/1.01  --sat_epr_types                         true
% 3.54/1.01  --sat_non_cyclic_types                  false
% 3.54/1.01  --sat_finite_models                     false
% 3.54/1.01  --sat_fm_lemmas                         false
% 3.54/1.01  --sat_fm_prep                           false
% 3.54/1.01  --sat_fm_uc_incr                        true
% 3.54/1.01  --sat_out_model                         small
% 3.54/1.01  --sat_out_clauses                       false
% 3.54/1.01  
% 3.54/1.01  ------ QBF Options
% 3.54/1.01  
% 3.54/1.01  --qbf_mode                              false
% 3.54/1.01  --qbf_elim_univ                         false
% 3.54/1.01  --qbf_dom_inst                          none
% 3.54/1.01  --qbf_dom_pre_inst                      false
% 3.54/1.01  --qbf_sk_in                             false
% 3.54/1.01  --qbf_pred_elim                         true
% 3.54/1.01  --qbf_split                             512
% 3.54/1.01  
% 3.54/1.01  ------ BMC1 Options
% 3.54/1.01  
% 3.54/1.01  --bmc1_incremental                      false
% 3.54/1.01  --bmc1_axioms                           reachable_all
% 3.54/1.01  --bmc1_min_bound                        0
% 3.54/1.01  --bmc1_max_bound                        -1
% 3.54/1.01  --bmc1_max_bound_default                -1
% 3.54/1.01  --bmc1_symbol_reachability              true
% 3.54/1.01  --bmc1_property_lemmas                  false
% 3.54/1.01  --bmc1_k_induction                      false
% 3.54/1.01  --bmc1_non_equiv_states                 false
% 3.54/1.01  --bmc1_deadlock                         false
% 3.54/1.01  --bmc1_ucm                              false
% 3.54/1.01  --bmc1_add_unsat_core                   none
% 3.54/1.01  --bmc1_unsat_core_children              false
% 3.54/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/1.01  --bmc1_out_stat                         full
% 3.54/1.01  --bmc1_ground_init                      false
% 3.54/1.01  --bmc1_pre_inst_next_state              false
% 3.54/1.01  --bmc1_pre_inst_state                   false
% 3.54/1.01  --bmc1_pre_inst_reach_state             false
% 3.54/1.01  --bmc1_out_unsat_core                   false
% 3.54/1.01  --bmc1_aig_witness_out                  false
% 3.54/1.01  --bmc1_verbose                          false
% 3.54/1.01  --bmc1_dump_clauses_tptp                false
% 3.54/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.54/1.01  --bmc1_dump_file                        -
% 3.54/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.54/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.54/1.01  --bmc1_ucm_extend_mode                  1
% 3.54/1.01  --bmc1_ucm_init_mode                    2
% 3.54/1.01  --bmc1_ucm_cone_mode                    none
% 3.54/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.54/1.01  --bmc1_ucm_relax_model                  4
% 3.54/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.54/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/1.01  --bmc1_ucm_layered_model                none
% 3.54/1.01  --bmc1_ucm_max_lemma_size               10
% 3.54/1.01  
% 3.54/1.01  ------ AIG Options
% 3.54/1.01  
% 3.54/1.01  --aig_mode                              false
% 3.54/1.01  
% 3.54/1.01  ------ Instantiation Options
% 3.54/1.01  
% 3.54/1.01  --instantiation_flag                    true
% 3.54/1.01  --inst_sos_flag                         false
% 3.54/1.01  --inst_sos_phase                        true
% 3.54/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/1.01  --inst_lit_sel_side                     num_symb
% 3.54/1.01  --inst_solver_per_active                1400
% 3.54/1.01  --inst_solver_calls_frac                1.
% 3.54/1.01  --inst_passive_queue_type               priority_queues
% 3.54/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/1.01  --inst_passive_queues_freq              [25;2]
% 3.54/1.01  --inst_dismatching                      true
% 3.54/1.01  --inst_eager_unprocessed_to_passive     true
% 3.54/1.01  --inst_prop_sim_given                   true
% 3.54/1.01  --inst_prop_sim_new                     false
% 3.54/1.01  --inst_subs_new                         false
% 3.54/1.01  --inst_eq_res_simp                      false
% 3.54/1.01  --inst_subs_given                       false
% 3.54/1.01  --inst_orphan_elimination               true
% 3.54/1.01  --inst_learning_loop_flag               true
% 3.54/1.01  --inst_learning_start                   3000
% 3.54/1.01  --inst_learning_factor                  2
% 3.54/1.01  --inst_start_prop_sim_after_learn       3
% 3.54/1.01  --inst_sel_renew                        solver
% 3.54/1.01  --inst_lit_activity_flag                true
% 3.54/1.01  --inst_restr_to_given                   false
% 3.54/1.01  --inst_activity_threshold               500
% 3.54/1.01  --inst_out_proof                        true
% 3.54/1.01  
% 3.54/1.01  ------ Resolution Options
% 3.54/1.01  
% 3.54/1.01  --resolution_flag                       true
% 3.54/1.01  --res_lit_sel                           adaptive
% 3.54/1.01  --res_lit_sel_side                      none
% 3.54/1.01  --res_ordering                          kbo
% 3.54/1.01  --res_to_prop_solver                    active
% 3.54/1.01  --res_prop_simpl_new                    false
% 3.54/1.01  --res_prop_simpl_given                  true
% 3.54/1.01  --res_passive_queue_type                priority_queues
% 3.54/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/1.01  --res_passive_queues_freq               [15;5]
% 3.54/1.01  --res_forward_subs                      full
% 3.54/1.01  --res_backward_subs                     full
% 3.54/1.01  --res_forward_subs_resolution           true
% 3.54/1.01  --res_backward_subs_resolution          true
% 3.54/1.01  --res_orphan_elimination                true
% 3.54/1.01  --res_time_limit                        2.
% 3.54/1.01  --res_out_proof                         true
% 3.54/1.01  
% 3.54/1.01  ------ Superposition Options
% 3.54/1.01  
% 3.54/1.01  --superposition_flag                    true
% 3.54/1.01  --sup_passive_queue_type                priority_queues
% 3.54/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.54/1.01  --demod_completeness_check              fast
% 3.54/1.01  --demod_use_ground                      true
% 3.54/1.01  --sup_to_prop_solver                    passive
% 3.54/1.01  --sup_prop_simpl_new                    true
% 3.54/1.01  --sup_prop_simpl_given                  true
% 3.54/1.01  --sup_fun_splitting                     false
% 3.54/1.01  --sup_smt_interval                      50000
% 3.54/1.01  
% 3.54/1.01  ------ Superposition Simplification Setup
% 3.54/1.01  
% 3.54/1.01  --sup_indices_passive                   []
% 3.54/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_full_bw                           [BwDemod]
% 3.54/1.01  --sup_immed_triv                        [TrivRules]
% 3.54/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_immed_bw_main                     []
% 3.54/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.01  
% 3.54/1.01  ------ Combination Options
% 3.54/1.01  
% 3.54/1.01  --comb_res_mult                         3
% 3.54/1.01  --comb_sup_mult                         2
% 3.54/1.01  --comb_inst_mult                        10
% 3.54/1.01  
% 3.54/1.01  ------ Debug Options
% 3.54/1.01  
% 3.54/1.01  --dbg_backtrace                         false
% 3.54/1.01  --dbg_dump_prop_clauses                 false
% 3.54/1.01  --dbg_dump_prop_clauses_file            -
% 3.54/1.01  --dbg_out_stat                          false
% 3.54/1.01  ------ Parsing...
% 3.54/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  ------ Proving...
% 3.54/1.01  ------ Problem Properties 
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  clauses                                 31
% 3.54/1.01  conjectures                             6
% 3.54/1.01  EPR                                     9
% 3.54/1.01  Horn                                    29
% 3.54/1.01  unary                                   16
% 3.54/1.01  binary                                  3
% 3.54/1.01  lits                                    75
% 3.54/1.01  lits eq                                 13
% 3.54/1.01  fd_pure                                 0
% 3.54/1.01  fd_pseudo                               0
% 3.54/1.01  fd_cond                                 3
% 3.54/1.01  fd_pseudo_cond                          1
% 3.54/1.01  AC symbols                              0
% 3.54/1.01  
% 3.54/1.01  ------ Schedule dynamic 5 is on 
% 3.54/1.01  
% 3.54/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ 
% 3.54/1.01  Current options:
% 3.54/1.01  ------ 
% 3.54/1.01  
% 3.54/1.01  ------ Input Options
% 3.54/1.01  
% 3.54/1.01  --out_options                           all
% 3.54/1.01  --tptp_safe_out                         true
% 3.54/1.01  --problem_path                          ""
% 3.54/1.01  --include_path                          ""
% 3.54/1.01  --clausifier                            res/vclausify_rel
% 3.54/1.01  --clausifier_options                    --mode clausify
% 3.54/1.01  --stdin                                 false
% 3.54/1.01  --stats_out                             all
% 3.54/1.01  
% 3.54/1.01  ------ General Options
% 3.54/1.01  
% 3.54/1.01  --fof                                   false
% 3.54/1.01  --time_out_real                         305.
% 3.54/1.01  --time_out_virtual                      -1.
% 3.54/1.01  --symbol_type_check                     false
% 3.54/1.01  --clausify_out                          false
% 3.54/1.01  --sig_cnt_out                           false
% 3.54/1.01  --trig_cnt_out                          false
% 3.54/1.01  --trig_cnt_out_tolerance                1.
% 3.54/1.01  --trig_cnt_out_sk_spl                   false
% 3.54/1.01  --abstr_cl_out                          false
% 3.54/1.01  
% 3.54/1.01  ------ Global Options
% 3.54/1.01  
% 3.54/1.01  --schedule                              default
% 3.54/1.01  --add_important_lit                     false
% 3.54/1.01  --prop_solver_per_cl                    1000
% 3.54/1.01  --min_unsat_core                        false
% 3.54/1.01  --soft_assumptions                      false
% 3.54/1.01  --soft_lemma_size                       3
% 3.54/1.01  --prop_impl_unit_size                   0
% 3.54/1.01  --prop_impl_unit                        []
% 3.54/1.01  --share_sel_clauses                     true
% 3.54/1.01  --reset_solvers                         false
% 3.54/1.01  --bc_imp_inh                            [conj_cone]
% 3.54/1.01  --conj_cone_tolerance                   3.
% 3.54/1.01  --extra_neg_conj                        none
% 3.54/1.01  --large_theory_mode                     true
% 3.54/1.01  --prolific_symb_bound                   200
% 3.54/1.01  --lt_threshold                          2000
% 3.54/1.01  --clause_weak_htbl                      true
% 3.54/1.01  --gc_record_bc_elim                     false
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing Options
% 3.54/1.01  
% 3.54/1.01  --preprocessing_flag                    true
% 3.54/1.01  --time_out_prep_mult                    0.1
% 3.54/1.01  --splitting_mode                        input
% 3.54/1.01  --splitting_grd                         true
% 3.54/1.01  --splitting_cvd                         false
% 3.54/1.01  --splitting_cvd_svl                     false
% 3.54/1.01  --splitting_nvd                         32
% 3.54/1.01  --sub_typing                            true
% 3.54/1.01  --prep_gs_sim                           true
% 3.54/1.01  --prep_unflatten                        true
% 3.54/1.01  --prep_res_sim                          true
% 3.54/1.01  --prep_upred                            true
% 3.54/1.01  --prep_sem_filter                       exhaustive
% 3.54/1.01  --prep_sem_filter_out                   false
% 3.54/1.01  --pred_elim                             true
% 3.54/1.01  --res_sim_input                         true
% 3.54/1.01  --eq_ax_congr_red                       true
% 3.54/1.01  --pure_diseq_elim                       true
% 3.54/1.01  --brand_transform                       false
% 3.54/1.01  --non_eq_to_eq                          false
% 3.54/1.01  --prep_def_merge                        true
% 3.54/1.01  --prep_def_merge_prop_impl              false
% 3.54/1.01  --prep_def_merge_mbd                    true
% 3.54/1.01  --prep_def_merge_tr_red                 false
% 3.54/1.01  --prep_def_merge_tr_cl                  false
% 3.54/1.01  --smt_preprocessing                     true
% 3.54/1.01  --smt_ac_axioms                         fast
% 3.54/1.01  --preprocessed_out                      false
% 3.54/1.01  --preprocessed_stats                    false
% 3.54/1.01  
% 3.54/1.01  ------ Abstraction refinement Options
% 3.54/1.01  
% 3.54/1.01  --abstr_ref                             []
% 3.54/1.01  --abstr_ref_prep                        false
% 3.54/1.01  --abstr_ref_until_sat                   false
% 3.54/1.01  --abstr_ref_sig_restrict                funpre
% 3.54/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/1.01  --abstr_ref_under                       []
% 3.54/1.01  
% 3.54/1.01  ------ SAT Options
% 3.54/1.01  
% 3.54/1.01  --sat_mode                              false
% 3.54/1.01  --sat_fm_restart_options                ""
% 3.54/1.01  --sat_gr_def                            false
% 3.54/1.01  --sat_epr_types                         true
% 3.54/1.01  --sat_non_cyclic_types                  false
% 3.54/1.01  --sat_finite_models                     false
% 3.54/1.01  --sat_fm_lemmas                         false
% 3.54/1.01  --sat_fm_prep                           false
% 3.54/1.01  --sat_fm_uc_incr                        true
% 3.54/1.01  --sat_out_model                         small
% 3.54/1.01  --sat_out_clauses                       false
% 3.54/1.01  
% 3.54/1.01  ------ QBF Options
% 3.54/1.01  
% 3.54/1.01  --qbf_mode                              false
% 3.54/1.01  --qbf_elim_univ                         false
% 3.54/1.01  --qbf_dom_inst                          none
% 3.54/1.01  --qbf_dom_pre_inst                      false
% 3.54/1.01  --qbf_sk_in                             false
% 3.54/1.01  --qbf_pred_elim                         true
% 3.54/1.01  --qbf_split                             512
% 3.54/1.01  
% 3.54/1.01  ------ BMC1 Options
% 3.54/1.01  
% 3.54/1.01  --bmc1_incremental                      false
% 3.54/1.01  --bmc1_axioms                           reachable_all
% 3.54/1.01  --bmc1_min_bound                        0
% 3.54/1.01  --bmc1_max_bound                        -1
% 3.54/1.01  --bmc1_max_bound_default                -1
% 3.54/1.01  --bmc1_symbol_reachability              true
% 3.54/1.01  --bmc1_property_lemmas                  false
% 3.54/1.01  --bmc1_k_induction                      false
% 3.54/1.01  --bmc1_non_equiv_states                 false
% 3.54/1.01  --bmc1_deadlock                         false
% 3.54/1.01  --bmc1_ucm                              false
% 3.54/1.01  --bmc1_add_unsat_core                   none
% 3.54/1.01  --bmc1_unsat_core_children              false
% 3.54/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/1.01  --bmc1_out_stat                         full
% 3.54/1.01  --bmc1_ground_init                      false
% 3.54/1.01  --bmc1_pre_inst_next_state              false
% 3.54/1.01  --bmc1_pre_inst_state                   false
% 3.54/1.01  --bmc1_pre_inst_reach_state             false
% 3.54/1.01  --bmc1_out_unsat_core                   false
% 3.54/1.01  --bmc1_aig_witness_out                  false
% 3.54/1.01  --bmc1_verbose                          false
% 3.54/1.01  --bmc1_dump_clauses_tptp                false
% 3.54/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.54/1.01  --bmc1_dump_file                        -
% 3.54/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.54/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.54/1.01  --bmc1_ucm_extend_mode                  1
% 3.54/1.01  --bmc1_ucm_init_mode                    2
% 3.54/1.01  --bmc1_ucm_cone_mode                    none
% 3.54/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.54/1.01  --bmc1_ucm_relax_model                  4
% 3.54/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.54/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/1.01  --bmc1_ucm_layered_model                none
% 3.54/1.01  --bmc1_ucm_max_lemma_size               10
% 3.54/1.01  
% 3.54/1.01  ------ AIG Options
% 3.54/1.01  
% 3.54/1.01  --aig_mode                              false
% 3.54/1.01  
% 3.54/1.01  ------ Instantiation Options
% 3.54/1.01  
% 3.54/1.01  --instantiation_flag                    true
% 3.54/1.01  --inst_sos_flag                         false
% 3.54/1.01  --inst_sos_phase                        true
% 3.54/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/1.01  --inst_lit_sel_side                     none
% 3.54/1.01  --inst_solver_per_active                1400
% 3.54/1.01  --inst_solver_calls_frac                1.
% 3.54/1.01  --inst_passive_queue_type               priority_queues
% 3.54/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/1.01  --inst_passive_queues_freq              [25;2]
% 3.54/1.01  --inst_dismatching                      true
% 3.54/1.01  --inst_eager_unprocessed_to_passive     true
% 3.54/1.01  --inst_prop_sim_given                   true
% 3.54/1.01  --inst_prop_sim_new                     false
% 3.54/1.01  --inst_subs_new                         false
% 3.54/1.01  --inst_eq_res_simp                      false
% 3.54/1.01  --inst_subs_given                       false
% 3.54/1.01  --inst_orphan_elimination               true
% 3.54/1.01  --inst_learning_loop_flag               true
% 3.54/1.01  --inst_learning_start                   3000
% 3.54/1.01  --inst_learning_factor                  2
% 3.54/1.01  --inst_start_prop_sim_after_learn       3
% 3.54/1.01  --inst_sel_renew                        solver
% 3.54/1.01  --inst_lit_activity_flag                true
% 3.54/1.01  --inst_restr_to_given                   false
% 3.54/1.01  --inst_activity_threshold               500
% 3.54/1.01  --inst_out_proof                        true
% 3.54/1.01  
% 3.54/1.01  ------ Resolution Options
% 3.54/1.01  
% 3.54/1.01  --resolution_flag                       false
% 3.54/1.01  --res_lit_sel                           adaptive
% 3.54/1.01  --res_lit_sel_side                      none
% 3.54/1.01  --res_ordering                          kbo
% 3.54/1.01  --res_to_prop_solver                    active
% 3.54/1.01  --res_prop_simpl_new                    false
% 3.54/1.01  --res_prop_simpl_given                  true
% 3.54/1.01  --res_passive_queue_type                priority_queues
% 3.54/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/1.01  --res_passive_queues_freq               [15;5]
% 3.54/1.01  --res_forward_subs                      full
% 3.54/1.01  --res_backward_subs                     full
% 3.54/1.01  --res_forward_subs_resolution           true
% 3.54/1.01  --res_backward_subs_resolution          true
% 3.54/1.01  --res_orphan_elimination                true
% 3.54/1.01  --res_time_limit                        2.
% 3.54/1.01  --res_out_proof                         true
% 3.54/1.01  
% 3.54/1.01  ------ Superposition Options
% 3.54/1.01  
% 3.54/1.01  --superposition_flag                    true
% 3.54/1.01  --sup_passive_queue_type                priority_queues
% 3.54/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.54/1.01  --demod_completeness_check              fast
% 3.54/1.01  --demod_use_ground                      true
% 3.54/1.01  --sup_to_prop_solver                    passive
% 3.54/1.01  --sup_prop_simpl_new                    true
% 3.54/1.01  --sup_prop_simpl_given                  true
% 3.54/1.01  --sup_fun_splitting                     false
% 3.54/1.01  --sup_smt_interval                      50000
% 3.54/1.01  
% 3.54/1.01  ------ Superposition Simplification Setup
% 3.54/1.01  
% 3.54/1.01  --sup_indices_passive                   []
% 3.54/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_full_bw                           [BwDemod]
% 3.54/1.01  --sup_immed_triv                        [TrivRules]
% 3.54/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_immed_bw_main                     []
% 3.54/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.01  
% 3.54/1.01  ------ Combination Options
% 3.54/1.01  
% 3.54/1.01  --comb_res_mult                         3
% 3.54/1.01  --comb_sup_mult                         2
% 3.54/1.01  --comb_inst_mult                        10
% 3.54/1.01  
% 3.54/1.01  ------ Debug Options
% 3.54/1.01  
% 3.54/1.01  --dbg_backtrace                         false
% 3.54/1.01  --dbg_dump_prop_clauses                 false
% 3.54/1.01  --dbg_dump_prop_clauses_file            -
% 3.54/1.01  --dbg_out_stat                          false
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  % SZS status Theorem for theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  fof(f22,conjecture,(
% 3.54/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f23,negated_conjecture,(
% 3.54/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.54/1.01    inference(negated_conjecture,[],[f22])).
% 3.54/1.01  
% 3.54/1.01  fof(f44,plain,(
% 3.54/1.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.54/1.01    inference(ennf_transformation,[],[f23])).
% 3.54/1.01  
% 3.54/1.01  fof(f45,plain,(
% 3.54/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.54/1.01    inference(flattening,[],[f44])).
% 3.54/1.01  
% 3.54/1.01  fof(f54,plain,(
% 3.54/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f53,plain,(
% 3.54/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f55,plain,(
% 3.54/1.01    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.54/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f54,f53])).
% 3.54/1.01  
% 3.54/1.01  fof(f90,plain,(
% 3.54/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.54/1.01    inference(cnf_transformation,[],[f55])).
% 3.54/1.01  
% 3.54/1.01  fof(f93,plain,(
% 3.54/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.54/1.01    inference(cnf_transformation,[],[f55])).
% 3.54/1.01  
% 3.54/1.01  fof(f19,axiom,(
% 3.54/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f40,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.54/1.01    inference(ennf_transformation,[],[f19])).
% 3.54/1.01  
% 3.54/1.01  fof(f41,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.54/1.01    inference(flattening,[],[f40])).
% 3.54/1.01  
% 3.54/1.01  fof(f84,plain,(
% 3.54/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f41])).
% 3.54/1.01  
% 3.54/1.01  fof(f91,plain,(
% 3.54/1.01    v1_funct_1(sK3)),
% 3.54/1.01    inference(cnf_transformation,[],[f55])).
% 3.54/1.01  
% 3.54/1.01  fof(f88,plain,(
% 3.54/1.01    v1_funct_1(sK2)),
% 3.54/1.01    inference(cnf_transformation,[],[f55])).
% 3.54/1.01  
% 3.54/1.01  fof(f21,axiom,(
% 3.54/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f42,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.54/1.01    inference(ennf_transformation,[],[f21])).
% 3.54/1.01  
% 3.54/1.01  fof(f43,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.54/1.01    inference(flattening,[],[f42])).
% 3.54/1.01  
% 3.54/1.01  fof(f86,plain,(
% 3.54/1.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f43])).
% 3.54/1.01  
% 3.54/1.01  fof(f89,plain,(
% 3.54/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.54/1.01    inference(cnf_transformation,[],[f55])).
% 3.54/1.01  
% 3.54/1.01  fof(f92,plain,(
% 3.54/1.01    v1_funct_2(sK3,sK1,sK0)),
% 3.54/1.01    inference(cnf_transformation,[],[f55])).
% 3.54/1.01  
% 3.54/1.01  fof(f9,axiom,(
% 3.54/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f31,plain,(
% 3.54/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(ennf_transformation,[],[f9])).
% 3.54/1.01  
% 3.54/1.01  fof(f50,plain,(
% 3.54/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(nnf_transformation,[],[f31])).
% 3.54/1.01  
% 3.54/1.01  fof(f69,plain,(
% 3.54/1.01    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f50])).
% 3.54/1.01  
% 3.54/1.01  fof(f16,axiom,(
% 3.54/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f36,plain,(
% 3.54/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.54/1.01    inference(ennf_transformation,[],[f16])).
% 3.54/1.01  
% 3.54/1.01  fof(f37,plain,(
% 3.54/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(flattening,[],[f36])).
% 3.54/1.01  
% 3.54/1.01  fof(f52,plain,(
% 3.54/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(nnf_transformation,[],[f37])).
% 3.54/1.01  
% 3.54/1.01  fof(f80,plain,(
% 3.54/1.01    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f52])).
% 3.54/1.01  
% 3.54/1.01  fof(f105,plain,(
% 3.54/1.01    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(equality_resolution,[],[f80])).
% 3.54/1.01  
% 3.54/1.01  fof(f95,plain,(
% 3.54/1.01    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.54/1.01    inference(cnf_transformation,[],[f55])).
% 3.54/1.01  
% 3.54/1.01  fof(f2,axiom,(
% 3.54/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f46,plain,(
% 3.54/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/1.01    inference(nnf_transformation,[],[f2])).
% 3.54/1.01  
% 3.54/1.01  fof(f47,plain,(
% 3.54/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/1.01    inference(flattening,[],[f46])).
% 3.54/1.01  
% 3.54/1.01  fof(f58,plain,(
% 3.54/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.54/1.01    inference(cnf_transformation,[],[f47])).
% 3.54/1.01  
% 3.54/1.01  fof(f100,plain,(
% 3.54/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.54/1.01    inference(equality_resolution,[],[f58])).
% 3.54/1.01  
% 3.54/1.01  fof(f8,axiom,(
% 3.54/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f30,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f8])).
% 3.54/1.01  
% 3.54/1.01  fof(f67,plain,(
% 3.54/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f30])).
% 3.54/1.01  
% 3.54/1.01  fof(f10,axiom,(
% 3.54/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f70,plain,(
% 3.54/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.54/1.01    inference(cnf_transformation,[],[f10])).
% 3.54/1.01  
% 3.54/1.01  fof(f14,axiom,(
% 3.54/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f25,plain,(
% 3.54/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.54/1.01    inference(pure_predicate_removal,[],[f14])).
% 3.54/1.01  
% 3.54/1.01  fof(f33,plain,(
% 3.54/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/1.01    inference(ennf_transformation,[],[f25])).
% 3.54/1.01  
% 3.54/1.01  fof(f76,plain,(
% 3.54/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/1.01    inference(cnf_transformation,[],[f33])).
% 3.54/1.01  
% 3.54/1.01  fof(f68,plain,(
% 3.54/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f50])).
% 3.54/1.01  
% 3.54/1.01  fof(f59,plain,(
% 3.54/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f47])).
% 3.54/1.01  
% 3.54/1.01  fof(f15,axiom,(
% 3.54/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f34,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.54/1.01    inference(ennf_transformation,[],[f15])).
% 3.54/1.01  
% 3.54/1.01  fof(f35,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/1.01    inference(flattening,[],[f34])).
% 3.54/1.01  
% 3.54/1.01  fof(f51,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/1.01    inference(nnf_transformation,[],[f35])).
% 3.54/1.01  
% 3.54/1.01  fof(f77,plain,(
% 3.54/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/1.01    inference(cnf_transformation,[],[f51])).
% 3.54/1.01  
% 3.54/1.01  fof(f94,plain,(
% 3.54/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.54/1.01    inference(cnf_transformation,[],[f55])).
% 3.54/1.01  
% 3.54/1.01  fof(f18,axiom,(
% 3.54/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f24,plain,(
% 3.54/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.54/1.01    inference(pure_predicate_removal,[],[f18])).
% 3.54/1.01  
% 3.54/1.01  fof(f83,plain,(
% 3.54/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.54/1.01    inference(cnf_transformation,[],[f24])).
% 3.54/1.01  
% 3.54/1.01  fof(f17,axiom,(
% 3.54/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f38,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.54/1.01    inference(ennf_transformation,[],[f17])).
% 3.54/1.01  
% 3.54/1.01  fof(f39,plain,(
% 3.54/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.54/1.01    inference(flattening,[],[f38])).
% 3.54/1.01  
% 3.54/1.01  fof(f82,plain,(
% 3.54/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f39])).
% 3.54/1.01  
% 3.54/1.01  fof(f11,axiom,(
% 3.54/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f32,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f11])).
% 3.54/1.01  
% 3.54/1.01  fof(f71,plain,(
% 3.54/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f32])).
% 3.54/1.01  
% 3.54/1.01  fof(f12,axiom,(
% 3.54/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f73,plain,(
% 3.54/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.54/1.01    inference(cnf_transformation,[],[f12])).
% 3.54/1.01  
% 3.54/1.01  fof(f20,axiom,(
% 3.54/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f85,plain,(
% 3.54/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f20])).
% 3.54/1.01  
% 3.54/1.01  fof(f96,plain,(
% 3.54/1.01    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.54/1.01    inference(definition_unfolding,[],[f73,f85])).
% 3.54/1.01  
% 3.54/1.01  fof(f13,axiom,(
% 3.54/1.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f75,plain,(
% 3.54/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.54/1.01    inference(cnf_transformation,[],[f13])).
% 3.54/1.01  
% 3.54/1.01  fof(f98,plain,(
% 3.54/1.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.54/1.01    inference(definition_unfolding,[],[f75,f85])).
% 3.54/1.01  
% 3.54/1.01  fof(f6,axiom,(
% 3.54/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f48,plain,(
% 3.54/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.54/1.01    inference(nnf_transformation,[],[f6])).
% 3.54/1.01  
% 3.54/1.01  fof(f49,plain,(
% 3.54/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.54/1.01    inference(flattening,[],[f48])).
% 3.54/1.01  
% 3.54/1.01  fof(f64,plain,(
% 3.54/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.54/1.01    inference(cnf_transformation,[],[f49])).
% 3.54/1.01  
% 3.54/1.01  fof(f103,plain,(
% 3.54/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.54/1.01    inference(equality_resolution,[],[f64])).
% 3.54/1.01  
% 3.54/1.01  fof(f65,plain,(
% 3.54/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.54/1.01    inference(cnf_transformation,[],[f49])).
% 3.54/1.01  
% 3.54/1.01  fof(f102,plain,(
% 3.54/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.54/1.01    inference(equality_resolution,[],[f65])).
% 3.54/1.01  
% 3.54/1.01  fof(f7,axiom,(
% 3.54/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f29,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f7])).
% 3.54/1.01  
% 3.54/1.01  fof(f66,plain,(
% 3.54/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f29])).
% 3.54/1.01  
% 3.54/1.01  fof(f1,axiom,(
% 3.54/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f26,plain,(
% 3.54/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f1])).
% 3.54/1.01  
% 3.54/1.01  fof(f56,plain,(
% 3.54/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f26])).
% 3.54/1.01  
% 3.54/1.01  fof(f3,axiom,(
% 3.54/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f60,plain,(
% 3.54/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f3])).
% 3.54/1.01  
% 3.54/1.01  fof(f4,axiom,(
% 3.54/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f61,plain,(
% 3.54/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f4])).
% 3.54/1.01  
% 3.54/1.01  fof(f5,axiom,(
% 3.54/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.54/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f27,plain,(
% 3.54/1.01    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.54/1.01    inference(ennf_transformation,[],[f5])).
% 3.54/1.01  
% 3.54/1.01  fof(f28,plain,(
% 3.54/1.01    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.54/1.01    inference(flattening,[],[f27])).
% 3.54/1.01  
% 3.54/1.01  fof(f62,plain,(
% 3.54/1.01    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f28])).
% 3.54/1.01  
% 3.54/1.01  cnf(c_36,negated_conjecture,
% 3.54/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.54/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1148,plain,
% 3.54/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_33,negated_conjecture,
% 3.54/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.54/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1151,plain,
% 3.54/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_28,plain,
% 3.54/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.54/1.01      | ~ v1_funct_1(X0)
% 3.54/1.01      | ~ v1_funct_1(X3)
% 3.54/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1154,plain,
% 3.54/1.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.54/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.54/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.54/1.01      | v1_funct_1(X5) != iProver_top
% 3.54/1.01      | v1_funct_1(X4) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_3968,plain,
% 3.54/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.54/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.54/1.01      | v1_funct_1(X2) != iProver_top
% 3.54/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_1151,c_1154]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_35,negated_conjecture,
% 3.54/1.01      ( v1_funct_1(sK3) ),
% 3.54/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_42,plain,
% 3.54/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4287,plain,
% 3.54/1.01      ( v1_funct_1(X2) != iProver_top
% 3.54/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.54/1.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_3968,c_42]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4288,plain,
% 3.54/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.54/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.54/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.54/1.01      inference(renaming,[status(thm)],[c_4287]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4298,plain,
% 3.54/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.54/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_1148,c_4288]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_38,negated_conjecture,
% 3.54/1.01      ( v1_funct_1(sK2) ),
% 3.54/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1481,plain,
% 3.54/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.54/1.01      | ~ v1_funct_1(X0)
% 3.54/1.01      | ~ v1_funct_1(sK3)
% 3.54/1.01      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1762,plain,
% 3.54/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.54/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.54/1.01      | ~ v1_funct_1(sK2)
% 3.54/1.01      | ~ v1_funct_1(sK3)
% 3.54/1.01      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1481]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2256,plain,
% 3.54/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.54/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.54/1.01      | ~ v1_funct_1(sK2)
% 3.54/1.01      | ~ v1_funct_1(sK3)
% 3.54/1.01      | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1762]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_3386,plain,
% 3.54/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.54/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.54/1.01      | ~ v1_funct_1(sK2)
% 3.54/1.01      | ~ v1_funct_1(sK3)
% 3.54/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_2256]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4409,plain,
% 3.54/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_4298,c_38,c_36,c_35,c_33,c_3386]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_30,plain,
% 3.54/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.54/1.01      | ~ v1_funct_2(X3,X4,X1)
% 3.54/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.54/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/1.01      | ~ v1_funct_1(X0)
% 3.54/1.01      | ~ v1_funct_1(X3)
% 3.54/1.01      | v2_funct_1(X3)
% 3.54/1.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.54/1.01      | k1_xboole_0 = X2 ),
% 3.54/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1152,plain,
% 3.54/1.01      ( k1_xboole_0 = X0
% 3.54/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.54/1.01      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.54/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.54/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.54/1.01      | v1_funct_1(X1) != iProver_top
% 3.54/1.01      | v1_funct_1(X3) != iProver_top
% 3.54/1.01      | v2_funct_1(X3) = iProver_top
% 3.54/1.01      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4415,plain,
% 3.54/1.01      ( sK0 = k1_xboole_0
% 3.54/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.54/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.54/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.54/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/1.01      | v1_funct_1(sK2) != iProver_top
% 3.54/1.01      | v1_funct_1(sK3) != iProver_top
% 3.54/1.01      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.54/1.01      | v2_funct_1(sK2) = iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_4409,c_1152]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_39,plain,
% 3.54/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_37,negated_conjecture,
% 3.54/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.54/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_40,plain,
% 3.54/1.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_41,plain,
% 3.54/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_34,negated_conjecture,
% 3.54/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_43,plain,
% 3.54/1.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_44,plain,
% 3.54/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_12,plain,
% 3.54/1.01      ( v5_relat_1(X0,X1)
% 3.54/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.54/1.01      | ~ v1_relat_1(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_23,plain,
% 3.54/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.54/1.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.54/1.01      | ~ v1_relat_1(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_31,negated_conjecture,
% 3.54/1.01      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.54/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_413,plain,
% 3.54/1.01      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.54/1.01      | ~ v2_funct_1(sK2)
% 3.54/1.01      | ~ v1_relat_1(X0)
% 3.54/1.01      | k2_relat_1(X0) != sK0
% 3.54/1.01      | sK3 != X0 ),
% 3.54/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_414,plain,
% 3.54/1.01      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.54/1.01      | ~ v2_funct_1(sK2)
% 3.54/1.01      | ~ v1_relat_1(sK3)
% 3.54/1.01      | k2_relat_1(sK3) != sK0 ),
% 3.54/1.01      inference(unflattening,[status(thm)],[c_413]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_467,plain,
% 3.54/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.54/1.01      | ~ v2_funct_1(sK2)
% 3.54/1.01      | ~ v1_relat_1(X0)
% 3.54/1.01      | ~ v1_relat_1(sK3)
% 3.54/1.01      | k2_relat_1(sK3) != X1
% 3.54/1.01      | k2_relat_1(sK3) != sK0
% 3.54/1.01      | sK3 != X0 ),
% 3.54/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_414]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_468,plain,
% 3.54/1.01      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.54/1.01      | ~ v2_funct_1(sK2)
% 3.54/1.01      | ~ v1_relat_1(sK3)
% 3.54/1.01      | k2_relat_1(sK3) != sK0 ),
% 3.54/1.01      inference(unflattening,[status(thm)],[c_467]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2,plain,
% 3.54/1.01      ( r1_tarski(X0,X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_478,plain,
% 3.54/1.01      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.54/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_468,c_2]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_479,plain,
% 3.54/1.01      ( k2_relat_1(sK3) != sK0
% 3.54/1.01      | v2_funct_1(sK2) != iProver_top
% 3.54/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11,plain,
% 3.54/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/1.01      | ~ v1_relat_1(X1)
% 3.54/1.01      | v1_relat_1(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1162,plain,
% 3.54/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2788,plain,
% 3.54/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.54/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_1151,c_1162]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_14,plain,
% 3.54/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1161,plain,
% 3.54/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2894,plain,
% 3.54/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 3.54/1.01      inference(forward_subsumption_resolution,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_2788,c_1161]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2789,plain,
% 3.54/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.54/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_1148,c_1162]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2949,plain,
% 3.54/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.54/1.01      inference(forward_subsumption_resolution,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_2789,c_1161]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_20,plain,
% 3.54/1.01      ( v5_relat_1(X0,X1)
% 3.54/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.54/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_13,plain,
% 3.54/1.01      ( ~ v5_relat_1(X0,X1)
% 3.54/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 3.54/1.01      | ~ v1_relat_1(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_434,plain,
% 3.54/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.54/1.01      | ~ v1_relat_1(X0) ),
% 3.54/1.01      inference(resolution,[status(thm)],[c_20,c_13]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1143,plain,
% 3.54/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.54/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2594,plain,
% 3.54/1.01      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.54/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_1151,c_1143]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1,plain,
% 3.54/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.54/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1166,plain,
% 3.54/1.01      ( X0 = X1
% 3.54/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.54/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2806,plain,
% 3.54/1.01      ( k2_relat_1(sK3) = sK0
% 3.54/1.01      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.54/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_2594,c_1166]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2952,plain,
% 3.54/1.01      ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.54/1.01      | k2_relat_1(sK3) = sK0 ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_2806,c_2894]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2953,plain,
% 3.54/1.01      ( k2_relat_1(sK3) = sK0
% 3.54/1.01      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
% 3.54/1.01      inference(renaming,[status(thm)],[c_2952]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_22,plain,
% 3.54/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.54/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.54/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.54/1.01      | X3 = X2 ),
% 3.54/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_32,negated_conjecture,
% 3.54/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_395,plain,
% 3.54/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/1.01      | X3 = X0
% 3.54/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.54/1.01      | k6_partfun1(sK0) != X3
% 3.54/1.01      | sK0 != X2
% 3.54/1.01      | sK0 != X1 ),
% 3.54/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_396,plain,
% 3.54/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.54/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.54/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.54/1.01      inference(unflattening,[status(thm)],[c_395]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_27,plain,
% 3.54/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.54/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_404,plain,
% 3.54/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.54/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.54/1.01      inference(forward_subsumption_resolution,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_396,c_27]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1144,plain,
% 3.54/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.54/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4412,plain,
% 3.54/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.54/1.01      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.54/1.01      inference(demodulation,[status(thm)],[c_4409,c_1144]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_25,plain,
% 3.54/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.54/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.54/1.01      | ~ v1_funct_1(X0)
% 3.54/1.01      | ~ v1_funct_1(X3) ),
% 3.54/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1157,plain,
% 3.54/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.54/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.54/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.54/1.01      | v1_funct_1(X0) != iProver_top
% 3.54/1.01      | v1_funct_1(X3) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4928,plain,
% 3.54/1.01      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.54/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.54/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/1.01      | v1_funct_1(sK2) != iProver_top
% 3.54/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_4409,c_1157]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_5285,plain,
% 3.54/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_4412,c_39,c_41,c_42,c_44,c_4928]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_15,plain,
% 3.54/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.54/1.01      | ~ v1_relat_1(X0)
% 3.54/1.01      | ~ v1_relat_1(X1) ),
% 3.54/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1160,plain,
% 3.54/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_5289,plain,
% 3.54/1.01      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.54/1.01      | v1_relat_1(sK2) != iProver_top
% 3.54/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_5285,c_1160]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_16,plain,
% 3.54/1.01      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.54/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_5290,plain,
% 3.54/1.01      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.54/1.01      | v1_relat_1(sK2) != iProver_top
% 3.54/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.54/1.01      inference(demodulation,[status(thm)],[c_5289,c_16]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_15482,plain,
% 3.54/1.01      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.54/1.01      | sK0 = k1_xboole_0 ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_4415,c_39,c_40,c_41,c_42,c_43,c_44,c_479,c_2806,
% 3.54/1.01                 c_2894,c_2949,c_5290]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_15483,plain,
% 3.54/1.01      ( sK0 = k1_xboole_0
% 3.54/1.01      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 3.54/1.01      inference(renaming,[status(thm)],[c_15482]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_15486,plain,
% 3.54/1.01      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.54/1.01      inference(light_normalisation,[status(thm)],[c_15483,c_5285]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_18,plain,
% 3.54/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1159,plain,
% 3.54/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_15489,plain,
% 3.54/1.01      ( sK0 = k1_xboole_0 ),
% 3.54/1.01      inference(forward_subsumption_resolution,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_15486,c_1159]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_15576,plain,
% 3.54/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 3.54/1.01      inference(demodulation,[status(thm)],[c_15489,c_1148]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_8,plain,
% 3.54/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.54/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_15584,plain,
% 3.54/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.54/1.01      inference(demodulation,[status(thm)],[c_15576,c_8]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_676,plain,
% 3.54/1.01      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.54/1.01      theory(equality) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_7107,plain,
% 3.54/1.01      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_676]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_7109,plain,
% 3.54/1.01      ( v2_funct_1(sK2)
% 3.54/1.01      | ~ v2_funct_1(k1_xboole_0)
% 3.54/1.01      | sK2 != k1_xboole_0 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_7107]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_667,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2664,plain,
% 3.54/1.01      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_667]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_5222,plain,
% 3.54/1.01      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_2664]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_5223,plain,
% 3.54/1.01      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_5222]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_7,plain,
% 3.54/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.54/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1155,plain,
% 3.54/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2368,plain,
% 3.54/1.01      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_7,c_1155]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10,plain,
% 3.54/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/1.01      | ~ v1_xboole_0(X1)
% 3.54/1.01      | v1_xboole_0(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1163,plain,
% 3.54/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.54/1.01      | v1_xboole_0(X1) != iProver_top
% 3.54/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_3354,plain,
% 3.54/1.01      ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
% 3.54/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_2368,c_1163]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2895,plain,
% 3.54/1.01      ( v1_relat_1(sK3) ),
% 3.54/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2894]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1960,plain,
% 3.54/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.54/1.01      | ~ v1_xboole_0(X0)
% 3.54/1.01      | v1_xboole_0(sK2) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1961,plain,
% 3.54/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.54/1.01      | v1_xboole_0(X0) != iProver_top
% 3.54/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_1960]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1963,plain,
% 3.54/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.54/1.01      | v1_xboole_0(sK2) = iProver_top
% 3.54/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1961]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_0,plain,
% 3.54/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.54/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1693,plain,
% 3.54/1.01      ( ~ v1_xboole_0(k6_partfun1(X0)) | k1_xboole_0 = k6_partfun1(X0) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1697,plain,
% 3.54/1.01      ( k1_xboole_0 = k6_partfun1(X0)
% 3.54/1.01      | v1_xboole_0(k6_partfun1(X0)) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1699,plain,
% 3.54/1.01      ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.54/1.01      | v1_xboole_0(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1697]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_666,plain,( X0 = X0 ),theory(equality) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1606,plain,
% 3.54/1.01      ( sK2 = sK2 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_666]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1543,plain,
% 3.54/1.01      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1547,plain,
% 3.54/1.01      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_1543]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1397,plain,
% 3.54/1.01      ( v2_funct_1(X0)
% 3.54/1.01      | ~ v2_funct_1(k6_partfun1(X1))
% 3.54/1.01      | X0 != k6_partfun1(X1) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_676]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1399,plain,
% 3.54/1.01      ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
% 3.54/1.01      | v2_funct_1(k1_xboole_0)
% 3.54/1.01      | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1397]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4,plain,
% 3.54/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_110,plain,
% 3.54/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_112,plain,
% 3.54/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_110]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_5,plain,
% 3.54/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_107,plain,
% 3.54/1.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_109,plain,
% 3.54/1.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_107]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_6,plain,
% 3.54/1.01      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_104,plain,
% 3.54/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 3.54/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.54/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_106,plain,
% 3.54/1.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.54/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.54/1.01      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_104]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_84,plain,
% 3.54/1.01      ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(contradiction,plain,
% 3.54/1.01      ( $false ),
% 3.54/1.01      inference(minisat,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_15584,c_7109,c_5290,c_5223,c_3354,c_2953,c_2949,
% 3.54/1.01                 c_2895,c_2894,c_1963,c_1699,c_1606,c_1547,c_1399,c_478,
% 3.54/1.01                 c_112,c_109,c_106,c_84]) ).
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  ------                               Statistics
% 3.54/1.01  
% 3.54/1.01  ------ General
% 3.54/1.01  
% 3.54/1.01  abstr_ref_over_cycles:                  0
% 3.54/1.01  abstr_ref_under_cycles:                 0
% 3.54/1.01  gc_basic_clause_elim:                   0
% 3.54/1.01  forced_gc_time:                         0
% 3.54/1.01  parsing_time:                           0.009
% 3.54/1.01  unif_index_cands_time:                  0.
% 3.54/1.01  unif_index_add_time:                    0.
% 3.54/1.01  orderings_time:                         0.
% 3.54/1.01  out_proof_time:                         0.011
% 3.54/1.01  total_time:                             0.483
% 3.54/1.01  num_of_symbols:                         54
% 3.54/1.01  num_of_terms:                           17724
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing
% 3.54/1.01  
% 3.54/1.01  num_of_splits:                          0
% 3.54/1.01  num_of_split_atoms:                     0
% 3.54/1.01  num_of_reused_defs:                     0
% 3.54/1.01  num_eq_ax_congr_red:                    11
% 3.54/1.01  num_of_sem_filtered_clauses:            1
% 3.54/1.01  num_of_subtypes:                        0
% 3.54/1.01  monotx_restored_types:                  0
% 3.54/1.01  sat_num_of_epr_types:                   0
% 3.54/1.01  sat_num_of_non_cyclic_types:            0
% 3.54/1.01  sat_guarded_non_collapsed_types:        0
% 3.54/1.01  num_pure_diseq_elim:                    0
% 3.54/1.01  simp_replaced_by:                       0
% 3.54/1.01  res_preprocessed:                       160
% 3.54/1.01  prep_upred:                             0
% 3.54/1.01  prep_unflattend:                        17
% 3.54/1.01  smt_new_axioms:                         0
% 3.54/1.01  pred_elim_cands:                        7
% 3.54/1.01  pred_elim:                              4
% 3.54/1.01  pred_elim_cl:                           7
% 3.54/1.01  pred_elim_cycles:                       6
% 3.54/1.01  merged_defs:                            0
% 3.54/1.01  merged_defs_ncl:                        0
% 3.54/1.01  bin_hyper_res:                          0
% 3.54/1.01  prep_cycles:                            4
% 3.54/1.01  pred_elim_time:                         0.004
% 3.54/1.01  splitting_time:                         0.
% 3.54/1.01  sem_filter_time:                        0.
% 3.54/1.01  monotx_time:                            0.
% 3.54/1.01  subtype_inf_time:                       0.
% 3.54/1.01  
% 3.54/1.01  ------ Problem properties
% 3.54/1.01  
% 3.54/1.01  clauses:                                31
% 3.54/1.01  conjectures:                            6
% 3.54/1.01  epr:                                    9
% 3.54/1.01  horn:                                   29
% 3.54/1.01  ground:                                 8
% 3.54/1.01  unary:                                  16
% 3.54/1.01  binary:                                 3
% 3.54/1.01  lits:                                   75
% 3.54/1.01  lits_eq:                                13
% 3.54/1.01  fd_pure:                                0
% 3.54/1.01  fd_pseudo:                              0
% 3.54/1.01  fd_cond:                                3
% 3.54/1.01  fd_pseudo_cond:                         1
% 3.54/1.01  ac_symbols:                             0
% 3.54/1.01  
% 3.54/1.01  ------ Propositional Solver
% 3.54/1.01  
% 3.54/1.01  prop_solver_calls:                      29
% 3.54/1.01  prop_fast_solver_calls:                 1454
% 3.54/1.01  smt_solver_calls:                       0
% 3.54/1.01  smt_fast_solver_calls:                  0
% 3.54/1.01  prop_num_of_clauses:                    6582
% 3.54/1.01  prop_preprocess_simplified:             15276
% 3.54/1.01  prop_fo_subsumed:                       68
% 3.54/1.01  prop_solver_time:                       0.
% 3.54/1.01  smt_solver_time:                        0.
% 3.54/1.01  smt_fast_solver_time:                   0.
% 3.54/1.01  prop_fast_solver_time:                  0.
% 3.54/1.01  prop_unsat_core_time:                   0.
% 3.54/1.01  
% 3.54/1.01  ------ QBF
% 3.54/1.01  
% 3.54/1.01  qbf_q_res:                              0
% 3.54/1.01  qbf_num_tautologies:                    0
% 3.54/1.01  qbf_prep_cycles:                        0
% 3.54/1.01  
% 3.54/1.01  ------ BMC1
% 3.54/1.01  
% 3.54/1.01  bmc1_current_bound:                     -1
% 3.54/1.01  bmc1_last_solved_bound:                 -1
% 3.54/1.01  bmc1_unsat_core_size:                   -1
% 3.54/1.01  bmc1_unsat_core_parents_size:           -1
% 3.54/1.01  bmc1_merge_next_fun:                    0
% 3.54/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.54/1.01  
% 3.54/1.01  ------ Instantiation
% 3.54/1.01  
% 3.54/1.01  inst_num_of_clauses:                    1757
% 3.54/1.01  inst_num_in_passive:                    848
% 3.54/1.01  inst_num_in_active:                     746
% 3.54/1.01  inst_num_in_unprocessed:                167
% 3.54/1.01  inst_num_of_loops:                      810
% 3.54/1.01  inst_num_of_learning_restarts:          0
% 3.54/1.01  inst_num_moves_active_passive:          63
% 3.54/1.01  inst_lit_activity:                      0
% 3.54/1.01  inst_lit_activity_moves:                1
% 3.54/1.01  inst_num_tautologies:                   0
% 3.54/1.01  inst_num_prop_implied:                  0
% 3.54/1.01  inst_num_existing_simplified:           0
% 3.54/1.01  inst_num_eq_res_simplified:             0
% 3.54/1.01  inst_num_child_elim:                    0
% 3.54/1.01  inst_num_of_dismatching_blockings:      112
% 3.54/1.01  inst_num_of_non_proper_insts:           1250
% 3.54/1.01  inst_num_of_duplicates:                 0
% 3.54/1.01  inst_inst_num_from_inst_to_res:         0
% 3.54/1.01  inst_dismatching_checking_time:         0.
% 3.54/1.01  
% 3.54/1.01  ------ Resolution
% 3.54/1.01  
% 3.54/1.01  res_num_of_clauses:                     0
% 3.54/1.01  res_num_in_passive:                     0
% 3.54/1.01  res_num_in_active:                      0
% 3.54/1.01  res_num_of_loops:                       164
% 3.54/1.01  res_forward_subset_subsumed:            56
% 3.54/1.01  res_backward_subset_subsumed:           8
% 3.54/1.01  res_forward_subsumed:                   0
% 3.54/1.01  res_backward_subsumed:                  1
% 3.54/1.01  res_forward_subsumption_resolution:     2
% 3.54/1.01  res_backward_subsumption_resolution:    0
% 3.54/1.01  res_clause_to_clause_subsumption:       3743
% 3.54/1.01  res_orphan_elimination:                 0
% 3.54/1.01  res_tautology_del:                      19
% 3.54/1.01  res_num_eq_res_simplified:              0
% 3.54/1.01  res_num_sel_changes:                    0
% 3.54/1.01  res_moves_from_active_to_pass:          0
% 3.54/1.01  
% 3.54/1.01  ------ Superposition
% 3.54/1.01  
% 3.54/1.01  sup_time_total:                         0.
% 3.54/1.01  sup_time_generating:                    0.
% 3.54/1.01  sup_time_sim_full:                      0.
% 3.54/1.01  sup_time_sim_immed:                     0.
% 3.54/1.01  
% 3.54/1.01  sup_num_of_clauses:                     347
% 3.54/1.01  sup_num_in_active:                      61
% 3.54/1.01  sup_num_in_passive:                     286
% 3.54/1.01  sup_num_of_loops:                       161
% 3.54/1.01  sup_fw_superposition:                   262
% 3.54/1.01  sup_bw_superposition:                   124
% 3.54/1.01  sup_immediate_simplified:               81
% 3.54/1.01  sup_given_eliminated:                   1
% 3.54/1.01  comparisons_done:                       0
% 3.54/1.01  comparisons_avoided:                    0
% 3.54/1.01  
% 3.54/1.01  ------ Simplifications
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  sim_fw_subset_subsumed:                 5
% 3.54/1.01  sim_bw_subset_subsumed:                 14
% 3.54/1.01  sim_fw_subsumed:                        10
% 3.54/1.01  sim_bw_subsumed:                        2
% 3.54/1.01  sim_fw_subsumption_res:                 20
% 3.54/1.01  sim_bw_subsumption_res:                 0
% 3.54/1.01  sim_tautology_del:                      2
% 3.54/1.01  sim_eq_tautology_del:                   9
% 3.54/1.01  sim_eq_res_simp:                        0
% 3.54/1.01  sim_fw_demodulated:                     21
% 3.54/1.01  sim_bw_demodulated:                     94
% 3.54/1.01  sim_light_normalised:                   41
% 3.54/1.01  sim_joinable_taut:                      0
% 3.54/1.01  sim_joinable_simp:                      0
% 3.54/1.01  sim_ac_normalised:                      0
% 3.54/1.01  sim_smt_subsumption:                    0
% 3.54/1.01  
%------------------------------------------------------------------------------
