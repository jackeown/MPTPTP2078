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
% DateTime   : Thu Dec  3 12:02:11 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  213 (1277 expanded)
%              Number of clauses        :  120 ( 382 expanded)
%              Number of leaves         :   27 ( 319 expanded)
%              Depth                    :   23
%              Number of atoms          :  646 (7927 expanded)
%              Number of equality atoms :  243 ( 661 expanded)
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

fof(f43,plain,(
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
    inference(flattening,[],[f43])).

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f54,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f53,f52])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f41,plain,(
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
    inference(flattening,[],[f41])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f94,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f78,f84])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

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
    inference(cnf_transformation,[],[f90])).

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
    inference(cnf_transformation,[],[f87])).

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
    inference(cnf_transformation,[],[f85])).

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
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f91])).

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
    inference(cnf_transformation,[],[f68])).

cnf(c_24,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_31,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_413,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

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
    inference(cnf_transformation,[],[f66])).

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
    inference(cnf_transformation,[],[f69])).

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
    inference(cnf_transformation,[],[f75])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

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
    inference(cnf_transformation,[],[f58])).

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
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

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

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_404,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_396,c_23])).

cnf(c_1144,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_4412,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4409,c_1144])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1156,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4928,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4409,c_1156])).

cnf(c_5285,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4412,c_39,c_41,c_42,c_44,c_4928])).

cnf(c_15,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f95])).

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
    inference(cnf_transformation,[],[f97])).

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

cnf(c_1157,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2368,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1157])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

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
    inference(cnf_transformation,[],[f55])).

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
    inference(cnf_transformation,[],[f59])).

cnf(c_110,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

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
    inference(cnf_transformation,[],[f61])).

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
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 4.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/0.99  
% 4.02/0.99  ------  iProver source info
% 4.02/0.99  
% 4.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/0.99  git: non_committed_changes: false
% 4.02/0.99  git: last_make_outside_of_git: false
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    --mode clausify
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         false
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     num_symb
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       true
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     false
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   []
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.99  --sup_full_bw                           [BwDemod]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  ------ Parsing...
% 4.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.99  ------ Proving...
% 4.02/0.99  ------ Problem Properties 
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  clauses                                 31
% 4.02/0.99  conjectures                             6
% 4.02/0.99  EPR                                     9
% 4.02/0.99  Horn                                    29
% 4.02/0.99  unary                                   16
% 4.02/0.99  binary                                  3
% 4.02/0.99  lits                                    75
% 4.02/0.99  lits eq                                 13
% 4.02/0.99  fd_pure                                 0
% 4.02/0.99  fd_pseudo                               0
% 4.02/0.99  fd_cond                                 3
% 4.02/0.99  fd_pseudo_cond                          1
% 4.02/0.99  AC symbols                              0
% 4.02/0.99  
% 4.02/0.99  ------ Schedule dynamic 5 is on 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  Current options:
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    --mode clausify
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         false
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     none
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       false
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     false
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   []
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.99  --sup_full_bw                           [BwDemod]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ Proving...
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS status Theorem for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  fof(f22,conjecture,(
% 4.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f23,negated_conjecture,(
% 4.02/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 4.02/0.99    inference(negated_conjecture,[],[f22])).
% 4.02/0.99  
% 4.02/0.99  fof(f43,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.02/0.99    inference(ennf_transformation,[],[f23])).
% 4.02/0.99  
% 4.02/0.99  fof(f44,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.02/0.99    inference(flattening,[],[f43])).
% 4.02/0.99  
% 4.02/0.99  fof(f53,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f52,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f54,plain,(
% 4.02/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f53,f52])).
% 4.02/0.99  
% 4.02/0.99  fof(f89,plain,(
% 4.02/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f92,plain,(
% 4.02/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f19,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f39,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.02/0.99    inference(ennf_transformation,[],[f19])).
% 4.02/0.99  
% 4.02/0.99  fof(f40,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.02/0.99    inference(flattening,[],[f39])).
% 4.02/0.99  
% 4.02/0.99  fof(f83,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f90,plain,(
% 4.02/0.99    v1_funct_1(sK3)),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f87,plain,(
% 4.02/0.99    v1_funct_1(sK2)),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f21,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f41,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.02/0.99    inference(ennf_transformation,[],[f21])).
% 4.02/0.99  
% 4.02/0.99  fof(f42,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.02/0.99    inference(flattening,[],[f41])).
% 4.02/0.99  
% 4.02/0.99  fof(f85,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f42])).
% 4.02/0.99  
% 4.02/0.99  fof(f88,plain,(
% 4.02/0.99    v1_funct_2(sK2,sK0,sK1)),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f91,plain,(
% 4.02/0.99    v1_funct_2(sK3,sK1,sK0)),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f9,axiom,(
% 4.02/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f30,plain,(
% 4.02/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(ennf_transformation,[],[f9])).
% 4.02/0.99  
% 4.02/0.99  fof(f49,plain,(
% 4.02/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f30])).
% 4.02/0.99  
% 4.02/0.99  fof(f68,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f49])).
% 4.02/0.99  
% 4.02/0.99  fof(f17,axiom,(
% 4.02/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f35,plain,(
% 4.02/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.02/0.99    inference(ennf_transformation,[],[f17])).
% 4.02/0.99  
% 4.02/0.99  fof(f36,plain,(
% 4.02/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(flattening,[],[f35])).
% 4.02/0.99  
% 4.02/0.99  fof(f51,plain,(
% 4.02/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f36])).
% 4.02/0.99  
% 4.02/0.99  fof(f80,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f51])).
% 4.02/0.99  
% 4.02/0.99  fof(f105,plain,(
% 4.02/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(equality_resolution,[],[f80])).
% 4.02/0.99  
% 4.02/0.99  fof(f94,plain,(
% 4.02/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f2,axiom,(
% 4.02/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f45,plain,(
% 4.02/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f2])).
% 4.02/0.99  
% 4.02/0.99  fof(f46,plain,(
% 4.02/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.02/0.99    inference(flattening,[],[f45])).
% 4.02/0.99  
% 4.02/0.99  fof(f57,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.02/0.99    inference(cnf_transformation,[],[f46])).
% 4.02/0.99  
% 4.02/0.99  fof(f100,plain,(
% 4.02/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.02/0.99    inference(equality_resolution,[],[f57])).
% 4.02/0.99  
% 4.02/0.99  fof(f8,axiom,(
% 4.02/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f29,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f8])).
% 4.02/0.99  
% 4.02/0.99  fof(f66,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f29])).
% 4.02/0.99  
% 4.02/0.99  fof(f10,axiom,(
% 4.02/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f69,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f10])).
% 4.02/0.99  
% 4.02/0.99  fof(f14,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f24,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.02/0.99    inference(pure_predicate_removal,[],[f14])).
% 4.02/0.99  
% 4.02/0.99  fof(f32,plain,(
% 4.02/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/0.99    inference(ennf_transformation,[],[f24])).
% 4.02/0.99  
% 4.02/0.99  fof(f75,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f32])).
% 4.02/0.99  
% 4.02/0.99  fof(f67,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f49])).
% 4.02/0.99  
% 4.02/0.99  fof(f58,plain,(
% 4.02/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f46])).
% 4.02/0.99  
% 4.02/0.99  fof(f15,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f33,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.02/0.99    inference(ennf_transformation,[],[f15])).
% 4.02/0.99  
% 4.02/0.99  fof(f34,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/0.99    inference(flattening,[],[f33])).
% 4.02/0.99  
% 4.02/0.99  fof(f50,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/0.99    inference(nnf_transformation,[],[f34])).
% 4.02/0.99  
% 4.02/0.99  fof(f76,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f50])).
% 4.02/0.99  
% 4.02/0.99  fof(f93,plain,(
% 4.02/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f16,axiom,(
% 4.02/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f78,plain,(
% 4.02/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f16])).
% 4.02/0.99  
% 4.02/0.99  fof(f20,axiom,(
% 4.02/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f84,plain,(
% 4.02/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f20])).
% 4.02/0.99  
% 4.02/0.99  fof(f99,plain,(
% 4.02/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.02/0.99    inference(definition_unfolding,[],[f78,f84])).
% 4.02/0.99  
% 4.02/0.99  fof(f18,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f37,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.02/0.99    inference(ennf_transformation,[],[f18])).
% 4.02/0.99  
% 4.02/0.99  fof(f38,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.02/0.99    inference(flattening,[],[f37])).
% 4.02/0.99  
% 4.02/0.99  fof(f82,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f38])).
% 4.02/0.99  
% 4.02/0.99  fof(f11,axiom,(
% 4.02/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f31,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f11])).
% 4.02/0.99  
% 4.02/0.99  fof(f70,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f31])).
% 4.02/0.99  
% 4.02/0.99  fof(f12,axiom,(
% 4.02/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f72,plain,(
% 4.02/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.02/0.99    inference(cnf_transformation,[],[f12])).
% 4.02/0.99  
% 4.02/0.99  fof(f95,plain,(
% 4.02/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 4.02/0.99    inference(definition_unfolding,[],[f72,f84])).
% 4.02/0.99  
% 4.02/0.99  fof(f13,axiom,(
% 4.02/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f74,plain,(
% 4.02/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f13])).
% 4.02/0.99  
% 4.02/0.99  fof(f97,plain,(
% 4.02/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 4.02/0.99    inference(definition_unfolding,[],[f74,f84])).
% 4.02/0.99  
% 4.02/0.99  fof(f6,axiom,(
% 4.02/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f47,plain,(
% 4.02/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.02/0.99    inference(nnf_transformation,[],[f6])).
% 4.02/0.99  
% 4.02/0.99  fof(f48,plain,(
% 4.02/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.02/0.99    inference(flattening,[],[f47])).
% 4.02/0.99  
% 4.02/0.99  fof(f63,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.02/0.99    inference(cnf_transformation,[],[f48])).
% 4.02/0.99  
% 4.02/0.99  fof(f103,plain,(
% 4.02/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.02/0.99    inference(equality_resolution,[],[f63])).
% 4.02/0.99  
% 4.02/0.99  fof(f64,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.02/0.99    inference(cnf_transformation,[],[f48])).
% 4.02/0.99  
% 4.02/0.99  fof(f102,plain,(
% 4.02/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.02/0.99    inference(equality_resolution,[],[f64])).
% 4.02/0.99  
% 4.02/0.99  fof(f7,axiom,(
% 4.02/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f28,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f7])).
% 4.02/0.99  
% 4.02/0.99  fof(f65,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f28])).
% 4.02/0.99  
% 4.02/0.99  fof(f1,axiom,(
% 4.02/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f25,plain,(
% 4.02/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f1])).
% 4.02/0.99  
% 4.02/0.99  fof(f55,plain,(
% 4.02/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f25])).
% 4.02/0.99  
% 4.02/0.99  fof(f3,axiom,(
% 4.02/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f59,plain,(
% 4.02/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f3])).
% 4.02/0.99  
% 4.02/0.99  fof(f4,axiom,(
% 4.02/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f60,plain,(
% 4.02/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f4])).
% 4.02/0.99  
% 4.02/0.99  fof(f5,axiom,(
% 4.02/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f26,plain,(
% 4.02/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 4.02/0.99    inference(ennf_transformation,[],[f5])).
% 4.02/0.99  
% 4.02/0.99  fof(f27,plain,(
% 4.02/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 4.02/0.99    inference(flattening,[],[f26])).
% 4.02/0.99  
% 4.02/0.99  fof(f61,plain,(
% 4.02/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f27])).
% 4.02/0.99  
% 4.02/0.99  cnf(c_36,negated_conjecture,
% 4.02/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f89]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1148,plain,
% 4.02/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_33,negated_conjecture,
% 4.02/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f92]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1151,plain,
% 4.02/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_28,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.02/0.99      | ~ v1_funct_1(X0)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1154,plain,
% 4.02/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.02/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | v1_funct_1(X5) != iProver_top
% 4.02/1.00      | v1_funct_1(X4) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_3968,plain,
% 4.02/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.02/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/1.00      | v1_funct_1(X2) != iProver_top
% 4.02/1.00      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_1151,c_1154]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_35,negated_conjecture,
% 4.02/1.00      ( v1_funct_1(sK3) ),
% 4.02/1.00      inference(cnf_transformation,[],[f90]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_42,plain,
% 4.02/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_4287,plain,
% 4.02/1.00      ( v1_funct_1(X2) != iProver_top
% 4.02/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/1.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_3968,c_42]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_4288,plain,
% 4.02/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.02/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/1.00      | v1_funct_1(X2) != iProver_top ),
% 4.02/1.00      inference(renaming,[status(thm)],[c_4287]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_4298,plain,
% 4.02/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 4.02/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_1148,c_4288]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_38,negated_conjecture,
% 4.02/1.00      ( v1_funct_1(sK2) ),
% 4.02/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1481,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 4.02/1.00      | ~ v1_funct_1(X0)
% 4.02/1.00      | ~ v1_funct_1(sK3)
% 4.02/1.00      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1762,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 4.02/1.00      | ~ v1_funct_1(sK2)
% 4.02/1.00      | ~ v1_funct_1(sK3)
% 4.02/1.00      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_1481]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2256,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.02/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/1.00      | ~ v1_funct_1(sK2)
% 4.02/1.00      | ~ v1_funct_1(sK3)
% 4.02/1.00      | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_1762]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_3386,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.02/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.02/1.00      | ~ v1_funct_1(sK2)
% 4.02/1.00      | ~ v1_funct_1(sK3)
% 4.02/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_2256]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_4409,plain,
% 4.02/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_4298,c_38,c_36,c_35,c_33,c_3386]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_30,plain,
% 4.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.02/1.00      | ~ v1_funct_2(X3,X4,X1)
% 4.02/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 4.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | ~ v1_funct_1(X0)
% 4.02/1.00      | ~ v1_funct_1(X3)
% 4.02/1.00      | v2_funct_1(X3)
% 4.02/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 4.02/1.00      | k1_xboole_0 = X2 ),
% 4.02/1.00      inference(cnf_transformation,[],[f85]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1152,plain,
% 4.02/1.00      ( k1_xboole_0 = X0
% 4.02/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 4.02/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 4.02/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 4.02/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.02/1.00      | v1_funct_1(X1) != iProver_top
% 4.02/1.00      | v1_funct_1(X3) != iProver_top
% 4.02/1.00      | v2_funct_1(X3) = iProver_top
% 4.02/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_4415,plain,
% 4.02/1.00      ( sK0 = k1_xboole_0
% 4.02/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.02/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 4.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.02/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.02/1.00      | v1_funct_1(sK2) != iProver_top
% 4.02/1.00      | v1_funct_1(sK3) != iProver_top
% 4.02/1.00      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 4.02/1.00      | v2_funct_1(sK2) = iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_4409,c_1152]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_39,plain,
% 4.02/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_37,negated_conjecture,
% 4.02/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 4.02/1.00      inference(cnf_transformation,[],[f88]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_40,plain,
% 4.02/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_41,plain,
% 4.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_34,negated_conjecture,
% 4.02/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f91]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_43,plain,
% 4.02/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_44,plain,
% 4.02/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_12,plain,
% 4.02/1.00      ( v5_relat_1(X0,X1)
% 4.02/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 4.02/1.00      | ~ v1_relat_1(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_24,plain,
% 4.02/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 4.02/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 4.02/1.00      | ~ v1_relat_1(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f105]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_31,negated_conjecture,
% 4.02/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 4.02/1.00      inference(cnf_transformation,[],[f94]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_413,plain,
% 4.02/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 4.02/1.00      | ~ v2_funct_1(sK2)
% 4.02/1.00      | ~ v1_relat_1(X0)
% 4.02/1.00      | k2_relat_1(X0) != sK0
% 4.02/1.00      | sK3 != X0 ),
% 4.02/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_414,plain,
% 4.02/1.00      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 4.02/1.00      | ~ v2_funct_1(sK2)
% 4.02/1.00      | ~ v1_relat_1(sK3)
% 4.02/1.00      | k2_relat_1(sK3) != sK0 ),
% 4.02/1.00      inference(unflattening,[status(thm)],[c_413]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_467,plain,
% 4.02/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 4.02/1.00      | ~ v2_funct_1(sK2)
% 4.02/1.00      | ~ v1_relat_1(X0)
% 4.02/1.00      | ~ v1_relat_1(sK3)
% 4.02/1.00      | k2_relat_1(sK3) != X1
% 4.02/1.00      | k2_relat_1(sK3) != sK0
% 4.02/1.00      | sK3 != X0 ),
% 4.02/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_414]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_468,plain,
% 4.02/1.00      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 4.02/1.00      | ~ v2_funct_1(sK2)
% 4.02/1.00      | ~ v1_relat_1(sK3)
% 4.02/1.00      | k2_relat_1(sK3) != sK0 ),
% 4.02/1.00      inference(unflattening,[status(thm)],[c_467]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2,plain,
% 4.02/1.00      ( r1_tarski(X0,X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f100]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_478,plain,
% 4.02/1.00      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 4.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_468,c_2]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_479,plain,
% 4.02/1.00      ( k2_relat_1(sK3) != sK0
% 4.02/1.00      | v2_funct_1(sK2) != iProver_top
% 4.02/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_11,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/1.00      | ~ v1_relat_1(X1)
% 4.02/1.00      | v1_relat_1(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f66]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1162,plain,
% 4.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.02/1.00      | v1_relat_1(X1) != iProver_top
% 4.02/1.00      | v1_relat_1(X0) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2788,plain,
% 4.02/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 4.02/1.00      | v1_relat_1(sK3) = iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_1151,c_1162]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_14,plain,
% 4.02/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.02/1.00      inference(cnf_transformation,[],[f69]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1161,plain,
% 4.02/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2894,plain,
% 4.02/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 4.02/1.00      inference(forward_subsumption_resolution,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_2788,c_1161]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2789,plain,
% 4.02/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 4.02/1.00      | v1_relat_1(sK2) = iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_1148,c_1162]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2949,plain,
% 4.02/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 4.02/1.00      inference(forward_subsumption_resolution,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_2789,c_1161]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_20,plain,
% 4.02/1.00      ( v5_relat_1(X0,X1)
% 4.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.02/1.00      inference(cnf_transformation,[],[f75]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_13,plain,
% 4.02/1.00      ( ~ v5_relat_1(X0,X1)
% 4.02/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 4.02/1.00      | ~ v1_relat_1(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_434,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 4.02/1.00      | ~ v1_relat_1(X0) ),
% 4.02/1.00      inference(resolution,[status(thm)],[c_20,c_13]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1143,plain,
% 4.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.02/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 4.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2594,plain,
% 4.02/1.00      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 4.02/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_1151,c_1143]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1,plain,
% 4.02/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.02/1.00      inference(cnf_transformation,[],[f58]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1166,plain,
% 4.02/1.00      ( X0 = X1
% 4.02/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.02/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2806,plain,
% 4.02/1.00      ( k2_relat_1(sK3) = sK0
% 4.02/1.00      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 4.02/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_2594,c_1166]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2952,plain,
% 4.02/1.00      ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 4.02/1.00      | k2_relat_1(sK3) = sK0 ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_2806,c_2894]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2953,plain,
% 4.02/1.00      ( k2_relat_1(sK3) = sK0
% 4.02/1.00      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
% 4.02/1.00      inference(renaming,[status(thm)],[c_2952]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_22,plain,
% 4.02/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/1.00      | X3 = X2 ),
% 4.02/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_32,negated_conjecture,
% 4.02/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 4.02/1.00      inference(cnf_transformation,[],[f93]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_395,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | X3 = X0
% 4.02/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 4.02/1.00      | k6_partfun1(sK0) != X3
% 4.02/1.00      | sK0 != X2
% 4.02/1.00      | sK0 != X1 ),
% 4.02/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_396,plain,
% 4.02/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.02/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.02/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.02/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_23,plain,
% 4.02/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.02/1.00      inference(cnf_transformation,[],[f99]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_404,plain,
% 4.02/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.02/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.02/1.00      inference(forward_subsumption_resolution,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_396,c_23]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1144,plain,
% 4.02/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.02/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_4412,plain,
% 4.02/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 4.02/1.00      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.02/1.00      inference(demodulation,[status(thm)],[c_4409,c_1144]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_26,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.02/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.02/1.00      | ~ v1_funct_1(X0)
% 4.02/1.00      | ~ v1_funct_1(X3) ),
% 4.02/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1156,plain,
% 4.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.02/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 4.02/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 4.02/1.00      | v1_funct_1(X0) != iProver_top
% 4.02/1.00      | v1_funct_1(X3) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_4928,plain,
% 4.02/1.00      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 4.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.02/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.02/1.00      | v1_funct_1(sK2) != iProver_top
% 4.02/1.00      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_4409,c_1156]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_5285,plain,
% 4.02/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_4412,c_39,c_41,c_42,c_44,c_4928]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15,plain,
% 4.02/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 4.02/1.00      | ~ v1_relat_1(X0)
% 4.02/1.00      | ~ v1_relat_1(X1) ),
% 4.02/1.00      inference(cnf_transformation,[],[f70]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1160,plain,
% 4.02/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 4.02/1.00      | v1_relat_1(X0) != iProver_top
% 4.02/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_5289,plain,
% 4.02/1.00      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 4.02/1.00      | v1_relat_1(sK2) != iProver_top
% 4.02/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_5285,c_1160]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_16,plain,
% 4.02/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 4.02/1.00      inference(cnf_transformation,[],[f95]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_5290,plain,
% 4.02/1.00      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 4.02/1.00      | v1_relat_1(sK2) != iProver_top
% 4.02/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.02/1.00      inference(demodulation,[status(thm)],[c_5289,c_16]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15482,plain,
% 4.02/1.00      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 4.02/1.00      | sK0 = k1_xboole_0 ),
% 4.02/1.00      inference(global_propositional_subsumption,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_4415,c_39,c_40,c_41,c_42,c_43,c_44,c_479,c_2806,
% 4.02/1.00                 c_2894,c_2949,c_5290]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15483,plain,
% 4.02/1.00      ( sK0 = k1_xboole_0
% 4.02/1.00      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 4.02/1.00      inference(renaming,[status(thm)],[c_15482]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15486,plain,
% 4.02/1.00      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 4.02/1.00      inference(light_normalisation,[status(thm)],[c_15483,c_5285]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_18,plain,
% 4.02/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 4.02/1.00      inference(cnf_transformation,[],[f97]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1159,plain,
% 4.02/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15489,plain,
% 4.02/1.00      ( sK0 = k1_xboole_0 ),
% 4.02/1.00      inference(forward_subsumption_resolution,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_15486,c_1159]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15576,plain,
% 4.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 4.02/1.00      inference(demodulation,[status(thm)],[c_15489,c_1148]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_8,plain,
% 4.02/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.02/1.00      inference(cnf_transformation,[],[f103]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_15584,plain,
% 4.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.02/1.00      inference(demodulation,[status(thm)],[c_15576,c_8]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_676,plain,
% 4.02/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 4.02/1.00      theory(equality) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7107,plain,
% 4.02/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_676]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7109,plain,
% 4.02/1.00      ( v2_funct_1(sK2)
% 4.02/1.00      | ~ v2_funct_1(k1_xboole_0)
% 4.02/1.00      | sK2 != k1_xboole_0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_7107]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_667,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2664,plain,
% 4.02/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_667]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_5222,plain,
% 4.02/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_2664]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_5223,plain,
% 4.02/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_5222]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_7,plain,
% 4.02/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.02/1.00      inference(cnf_transformation,[],[f102]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1157,plain,
% 4.02/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2368,plain,
% 4.02/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_7,c_1157]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_10,plain,
% 4.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/1.00      | ~ v1_xboole_0(X1)
% 4.02/1.00      | v1_xboole_0(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f65]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1163,plain,
% 4.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.02/1.00      | v1_xboole_0(X1) != iProver_top
% 4.02/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_3354,plain,
% 4.02/1.00      ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
% 4.02/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.02/1.00      inference(superposition,[status(thm)],[c_2368,c_1163]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_2895,plain,
% 4.02/1.00      ( v1_relat_1(sK3) ),
% 4.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2894]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1960,plain,
% 4.02/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 4.02/1.00      | ~ v1_xboole_0(X0)
% 4.02/1.00      | v1_xboole_0(sK2) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1961,plain,
% 4.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 4.02/1.00      | v1_xboole_0(X0) != iProver_top
% 4.02/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1960]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1963,plain,
% 4.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 4.02/1.00      | v1_xboole_0(sK2) = iProver_top
% 4.02/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_1961]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_0,plain,
% 4.02/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 4.02/1.00      inference(cnf_transformation,[],[f55]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1693,plain,
% 4.02/1.00      ( ~ v1_xboole_0(k6_partfun1(X0)) | k1_xboole_0 = k6_partfun1(X0) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1697,plain,
% 4.02/1.00      ( k1_xboole_0 = k6_partfun1(X0)
% 4.02/1.00      | v1_xboole_0(k6_partfun1(X0)) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1699,plain,
% 4.02/1.00      ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 4.02/1.00      | v1_xboole_0(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_1697]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_666,plain,( X0 = X0 ),theory(equality) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1606,plain,
% 4.02/1.00      ( sK2 = sK2 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_666]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1543,plain,
% 4.02/1.00      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1547,plain,
% 4.02/1.00      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1543]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1397,plain,
% 4.02/1.00      ( v2_funct_1(X0)
% 4.02/1.00      | ~ v2_funct_1(k6_partfun1(X1))
% 4.02/1.00      | X0 != k6_partfun1(X1) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_676]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_1399,plain,
% 4.02/1.00      ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
% 4.02/1.00      | v2_funct_1(k1_xboole_0)
% 4.02/1.00      | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_1397]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_4,plain,
% 4.02/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_110,plain,
% 4.02/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_112,plain,
% 4.02/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_110]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_5,plain,
% 4.02/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f60]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_107,plain,
% 4.02/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_109,plain,
% 4.02/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_107]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_6,plain,
% 4.02/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 4.02/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_104,plain,
% 4.02/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 4.02/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.02/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.02/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_106,plain,
% 4.02/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.02/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.02/1.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_104]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(c_84,plain,
% 4.02/1.00      ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
% 4.02/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 4.02/1.00  
% 4.02/1.00  cnf(contradiction,plain,
% 4.02/1.00      ( $false ),
% 4.02/1.00      inference(minisat,
% 4.02/1.00                [status(thm)],
% 4.02/1.00                [c_15584,c_7109,c_5290,c_5223,c_3354,c_2953,c_2949,
% 4.02/1.00                 c_2895,c_2894,c_1963,c_1699,c_1606,c_1547,c_1399,c_478,
% 4.02/1.00                 c_112,c_109,c_106,c_84]) ).
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/1.00  
% 4.02/1.00  ------                               Statistics
% 4.02/1.00  
% 4.02/1.00  ------ General
% 4.02/1.00  
% 4.02/1.00  abstr_ref_over_cycles:                  0
% 4.02/1.00  abstr_ref_under_cycles:                 0
% 4.02/1.00  gc_basic_clause_elim:                   0
% 4.02/1.00  forced_gc_time:                         0
% 4.02/1.00  parsing_time:                           0.011
% 4.02/1.00  unif_index_cands_time:                  0.
% 4.02/1.00  unif_index_add_time:                    0.
% 4.02/1.00  orderings_time:                         0.
% 4.02/1.00  out_proof_time:                         0.013
% 4.02/1.00  total_time:                             0.486
% 4.02/1.00  num_of_symbols:                         54
% 4.02/1.00  num_of_terms:                           17724
% 4.02/1.00  
% 4.02/1.00  ------ Preprocessing
% 4.02/1.00  
% 4.02/1.00  num_of_splits:                          0
% 4.02/1.00  num_of_split_atoms:                     0
% 4.02/1.00  num_of_reused_defs:                     0
% 4.02/1.00  num_eq_ax_congr_red:                    11
% 4.02/1.00  num_of_sem_filtered_clauses:            1
% 4.02/1.00  num_of_subtypes:                        0
% 4.02/1.00  monotx_restored_types:                  0
% 4.02/1.00  sat_num_of_epr_types:                   0
% 4.02/1.00  sat_num_of_non_cyclic_types:            0
% 4.02/1.00  sat_guarded_non_collapsed_types:        0
% 4.02/1.00  num_pure_diseq_elim:                    0
% 4.02/1.00  simp_replaced_by:                       0
% 4.02/1.00  res_preprocessed:                       160
% 4.02/1.00  prep_upred:                             0
% 4.02/1.00  prep_unflattend:                        17
% 4.02/1.00  smt_new_axioms:                         0
% 4.02/1.00  pred_elim_cands:                        7
% 4.02/1.00  pred_elim:                              4
% 4.02/1.00  pred_elim_cl:                           7
% 4.02/1.00  pred_elim_cycles:                       6
% 4.02/1.00  merged_defs:                            0
% 4.02/1.00  merged_defs_ncl:                        0
% 4.02/1.00  bin_hyper_res:                          0
% 4.02/1.00  prep_cycles:                            4
% 4.02/1.00  pred_elim_time:                         0.003
% 4.02/1.00  splitting_time:                         0.
% 4.02/1.00  sem_filter_time:                        0.
% 4.02/1.00  monotx_time:                            0.
% 4.02/1.00  subtype_inf_time:                       0.
% 4.02/1.00  
% 4.02/1.00  ------ Problem properties
% 4.02/1.00  
% 4.02/1.00  clauses:                                31
% 4.02/1.00  conjectures:                            6
% 4.02/1.00  epr:                                    9
% 4.02/1.00  horn:                                   29
% 4.02/1.00  ground:                                 8
% 4.02/1.00  unary:                                  16
% 4.02/1.00  binary:                                 3
% 4.02/1.00  lits:                                   75
% 4.02/1.00  lits_eq:                                13
% 4.02/1.00  fd_pure:                                0
% 4.02/1.00  fd_pseudo:                              0
% 4.02/1.00  fd_cond:                                3
% 4.02/1.00  fd_pseudo_cond:                         1
% 4.02/1.00  ac_symbols:                             0
% 4.02/1.00  
% 4.02/1.00  ------ Propositional Solver
% 4.02/1.00  
% 4.02/1.00  prop_solver_calls:                      29
% 4.02/1.00  prop_fast_solver_calls:                 1454
% 4.02/1.00  smt_solver_calls:                       0
% 4.02/1.00  smt_fast_solver_calls:                  0
% 4.02/1.00  prop_num_of_clauses:                    6582
% 4.02/1.00  prop_preprocess_simplified:             15276
% 4.02/1.00  prop_fo_subsumed:                       68
% 4.02/1.00  prop_solver_time:                       0.
% 4.02/1.00  smt_solver_time:                        0.
% 4.02/1.00  smt_fast_solver_time:                   0.
% 4.02/1.00  prop_fast_solver_time:                  0.
% 4.02/1.00  prop_unsat_core_time:                   0.001
% 4.02/1.00  
% 4.02/1.00  ------ QBF
% 4.02/1.00  
% 4.02/1.00  qbf_q_res:                              0
% 4.02/1.00  qbf_num_tautologies:                    0
% 4.02/1.00  qbf_prep_cycles:                        0
% 4.02/1.00  
% 4.02/1.00  ------ BMC1
% 4.02/1.00  
% 4.02/1.00  bmc1_current_bound:                     -1
% 4.02/1.00  bmc1_last_solved_bound:                 -1
% 4.02/1.00  bmc1_unsat_core_size:                   -1
% 4.02/1.00  bmc1_unsat_core_parents_size:           -1
% 4.02/1.00  bmc1_merge_next_fun:                    0
% 4.02/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.02/1.00  
% 4.02/1.00  ------ Instantiation
% 4.02/1.00  
% 4.02/1.00  inst_num_of_clauses:                    1757
% 4.02/1.00  inst_num_in_passive:                    848
% 4.02/1.00  inst_num_in_active:                     746
% 4.02/1.00  inst_num_in_unprocessed:                167
% 4.02/1.00  inst_num_of_loops:                      810
% 4.02/1.00  inst_num_of_learning_restarts:          0
% 4.02/1.00  inst_num_moves_active_passive:          63
% 4.02/1.00  inst_lit_activity:                      0
% 4.02/1.00  inst_lit_activity_moves:                1
% 4.02/1.00  inst_num_tautologies:                   0
% 4.02/1.00  inst_num_prop_implied:                  0
% 4.02/1.00  inst_num_existing_simplified:           0
% 4.02/1.00  inst_num_eq_res_simplified:             0
% 4.02/1.00  inst_num_child_elim:                    0
% 4.02/1.00  inst_num_of_dismatching_blockings:      112
% 4.02/1.00  inst_num_of_non_proper_insts:           1250
% 4.02/1.00  inst_num_of_duplicates:                 0
% 4.02/1.00  inst_inst_num_from_inst_to_res:         0
% 4.02/1.00  inst_dismatching_checking_time:         0.
% 4.02/1.00  
% 4.02/1.00  ------ Resolution
% 4.02/1.00  
% 4.02/1.00  res_num_of_clauses:                     0
% 4.02/1.00  res_num_in_passive:                     0
% 4.02/1.00  res_num_in_active:                      0
% 4.02/1.00  res_num_of_loops:                       164
% 4.02/1.00  res_forward_subset_subsumed:            56
% 4.02/1.00  res_backward_subset_subsumed:           8
% 4.02/1.00  res_forward_subsumed:                   0
% 4.02/1.00  res_backward_subsumed:                  1
% 4.02/1.00  res_forward_subsumption_resolution:     2
% 4.02/1.00  res_backward_subsumption_resolution:    0
% 4.02/1.00  res_clause_to_clause_subsumption:       3743
% 4.02/1.00  res_orphan_elimination:                 0
% 4.02/1.00  res_tautology_del:                      19
% 4.02/1.00  res_num_eq_res_simplified:              0
% 4.02/1.00  res_num_sel_changes:                    0
% 4.02/1.00  res_moves_from_active_to_pass:          0
% 4.02/1.00  
% 4.02/1.00  ------ Superposition
% 4.02/1.00  
% 4.02/1.00  sup_time_total:                         0.
% 4.02/1.00  sup_time_generating:                    0.
% 4.02/1.00  sup_time_sim_full:                      0.
% 4.02/1.00  sup_time_sim_immed:                     0.
% 4.02/1.00  
% 4.02/1.00  sup_num_of_clauses:                     347
% 4.02/1.00  sup_num_in_active:                      61
% 4.02/1.00  sup_num_in_passive:                     286
% 4.02/1.00  sup_num_of_loops:                       161
% 4.02/1.00  sup_fw_superposition:                   262
% 4.02/1.00  sup_bw_superposition:                   124
% 4.02/1.00  sup_immediate_simplified:               81
% 4.02/1.00  sup_given_eliminated:                   1
% 4.02/1.00  comparisons_done:                       0
% 4.02/1.00  comparisons_avoided:                    0
% 4.02/1.00  
% 4.02/1.00  ------ Simplifications
% 4.02/1.00  
% 4.02/1.00  
% 4.02/1.00  sim_fw_subset_subsumed:                 5
% 4.02/1.00  sim_bw_subset_subsumed:                 14
% 4.02/1.00  sim_fw_subsumed:                        10
% 4.02/1.00  sim_bw_subsumed:                        2
% 4.02/1.00  sim_fw_subsumption_res:                 20
% 4.02/1.00  sim_bw_subsumption_res:                 0
% 4.02/1.00  sim_tautology_del:                      2
% 4.02/1.00  sim_eq_tautology_del:                   9
% 4.02/1.00  sim_eq_res_simp:                        0
% 4.02/1.00  sim_fw_demodulated:                     21
% 4.02/1.00  sim_bw_demodulated:                     94
% 4.02/1.00  sim_light_normalised:                   41
% 4.02/1.00  sim_joinable_taut:                      0
% 4.02/1.00  sim_joinable_simp:                      0
% 4.02/1.00  sim_ac_normalised:                      0
% 4.02/1.00  sim_smt_subsumption:                    0
% 4.02/1.00  
%------------------------------------------------------------------------------
