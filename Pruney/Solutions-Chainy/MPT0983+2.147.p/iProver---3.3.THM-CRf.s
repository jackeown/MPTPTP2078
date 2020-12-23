%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:16 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 746 expanded)
%              Number of clauses        :  118 ( 234 expanded)
%              Number of leaves         :   27 ( 181 expanded)
%              Depth                    :   20
%              Number of atoms          :  643 (4215 expanded)
%              Number of equality atoms :  227 ( 420 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f73,f84])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f53,f52])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f71,f84])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f94,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f95,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f70,f84])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f84])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1191,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_421,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_27,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_429,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_421,c_27])).

cnf(c_1176,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1236,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1507,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1176,c_38,c_36,c_35,c_33,c_429,c_1236])).

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

cnf(c_1184,plain,
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

cnf(c_3233,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_1184])).

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

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_86,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_88,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_16,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_117,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_121,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_126,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_31,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_438,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_439,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_492,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_439])).

cnf(c_493,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_503,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_493,c_3])).

cnf(c_504,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_708,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1249,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1250,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_1252,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_1303,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1304,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_1306,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1423,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1424,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1423])).

cnf(c_1361,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1465,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_698,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1534,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1535,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_1753,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1496,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1833,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_1834,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_1183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_9])).

cnf(c_1175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_2084,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1175])).

cnf(c_1198,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2445,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1198])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1195,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2564,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1196])).

cnf(c_2570,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_2564])).

cnf(c_1180,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2565,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1196])).

cnf(c_3014,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_2565])).

cnf(c_699,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3221,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_3222,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3221])).

cnf(c_3224,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3222])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1186,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3382,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1186])).

cnf(c_3414,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3382,c_42])).

cnf(c_3415,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3414])).

cnf(c_3422,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_3415])).

cnf(c_3424,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3422,c_1507])).

cnf(c_3526,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_39])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1192,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3529,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_1192])).

cnf(c_14,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3530,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3529,c_14])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1193,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3528,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_1193])).

cnf(c_15,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3531,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3528,c_15])).

cnf(c_4207,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3531,c_2570,c_3014])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_7])).

cnf(c_1177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_2656,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1177])).

cnf(c_3049,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2656,c_3014])).

cnf(c_3053,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_1198])).

cnf(c_4212,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_4207,c_3053])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1194,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6309,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_1194])).

cnf(c_6596,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3233,c_39,c_40,c_41,c_42,c_43,c_44,c_88,c_16,c_117,c_121,c_126,c_504,c_1252,c_1306,c_1424,c_1465,c_1535,c_1753,c_1834,c_2445,c_2570,c_3014,c_3224,c_3530,c_6309])).

cnf(c_6600,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1191,c_6596])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.84/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.03  
% 3.84/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.03  
% 3.84/1.03  ------  iProver source info
% 3.84/1.03  
% 3.84/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.03  git: non_committed_changes: false
% 3.84/1.03  git: last_make_outside_of_git: false
% 3.84/1.03  
% 3.84/1.03  ------ 
% 3.84/1.03  
% 3.84/1.03  ------ Input Options
% 3.84/1.03  
% 3.84/1.03  --out_options                           all
% 3.84/1.03  --tptp_safe_out                         true
% 3.84/1.03  --problem_path                          ""
% 3.84/1.03  --include_path                          ""
% 3.84/1.03  --clausifier                            res/vclausify_rel
% 3.84/1.03  --clausifier_options                    ""
% 3.84/1.03  --stdin                                 false
% 3.84/1.03  --stats_out                             all
% 3.84/1.03  
% 3.84/1.03  ------ General Options
% 3.84/1.03  
% 3.84/1.03  --fof                                   false
% 3.84/1.03  --time_out_real                         305.
% 3.84/1.03  --time_out_virtual                      -1.
% 3.84/1.03  --symbol_type_check                     false
% 3.84/1.03  --clausify_out                          false
% 3.84/1.03  --sig_cnt_out                           false
% 3.84/1.03  --trig_cnt_out                          false
% 3.84/1.03  --trig_cnt_out_tolerance                1.
% 3.84/1.03  --trig_cnt_out_sk_spl                   false
% 3.84/1.03  --abstr_cl_out                          false
% 3.84/1.03  
% 3.84/1.03  ------ Global Options
% 3.84/1.03  
% 3.84/1.03  --schedule                              default
% 3.84/1.03  --add_important_lit                     false
% 3.84/1.03  --prop_solver_per_cl                    1000
% 3.84/1.03  --min_unsat_core                        false
% 3.84/1.03  --soft_assumptions                      false
% 3.84/1.03  --soft_lemma_size                       3
% 3.84/1.03  --prop_impl_unit_size                   0
% 3.84/1.03  --prop_impl_unit                        []
% 3.84/1.03  --share_sel_clauses                     true
% 3.84/1.03  --reset_solvers                         false
% 3.84/1.03  --bc_imp_inh                            [conj_cone]
% 3.84/1.03  --conj_cone_tolerance                   3.
% 3.84/1.03  --extra_neg_conj                        none
% 3.84/1.03  --large_theory_mode                     true
% 3.84/1.03  --prolific_symb_bound                   200
% 3.84/1.03  --lt_threshold                          2000
% 3.84/1.03  --clause_weak_htbl                      true
% 3.84/1.03  --gc_record_bc_elim                     false
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing Options
% 3.84/1.03  
% 3.84/1.03  --preprocessing_flag                    true
% 3.84/1.03  --time_out_prep_mult                    0.1
% 3.84/1.03  --splitting_mode                        input
% 3.84/1.03  --splitting_grd                         true
% 3.84/1.03  --splitting_cvd                         false
% 3.84/1.03  --splitting_cvd_svl                     false
% 3.84/1.03  --splitting_nvd                         32
% 3.84/1.03  --sub_typing                            true
% 3.84/1.03  --prep_gs_sim                           true
% 3.84/1.03  --prep_unflatten                        true
% 3.84/1.03  --prep_res_sim                          true
% 3.84/1.03  --prep_upred                            true
% 3.84/1.03  --prep_sem_filter                       exhaustive
% 3.84/1.03  --prep_sem_filter_out                   false
% 3.84/1.03  --pred_elim                             true
% 3.84/1.03  --res_sim_input                         true
% 3.84/1.03  --eq_ax_congr_red                       true
% 3.84/1.03  --pure_diseq_elim                       true
% 3.84/1.03  --brand_transform                       false
% 3.84/1.03  --non_eq_to_eq                          false
% 3.84/1.03  --prep_def_merge                        true
% 3.84/1.03  --prep_def_merge_prop_impl              false
% 3.84/1.03  --prep_def_merge_mbd                    true
% 3.84/1.03  --prep_def_merge_tr_red                 false
% 3.84/1.03  --prep_def_merge_tr_cl                  false
% 3.84/1.03  --smt_preprocessing                     true
% 3.84/1.03  --smt_ac_axioms                         fast
% 3.84/1.03  --preprocessed_out                      false
% 3.84/1.03  --preprocessed_stats                    false
% 3.84/1.03  
% 3.84/1.03  ------ Abstraction refinement Options
% 3.84/1.03  
% 3.84/1.03  --abstr_ref                             []
% 3.84/1.03  --abstr_ref_prep                        false
% 3.84/1.03  --abstr_ref_until_sat                   false
% 3.84/1.03  --abstr_ref_sig_restrict                funpre
% 3.84/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.03  --abstr_ref_under                       []
% 3.84/1.03  
% 3.84/1.03  ------ SAT Options
% 3.84/1.03  
% 3.84/1.03  --sat_mode                              false
% 3.84/1.03  --sat_fm_restart_options                ""
% 3.84/1.03  --sat_gr_def                            false
% 3.84/1.03  --sat_epr_types                         true
% 3.84/1.03  --sat_non_cyclic_types                  false
% 3.84/1.03  --sat_finite_models                     false
% 3.84/1.03  --sat_fm_lemmas                         false
% 3.84/1.03  --sat_fm_prep                           false
% 3.84/1.03  --sat_fm_uc_incr                        true
% 3.84/1.03  --sat_out_model                         small
% 3.84/1.03  --sat_out_clauses                       false
% 3.84/1.03  
% 3.84/1.03  ------ QBF Options
% 3.84/1.03  
% 3.84/1.03  --qbf_mode                              false
% 3.84/1.03  --qbf_elim_univ                         false
% 3.84/1.03  --qbf_dom_inst                          none
% 3.84/1.03  --qbf_dom_pre_inst                      false
% 3.84/1.03  --qbf_sk_in                             false
% 3.84/1.03  --qbf_pred_elim                         true
% 3.84/1.03  --qbf_split                             512
% 3.84/1.03  
% 3.84/1.03  ------ BMC1 Options
% 3.84/1.03  
% 3.84/1.03  --bmc1_incremental                      false
% 3.84/1.03  --bmc1_axioms                           reachable_all
% 3.84/1.03  --bmc1_min_bound                        0
% 3.84/1.03  --bmc1_max_bound                        -1
% 3.84/1.03  --bmc1_max_bound_default                -1
% 3.84/1.03  --bmc1_symbol_reachability              true
% 3.84/1.03  --bmc1_property_lemmas                  false
% 3.84/1.03  --bmc1_k_induction                      false
% 3.84/1.03  --bmc1_non_equiv_states                 false
% 3.84/1.03  --bmc1_deadlock                         false
% 3.84/1.03  --bmc1_ucm                              false
% 3.84/1.03  --bmc1_add_unsat_core                   none
% 3.84/1.03  --bmc1_unsat_core_children              false
% 3.84/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.03  --bmc1_out_stat                         full
% 3.84/1.03  --bmc1_ground_init                      false
% 3.84/1.03  --bmc1_pre_inst_next_state              false
% 3.84/1.03  --bmc1_pre_inst_state                   false
% 3.84/1.03  --bmc1_pre_inst_reach_state             false
% 3.84/1.03  --bmc1_out_unsat_core                   false
% 3.84/1.03  --bmc1_aig_witness_out                  false
% 3.84/1.03  --bmc1_verbose                          false
% 3.84/1.03  --bmc1_dump_clauses_tptp                false
% 3.84/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.03  --bmc1_dump_file                        -
% 3.84/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.03  --bmc1_ucm_extend_mode                  1
% 3.84/1.03  --bmc1_ucm_init_mode                    2
% 3.84/1.03  --bmc1_ucm_cone_mode                    none
% 3.84/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.03  --bmc1_ucm_relax_model                  4
% 3.84/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.03  --bmc1_ucm_layered_model                none
% 3.84/1.03  --bmc1_ucm_max_lemma_size               10
% 3.84/1.03  
% 3.84/1.03  ------ AIG Options
% 3.84/1.03  
% 3.84/1.03  --aig_mode                              false
% 3.84/1.03  
% 3.84/1.03  ------ Instantiation Options
% 3.84/1.03  
% 3.84/1.03  --instantiation_flag                    true
% 3.84/1.03  --inst_sos_flag                         true
% 3.84/1.03  --inst_sos_phase                        true
% 3.84/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.03  --inst_lit_sel_side                     num_symb
% 3.84/1.03  --inst_solver_per_active                1400
% 3.84/1.03  --inst_solver_calls_frac                1.
% 3.84/1.03  --inst_passive_queue_type               priority_queues
% 3.84/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.03  --inst_passive_queues_freq              [25;2]
% 3.84/1.03  --inst_dismatching                      true
% 3.84/1.03  --inst_eager_unprocessed_to_passive     true
% 3.84/1.03  --inst_prop_sim_given                   true
% 3.84/1.03  --inst_prop_sim_new                     false
% 3.84/1.03  --inst_subs_new                         false
% 3.84/1.03  --inst_eq_res_simp                      false
% 3.84/1.03  --inst_subs_given                       false
% 3.84/1.03  --inst_orphan_elimination               true
% 3.84/1.03  --inst_learning_loop_flag               true
% 3.84/1.03  --inst_learning_start                   3000
% 3.84/1.03  --inst_learning_factor                  2
% 3.84/1.03  --inst_start_prop_sim_after_learn       3
% 3.84/1.03  --inst_sel_renew                        solver
% 3.84/1.03  --inst_lit_activity_flag                true
% 3.84/1.03  --inst_restr_to_given                   false
% 3.84/1.03  --inst_activity_threshold               500
% 3.84/1.03  --inst_out_proof                        true
% 3.84/1.03  
% 3.84/1.03  ------ Resolution Options
% 3.84/1.03  
% 3.84/1.03  --resolution_flag                       true
% 3.84/1.03  --res_lit_sel                           adaptive
% 3.84/1.03  --res_lit_sel_side                      none
% 3.84/1.03  --res_ordering                          kbo
% 3.84/1.03  --res_to_prop_solver                    active
% 3.84/1.03  --res_prop_simpl_new                    false
% 3.84/1.03  --res_prop_simpl_given                  true
% 3.84/1.03  --res_passive_queue_type                priority_queues
% 3.84/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.03  --res_passive_queues_freq               [15;5]
% 3.84/1.03  --res_forward_subs                      full
% 3.84/1.03  --res_backward_subs                     full
% 3.84/1.03  --res_forward_subs_resolution           true
% 3.84/1.03  --res_backward_subs_resolution          true
% 3.84/1.03  --res_orphan_elimination                true
% 3.84/1.03  --res_time_limit                        2.
% 3.84/1.03  --res_out_proof                         true
% 3.84/1.03  
% 3.84/1.03  ------ Superposition Options
% 3.84/1.03  
% 3.84/1.03  --superposition_flag                    true
% 3.84/1.03  --sup_passive_queue_type                priority_queues
% 3.84/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.03  --demod_completeness_check              fast
% 3.84/1.03  --demod_use_ground                      true
% 3.84/1.03  --sup_to_prop_solver                    passive
% 3.84/1.03  --sup_prop_simpl_new                    true
% 3.84/1.03  --sup_prop_simpl_given                  true
% 3.84/1.03  --sup_fun_splitting                     true
% 3.84/1.03  --sup_smt_interval                      50000
% 3.84/1.03  
% 3.84/1.03  ------ Superposition Simplification Setup
% 3.84/1.03  
% 3.84/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/1.03  --sup_immed_triv                        [TrivRules]
% 3.84/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_immed_bw_main                     []
% 3.84/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_input_bw                          []
% 3.84/1.03  
% 3.84/1.03  ------ Combination Options
% 3.84/1.03  
% 3.84/1.03  --comb_res_mult                         3
% 3.84/1.03  --comb_sup_mult                         2
% 3.84/1.03  --comb_inst_mult                        10
% 3.84/1.03  
% 3.84/1.03  ------ Debug Options
% 3.84/1.03  
% 3.84/1.03  --dbg_backtrace                         false
% 3.84/1.03  --dbg_dump_prop_clauses                 false
% 3.84/1.03  --dbg_dump_prop_clauses_file            -
% 3.84/1.03  --dbg_out_stat                          false
% 3.84/1.03  ------ Parsing...
% 3.84/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.03  ------ Proving...
% 3.84/1.03  ------ Problem Properties 
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  clauses                                 30
% 3.84/1.03  conjectures                             6
% 3.84/1.03  EPR                                     8
% 3.84/1.03  Horn                                    29
% 3.84/1.03  unary                                   15
% 3.84/1.03  binary                                  2
% 3.84/1.03  lits                                    75
% 3.84/1.03  lits eq                                 9
% 3.84/1.03  fd_pure                                 0
% 3.84/1.03  fd_pseudo                               0
% 3.84/1.03  fd_cond                                 2
% 3.84/1.03  fd_pseudo_cond                          1
% 3.84/1.03  AC symbols                              0
% 3.84/1.03  
% 3.84/1.03  ------ Schedule dynamic 5 is on 
% 3.84/1.03  
% 3.84/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  ------ 
% 3.84/1.03  Current options:
% 3.84/1.03  ------ 
% 3.84/1.03  
% 3.84/1.03  ------ Input Options
% 3.84/1.03  
% 3.84/1.03  --out_options                           all
% 3.84/1.03  --tptp_safe_out                         true
% 3.84/1.03  --problem_path                          ""
% 3.84/1.03  --include_path                          ""
% 3.84/1.03  --clausifier                            res/vclausify_rel
% 3.84/1.03  --clausifier_options                    ""
% 3.84/1.03  --stdin                                 false
% 3.84/1.03  --stats_out                             all
% 3.84/1.03  
% 3.84/1.03  ------ General Options
% 3.84/1.03  
% 3.84/1.03  --fof                                   false
% 3.84/1.03  --time_out_real                         305.
% 3.84/1.03  --time_out_virtual                      -1.
% 3.84/1.03  --symbol_type_check                     false
% 3.84/1.03  --clausify_out                          false
% 3.84/1.03  --sig_cnt_out                           false
% 3.84/1.03  --trig_cnt_out                          false
% 3.84/1.03  --trig_cnt_out_tolerance                1.
% 3.84/1.03  --trig_cnt_out_sk_spl                   false
% 3.84/1.03  --abstr_cl_out                          false
% 3.84/1.03  
% 3.84/1.03  ------ Global Options
% 3.84/1.03  
% 3.84/1.03  --schedule                              default
% 3.84/1.03  --add_important_lit                     false
% 3.84/1.03  --prop_solver_per_cl                    1000
% 3.84/1.03  --min_unsat_core                        false
% 3.84/1.03  --soft_assumptions                      false
% 3.84/1.03  --soft_lemma_size                       3
% 3.84/1.03  --prop_impl_unit_size                   0
% 3.84/1.03  --prop_impl_unit                        []
% 3.84/1.03  --share_sel_clauses                     true
% 3.84/1.03  --reset_solvers                         false
% 3.84/1.03  --bc_imp_inh                            [conj_cone]
% 3.84/1.03  --conj_cone_tolerance                   3.
% 3.84/1.03  --extra_neg_conj                        none
% 3.84/1.03  --large_theory_mode                     true
% 3.84/1.03  --prolific_symb_bound                   200
% 3.84/1.03  --lt_threshold                          2000
% 3.84/1.03  --clause_weak_htbl                      true
% 3.84/1.03  --gc_record_bc_elim                     false
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing Options
% 3.84/1.03  
% 3.84/1.03  --preprocessing_flag                    true
% 3.84/1.03  --time_out_prep_mult                    0.1
% 3.84/1.03  --splitting_mode                        input
% 3.84/1.03  --splitting_grd                         true
% 3.84/1.03  --splitting_cvd                         false
% 3.84/1.03  --splitting_cvd_svl                     false
% 3.84/1.03  --splitting_nvd                         32
% 3.84/1.03  --sub_typing                            true
% 3.84/1.03  --prep_gs_sim                           true
% 3.84/1.03  --prep_unflatten                        true
% 3.84/1.03  --prep_res_sim                          true
% 3.84/1.03  --prep_upred                            true
% 3.84/1.03  --prep_sem_filter                       exhaustive
% 3.84/1.03  --prep_sem_filter_out                   false
% 3.84/1.03  --pred_elim                             true
% 3.84/1.03  --res_sim_input                         true
% 3.84/1.03  --eq_ax_congr_red                       true
% 3.84/1.03  --pure_diseq_elim                       true
% 3.84/1.03  --brand_transform                       false
% 3.84/1.03  --non_eq_to_eq                          false
% 3.84/1.03  --prep_def_merge                        true
% 3.84/1.03  --prep_def_merge_prop_impl              false
% 3.84/1.03  --prep_def_merge_mbd                    true
% 3.84/1.03  --prep_def_merge_tr_red                 false
% 3.84/1.03  --prep_def_merge_tr_cl                  false
% 3.84/1.03  --smt_preprocessing                     true
% 3.84/1.03  --smt_ac_axioms                         fast
% 3.84/1.03  --preprocessed_out                      false
% 3.84/1.03  --preprocessed_stats                    false
% 3.84/1.03  
% 3.84/1.03  ------ Abstraction refinement Options
% 3.84/1.03  
% 3.84/1.03  --abstr_ref                             []
% 3.84/1.03  --abstr_ref_prep                        false
% 3.84/1.03  --abstr_ref_until_sat                   false
% 3.84/1.03  --abstr_ref_sig_restrict                funpre
% 3.84/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.03  --abstr_ref_under                       []
% 3.84/1.03  
% 3.84/1.03  ------ SAT Options
% 3.84/1.03  
% 3.84/1.03  --sat_mode                              false
% 3.84/1.03  --sat_fm_restart_options                ""
% 3.84/1.03  --sat_gr_def                            false
% 3.84/1.03  --sat_epr_types                         true
% 3.84/1.03  --sat_non_cyclic_types                  false
% 3.84/1.03  --sat_finite_models                     false
% 3.84/1.03  --sat_fm_lemmas                         false
% 3.84/1.03  --sat_fm_prep                           false
% 3.84/1.03  --sat_fm_uc_incr                        true
% 3.84/1.03  --sat_out_model                         small
% 3.84/1.03  --sat_out_clauses                       false
% 3.84/1.03  
% 3.84/1.03  ------ QBF Options
% 3.84/1.03  
% 3.84/1.03  --qbf_mode                              false
% 3.84/1.03  --qbf_elim_univ                         false
% 3.84/1.03  --qbf_dom_inst                          none
% 3.84/1.03  --qbf_dom_pre_inst                      false
% 3.84/1.03  --qbf_sk_in                             false
% 3.84/1.03  --qbf_pred_elim                         true
% 3.84/1.03  --qbf_split                             512
% 3.84/1.03  
% 3.84/1.03  ------ BMC1 Options
% 3.84/1.03  
% 3.84/1.03  --bmc1_incremental                      false
% 3.84/1.03  --bmc1_axioms                           reachable_all
% 3.84/1.03  --bmc1_min_bound                        0
% 3.84/1.03  --bmc1_max_bound                        -1
% 3.84/1.03  --bmc1_max_bound_default                -1
% 3.84/1.03  --bmc1_symbol_reachability              true
% 3.84/1.03  --bmc1_property_lemmas                  false
% 3.84/1.03  --bmc1_k_induction                      false
% 3.84/1.03  --bmc1_non_equiv_states                 false
% 3.84/1.03  --bmc1_deadlock                         false
% 3.84/1.03  --bmc1_ucm                              false
% 3.84/1.03  --bmc1_add_unsat_core                   none
% 3.84/1.03  --bmc1_unsat_core_children              false
% 3.84/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.03  --bmc1_out_stat                         full
% 3.84/1.03  --bmc1_ground_init                      false
% 3.84/1.03  --bmc1_pre_inst_next_state              false
% 3.84/1.03  --bmc1_pre_inst_state                   false
% 3.84/1.03  --bmc1_pre_inst_reach_state             false
% 3.84/1.03  --bmc1_out_unsat_core                   false
% 3.84/1.03  --bmc1_aig_witness_out                  false
% 3.84/1.03  --bmc1_verbose                          false
% 3.84/1.03  --bmc1_dump_clauses_tptp                false
% 3.84/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.03  --bmc1_dump_file                        -
% 3.84/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.03  --bmc1_ucm_extend_mode                  1
% 3.84/1.03  --bmc1_ucm_init_mode                    2
% 3.84/1.03  --bmc1_ucm_cone_mode                    none
% 3.84/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.03  --bmc1_ucm_relax_model                  4
% 3.84/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.03  --bmc1_ucm_layered_model                none
% 3.84/1.03  --bmc1_ucm_max_lemma_size               10
% 3.84/1.03  
% 3.84/1.03  ------ AIG Options
% 3.84/1.03  
% 3.84/1.03  --aig_mode                              false
% 3.84/1.03  
% 3.84/1.03  ------ Instantiation Options
% 3.84/1.03  
% 3.84/1.03  --instantiation_flag                    true
% 3.84/1.03  --inst_sos_flag                         true
% 3.84/1.03  --inst_sos_phase                        true
% 3.84/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.03  --inst_lit_sel_side                     none
% 3.84/1.03  --inst_solver_per_active                1400
% 3.84/1.03  --inst_solver_calls_frac                1.
% 3.84/1.03  --inst_passive_queue_type               priority_queues
% 3.84/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.03  --inst_passive_queues_freq              [25;2]
% 3.84/1.03  --inst_dismatching                      true
% 3.84/1.03  --inst_eager_unprocessed_to_passive     true
% 3.84/1.03  --inst_prop_sim_given                   true
% 3.84/1.03  --inst_prop_sim_new                     false
% 3.84/1.03  --inst_subs_new                         false
% 3.84/1.03  --inst_eq_res_simp                      false
% 3.84/1.03  --inst_subs_given                       false
% 3.84/1.03  --inst_orphan_elimination               true
% 3.84/1.03  --inst_learning_loop_flag               true
% 3.84/1.03  --inst_learning_start                   3000
% 3.84/1.03  --inst_learning_factor                  2
% 3.84/1.03  --inst_start_prop_sim_after_learn       3
% 3.84/1.03  --inst_sel_renew                        solver
% 3.84/1.03  --inst_lit_activity_flag                true
% 3.84/1.03  --inst_restr_to_given                   false
% 3.84/1.03  --inst_activity_threshold               500
% 3.84/1.03  --inst_out_proof                        true
% 3.84/1.03  
% 3.84/1.03  ------ Resolution Options
% 3.84/1.03  
% 3.84/1.03  --resolution_flag                       false
% 3.84/1.03  --res_lit_sel                           adaptive
% 3.84/1.03  --res_lit_sel_side                      none
% 3.84/1.03  --res_ordering                          kbo
% 3.84/1.03  --res_to_prop_solver                    active
% 3.84/1.03  --res_prop_simpl_new                    false
% 3.84/1.03  --res_prop_simpl_given                  true
% 3.84/1.03  --res_passive_queue_type                priority_queues
% 3.84/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.03  --res_passive_queues_freq               [15;5]
% 3.84/1.03  --res_forward_subs                      full
% 3.84/1.03  --res_backward_subs                     full
% 3.84/1.03  --res_forward_subs_resolution           true
% 3.84/1.03  --res_backward_subs_resolution          true
% 3.84/1.03  --res_orphan_elimination                true
% 3.84/1.03  --res_time_limit                        2.
% 3.84/1.03  --res_out_proof                         true
% 3.84/1.03  
% 3.84/1.03  ------ Superposition Options
% 3.84/1.03  
% 3.84/1.03  --superposition_flag                    true
% 3.84/1.03  --sup_passive_queue_type                priority_queues
% 3.84/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.03  --demod_completeness_check              fast
% 3.84/1.03  --demod_use_ground                      true
% 3.84/1.03  --sup_to_prop_solver                    passive
% 3.84/1.03  --sup_prop_simpl_new                    true
% 3.84/1.03  --sup_prop_simpl_given                  true
% 3.84/1.03  --sup_fun_splitting                     true
% 3.84/1.03  --sup_smt_interval                      50000
% 3.84/1.03  
% 3.84/1.03  ------ Superposition Simplification Setup
% 3.84/1.03  
% 3.84/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/1.03  --sup_immed_triv                        [TrivRules]
% 3.84/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_immed_bw_main                     []
% 3.84/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.03  --sup_input_bw                          []
% 3.84/1.03  
% 3.84/1.03  ------ Combination Options
% 3.84/1.03  
% 3.84/1.03  --comb_res_mult                         3
% 3.84/1.03  --comb_sup_mult                         2
% 3.84/1.03  --comb_inst_mult                        10
% 3.84/1.03  
% 3.84/1.03  ------ Debug Options
% 3.84/1.03  
% 3.84/1.03  --dbg_backtrace                         false
% 3.84/1.03  --dbg_dump_prop_clauses                 false
% 3.84/1.03  --dbg_dump_prop_clauses_file            -
% 3.84/1.03  --dbg_out_stat                          false
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  ------ Proving...
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  % SZS status Theorem for theBenchmark.p
% 3.84/1.03  
% 3.84/1.03   Resolution empty clause
% 3.84/1.03  
% 3.84/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.03  
% 3.84/1.03  fof(f13,axiom,(
% 3.84/1.03    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f73,plain,(
% 3.84/1.03    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.84/1.03    inference(cnf_transformation,[],[f13])).
% 3.84/1.03  
% 3.84/1.03  fof(f20,axiom,(
% 3.84/1.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f84,plain,(
% 3.84/1.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f20])).
% 3.84/1.03  
% 3.84/1.03  fof(f98,plain,(
% 3.84/1.03    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.84/1.03    inference(definition_unfolding,[],[f73,f84])).
% 3.84/1.03  
% 3.84/1.03  fof(f15,axiom,(
% 3.84/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f34,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.84/1.03    inference(ennf_transformation,[],[f15])).
% 3.84/1.03  
% 3.84/1.03  fof(f35,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/1.03    inference(flattening,[],[f34])).
% 3.84/1.03  
% 3.84/1.03  fof(f50,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/1.03    inference(nnf_transformation,[],[f35])).
% 3.84/1.03  
% 3.84/1.03  fof(f76,plain,(
% 3.84/1.03    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/1.03    inference(cnf_transformation,[],[f50])).
% 3.84/1.03  
% 3.84/1.03  fof(f22,conjecture,(
% 3.84/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f23,negated_conjecture,(
% 3.84/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.84/1.03    inference(negated_conjecture,[],[f22])).
% 3.84/1.03  
% 3.84/1.03  fof(f44,plain,(
% 3.84/1.03    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.84/1.03    inference(ennf_transformation,[],[f23])).
% 3.84/1.03  
% 3.84/1.03  fof(f45,plain,(
% 3.84/1.03    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.84/1.03    inference(flattening,[],[f44])).
% 3.84/1.03  
% 3.84/1.03  fof(f53,plain,(
% 3.84/1.03    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.84/1.03    introduced(choice_axiom,[])).
% 3.84/1.03  
% 3.84/1.03  fof(f52,plain,(
% 3.84/1.03    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.84/1.03    introduced(choice_axiom,[])).
% 3.84/1.03  
% 3.84/1.03  fof(f54,plain,(
% 3.84/1.03    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.84/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f53,f52])).
% 3.84/1.03  
% 3.84/1.03  fof(f93,plain,(
% 3.84/1.03    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.84/1.03    inference(cnf_transformation,[],[f54])).
% 3.84/1.03  
% 3.84/1.03  fof(f18,axiom,(
% 3.84/1.03    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f24,plain,(
% 3.84/1.03    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.84/1.03    inference(pure_predicate_removal,[],[f18])).
% 3.84/1.03  
% 3.84/1.03  fof(f82,plain,(
% 3.84/1.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.84/1.03    inference(cnf_transformation,[],[f24])).
% 3.84/1.03  
% 3.84/1.03  fof(f87,plain,(
% 3.84/1.03    v1_funct_1(sK2)),
% 3.84/1.03    inference(cnf_transformation,[],[f54])).
% 3.84/1.03  
% 3.84/1.03  fof(f89,plain,(
% 3.84/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.84/1.03    inference(cnf_transformation,[],[f54])).
% 3.84/1.03  
% 3.84/1.03  fof(f90,plain,(
% 3.84/1.03    v1_funct_1(sK3)),
% 3.84/1.03    inference(cnf_transformation,[],[f54])).
% 3.84/1.03  
% 3.84/1.03  fof(f92,plain,(
% 3.84/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.84/1.03    inference(cnf_transformation,[],[f54])).
% 3.84/1.03  
% 3.84/1.03  fof(f17,axiom,(
% 3.84/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f38,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.84/1.03    inference(ennf_transformation,[],[f17])).
% 3.84/1.03  
% 3.84/1.03  fof(f39,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.84/1.03    inference(flattening,[],[f38])).
% 3.84/1.03  
% 3.84/1.03  fof(f81,plain,(
% 3.84/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f39])).
% 3.84/1.03  
% 3.84/1.03  fof(f21,axiom,(
% 3.84/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f42,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.84/1.03    inference(ennf_transformation,[],[f21])).
% 3.84/1.03  
% 3.84/1.03  fof(f43,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.84/1.03    inference(flattening,[],[f42])).
% 3.84/1.03  
% 3.84/1.03  fof(f85,plain,(
% 3.84/1.03    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f43])).
% 3.84/1.03  
% 3.84/1.03  fof(f88,plain,(
% 3.84/1.03    v1_funct_2(sK2,sK0,sK1)),
% 3.84/1.03    inference(cnf_transformation,[],[f54])).
% 3.84/1.03  
% 3.84/1.03  fof(f91,plain,(
% 3.84/1.03    v1_funct_2(sK3,sK1,sK0)),
% 3.84/1.03    inference(cnf_transformation,[],[f54])).
% 3.84/1.03  
% 3.84/1.03  fof(f12,axiom,(
% 3.84/1.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f71,plain,(
% 3.84/1.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.84/1.03    inference(cnf_transformation,[],[f12])).
% 3.84/1.03  
% 3.84/1.03  fof(f97,plain,(
% 3.84/1.03    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.84/1.03    inference(definition_unfolding,[],[f71,f84])).
% 3.84/1.03  
% 3.84/1.03  fof(f3,axiom,(
% 3.84/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f46,plain,(
% 3.84/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/1.03    inference(nnf_transformation,[],[f3])).
% 3.84/1.03  
% 3.84/1.03  fof(f47,plain,(
% 3.84/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/1.03    inference(flattening,[],[f46])).
% 3.84/1.03  
% 3.84/1.03  fof(f57,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.84/1.03    inference(cnf_transformation,[],[f47])).
% 3.84/1.03  
% 3.84/1.03  fof(f101,plain,(
% 3.84/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/1.03    inference(equality_resolution,[],[f57])).
% 3.84/1.03  
% 3.84/1.03  fof(f59,plain,(
% 3.84/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f47])).
% 3.84/1.03  
% 3.84/1.03  fof(f1,axiom,(
% 3.84/1.03    v1_xboole_0(k1_xboole_0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f55,plain,(
% 3.84/1.03    v1_xboole_0(k1_xboole_0)),
% 3.84/1.03    inference(cnf_transformation,[],[f1])).
% 3.84/1.03  
% 3.84/1.03  fof(f6,axiom,(
% 3.84/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f28,plain,(
% 3.84/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.84/1.03    inference(ennf_transformation,[],[f6])).
% 3.84/1.03  
% 3.84/1.03  fof(f49,plain,(
% 3.84/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.84/1.03    inference(nnf_transformation,[],[f28])).
% 3.84/1.03  
% 3.84/1.03  fof(f64,plain,(
% 3.84/1.03    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f49])).
% 3.84/1.03  
% 3.84/1.03  fof(f16,axiom,(
% 3.84/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f36,plain,(
% 3.84/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.84/1.03    inference(ennf_transformation,[],[f16])).
% 3.84/1.03  
% 3.84/1.03  fof(f37,plain,(
% 3.84/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.84/1.03    inference(flattening,[],[f36])).
% 3.84/1.03  
% 3.84/1.03  fof(f51,plain,(
% 3.84/1.03    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.84/1.03    inference(nnf_transformation,[],[f37])).
% 3.84/1.03  
% 3.84/1.03  fof(f79,plain,(
% 3.84/1.03    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f51])).
% 3.84/1.03  
% 3.84/1.03  fof(f103,plain,(
% 3.84/1.03    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.84/1.03    inference(equality_resolution,[],[f79])).
% 3.84/1.03  
% 3.84/1.03  fof(f94,plain,(
% 3.84/1.03    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.84/1.03    inference(cnf_transformation,[],[f54])).
% 3.84/1.03  
% 3.84/1.03  fof(f58,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.84/1.03    inference(cnf_transformation,[],[f47])).
% 3.84/1.03  
% 3.84/1.03  fof(f100,plain,(
% 3.84/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/1.03    inference(equality_resolution,[],[f58])).
% 3.84/1.03  
% 3.84/1.03  fof(f2,axiom,(
% 3.84/1.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f25,plain,(
% 3.84/1.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.84/1.03    inference(ennf_transformation,[],[f2])).
% 3.84/1.03  
% 3.84/1.03  fof(f56,plain,(
% 3.84/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f25])).
% 3.84/1.03  
% 3.84/1.03  fof(f14,axiom,(
% 3.84/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f33,plain,(
% 3.84/1.03    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/1.03    inference(ennf_transformation,[],[f14])).
% 3.84/1.03  
% 3.84/1.03  fof(f75,plain,(
% 3.84/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/1.03    inference(cnf_transformation,[],[f33])).
% 3.84/1.03  
% 3.84/1.03  fof(f63,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f49])).
% 3.84/1.03  
% 3.84/1.03  fof(f7,axiom,(
% 3.84/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f65,plain,(
% 3.84/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.84/1.03    inference(cnf_transformation,[],[f7])).
% 3.84/1.03  
% 3.84/1.03  fof(f4,axiom,(
% 3.84/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f26,plain,(
% 3.84/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.84/1.03    inference(ennf_transformation,[],[f4])).
% 3.84/1.03  
% 3.84/1.03  fof(f60,plain,(
% 3.84/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f26])).
% 3.84/1.03  
% 3.84/1.03  fof(f19,axiom,(
% 3.84/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f40,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.84/1.03    inference(ennf_transformation,[],[f19])).
% 3.84/1.03  
% 3.84/1.03  fof(f41,plain,(
% 3.84/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.84/1.03    inference(flattening,[],[f40])).
% 3.84/1.03  
% 3.84/1.03  fof(f83,plain,(
% 3.84/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f41])).
% 3.84/1.03  
% 3.84/1.03  fof(f10,axiom,(
% 3.84/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f32,plain,(
% 3.84/1.03    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.84/1.03    inference(ennf_transformation,[],[f10])).
% 3.84/1.03  
% 3.84/1.03  fof(f68,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f32])).
% 3.84/1.03  
% 3.84/1.03  fof(f11,axiom,(
% 3.84/1.03    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f70,plain,(
% 3.84/1.03    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.84/1.03    inference(cnf_transformation,[],[f11])).
% 3.84/1.03  
% 3.84/1.03  fof(f95,plain,(
% 3.84/1.03    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.84/1.03    inference(definition_unfolding,[],[f70,f84])).
% 3.84/1.03  
% 3.84/1.03  fof(f9,axiom,(
% 3.84/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f31,plain,(
% 3.84/1.03    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.84/1.03    inference(ennf_transformation,[],[f9])).
% 3.84/1.03  
% 3.84/1.03  fof(f67,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f31])).
% 3.84/1.03  
% 3.84/1.03  fof(f69,plain,(
% 3.84/1.03    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.84/1.03    inference(cnf_transformation,[],[f11])).
% 3.84/1.03  
% 3.84/1.03  fof(f96,plain,(
% 3.84/1.03    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.84/1.03    inference(definition_unfolding,[],[f69,f84])).
% 3.84/1.03  
% 3.84/1.03  fof(f74,plain,(
% 3.84/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/1.03    inference(cnf_transformation,[],[f33])).
% 3.84/1.03  
% 3.84/1.03  fof(f5,axiom,(
% 3.84/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f27,plain,(
% 3.84/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.84/1.03    inference(ennf_transformation,[],[f5])).
% 3.84/1.03  
% 3.84/1.03  fof(f48,plain,(
% 3.84/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.84/1.03    inference(nnf_transformation,[],[f27])).
% 3.84/1.03  
% 3.84/1.03  fof(f61,plain,(
% 3.84/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f48])).
% 3.84/1.03  
% 3.84/1.03  fof(f8,axiom,(
% 3.84/1.03    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 3.84/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/1.03  
% 3.84/1.03  fof(f29,plain,(
% 3.84/1.03    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.84/1.03    inference(ennf_transformation,[],[f8])).
% 3.84/1.03  
% 3.84/1.03  fof(f30,plain,(
% 3.84/1.03    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.84/1.03    inference(flattening,[],[f29])).
% 3.84/1.03  
% 3.84/1.03  fof(f66,plain,(
% 3.84/1.03    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.84/1.03    inference(cnf_transformation,[],[f30])).
% 3.84/1.03  
% 3.84/1.03  cnf(c_17,plain,
% 3.84/1.03      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.84/1.03      inference(cnf_transformation,[],[f98]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1191,plain,
% 3.84/1.03      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_22,plain,
% 3.84/1.03      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.84/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.84/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.84/1.03      | X3 = X2 ),
% 3.84/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_32,negated_conjecture,
% 3.84/1.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.84/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_420,plain,
% 3.84/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/1.03      | X3 = X0
% 3.84/1.03      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.84/1.03      | k6_partfun1(sK0) != X3
% 3.84/1.03      | sK0 != X2
% 3.84/1.03      | sK0 != X1 ),
% 3.84/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_421,plain,
% 3.84/1.03      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.84/1.03      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.84/1.03      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.84/1.03      inference(unflattening,[status(thm)],[c_420]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_27,plain,
% 3.84/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.84/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_429,plain,
% 3.84/1.03      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.84/1.03      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.84/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_421,c_27]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1176,plain,
% 3.84/1.03      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.84/1.03      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_38,negated_conjecture,
% 3.84/1.03      ( v1_funct_1(sK2) ),
% 3.84/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_36,negated_conjecture,
% 3.84/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.84/1.03      inference(cnf_transformation,[],[f89]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_35,negated_conjecture,
% 3.84/1.03      ( v1_funct_1(sK3) ),
% 3.84/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_33,negated_conjecture,
% 3.84/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.84/1.03      inference(cnf_transformation,[],[f92]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_25,plain,
% 3.84/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.84/1.03      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.84/1.03      | ~ v1_funct_1(X0)
% 3.84/1.03      | ~ v1_funct_1(X3) ),
% 3.84/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1236,plain,
% 3.84/1.03      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.84/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.84/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.84/1.03      | ~ v1_funct_1(sK2)
% 3.84/1.03      | ~ v1_funct_1(sK3) ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_25]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1507,plain,
% 3.84/1.03      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.84/1.03      inference(global_propositional_subsumption,
% 3.84/1.03                [status(thm)],
% 3.84/1.03                [c_1176,c_38,c_36,c_35,c_33,c_429,c_1236]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_30,plain,
% 3.84/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/1.03      | ~ v1_funct_2(X3,X4,X1)
% 3.84/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.84/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/1.03      | ~ v1_funct_1(X0)
% 3.84/1.03      | ~ v1_funct_1(X3)
% 3.84/1.03      | v2_funct_1(X3)
% 3.84/1.03      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.84/1.03      | k1_xboole_0 = X2 ),
% 3.84/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1184,plain,
% 3.84/1.03      ( k1_xboole_0 = X0
% 3.84/1.03      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.84/1.03      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.84/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.84/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.84/1.03      | v1_funct_1(X1) != iProver_top
% 3.84/1.03      | v1_funct_1(X3) != iProver_top
% 3.84/1.03      | v2_funct_1(X3) = iProver_top
% 3.84/1.03      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3233,plain,
% 3.84/1.03      ( sK0 = k1_xboole_0
% 3.84/1.03      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.84/1.03      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.84/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.84/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.84/1.03      | v1_funct_1(sK2) != iProver_top
% 3.84/1.03      | v1_funct_1(sK3) != iProver_top
% 3.84/1.03      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.84/1.03      | v2_funct_1(sK2) = iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1507,c_1184]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_39,plain,
% 3.84/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_37,negated_conjecture,
% 3.84/1.03      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.84/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_40,plain,
% 3.84/1.03      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_41,plain,
% 3.84/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_42,plain,
% 3.84/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_34,negated_conjecture,
% 3.84/1.03      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.84/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_43,plain,
% 3.84/1.03      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_44,plain,
% 3.84/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_86,plain,
% 3.84/1.03      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_88,plain,
% 3.84/1.03      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_86]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_16,plain,
% 3.84/1.03      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.84/1.03      inference(cnf_transformation,[],[f97]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f101]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_117,plain,
% 3.84/1.03      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_2,plain,
% 3.84/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.84/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_121,plain,
% 3.84/1.03      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_0,plain,
% 3.84/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 3.84/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_126,plain,
% 3.84/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_8,plain,
% 3.84/1.03      ( v5_relat_1(X0,X1) | ~ r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.84/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_23,plain,
% 3.84/1.03      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.84/1.03      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.84/1.03      | ~ v1_relat_1(X0) ),
% 3.84/1.03      inference(cnf_transformation,[],[f103]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_31,negated_conjecture,
% 3.84/1.03      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.84/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_438,plain,
% 3.84/1.03      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.84/1.03      | ~ v2_funct_1(sK2)
% 3.84/1.03      | ~ v1_relat_1(X0)
% 3.84/1.03      | k2_relat_1(X0) != sK0
% 3.84/1.03      | sK3 != X0 ),
% 3.84/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_439,plain,
% 3.84/1.03      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.84/1.03      | ~ v2_funct_1(sK2)
% 3.84/1.03      | ~ v1_relat_1(sK3)
% 3.84/1.03      | k2_relat_1(sK3) != sK0 ),
% 3.84/1.03      inference(unflattening,[status(thm)],[c_438]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_492,plain,
% 3.84/1.03      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.84/1.03      | ~ v2_funct_1(sK2)
% 3.84/1.03      | ~ v1_relat_1(X0)
% 3.84/1.03      | ~ v1_relat_1(sK3)
% 3.84/1.03      | k2_relat_1(sK3) != X1
% 3.84/1.03      | k2_relat_1(sK3) != sK0
% 3.84/1.03      | sK3 != X0 ),
% 3.84/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_439]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_493,plain,
% 3.84/1.03      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.84/1.03      | ~ v2_funct_1(sK2)
% 3.84/1.03      | ~ v1_relat_1(sK3)
% 3.84/1.03      | k2_relat_1(sK3) != sK0 ),
% 3.84/1.03      inference(unflattening,[status(thm)],[c_492]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f100]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_503,plain,
% 3.84/1.03      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.84/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_493,c_3]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_504,plain,
% 3.84/1.03      ( k2_relat_1(sK3) != sK0
% 3.84/1.03      | v2_funct_1(sK2) != iProver_top
% 3.84/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_708,plain,
% 3.84/1.03      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.84/1.03      theory(equality) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1249,plain,
% 3.84/1.03      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_708]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1250,plain,
% 3.84/1.03      ( sK2 != X0
% 3.84/1.03      | v2_funct_1(X0) != iProver_top
% 3.84/1.03      | v2_funct_1(sK2) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1252,plain,
% 3.84/1.03      ( sK2 != k1_xboole_0
% 3.84/1.03      | v2_funct_1(sK2) = iProver_top
% 3.84/1.03      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_1250]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1303,plain,
% 3.84/1.03      ( v2_funct_1(X0)
% 3.84/1.03      | ~ v2_funct_1(k6_partfun1(X1))
% 3.84/1.03      | X0 != k6_partfun1(X1) ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_708]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1304,plain,
% 3.84/1.03      ( X0 != k6_partfun1(X1)
% 3.84/1.03      | v2_funct_1(X0) = iProver_top
% 3.84/1.03      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1306,plain,
% 3.84/1.03      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.84/1.03      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.84/1.03      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_1304]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1,plain,
% 3.84/1.03      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.84/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1423,plain,
% 3.84/1.03      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1424,plain,
% 3.84/1.03      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_1423]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1361,plain,
% 3.84/1.03      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1465,plain,
% 3.84/1.03      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_1361]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_698,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1534,plain,
% 3.84/1.03      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_698]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1535,plain,
% 3.84/1.03      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.84/1.03      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.84/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_1534]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1753,plain,
% 3.84/1.03      ( r1_tarski(sK2,sK2) ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1496,plain,
% 3.84/1.03      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_698]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1833,plain,
% 3.84/1.03      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_1496]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1834,plain,
% 3.84/1.03      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_1833]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1183,plain,
% 3.84/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_19,plain,
% 3.84/1.03      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.84/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_9,plain,
% 3.84/1.03      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.84/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_459,plain,
% 3.84/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/1.03      | r1_tarski(k2_relat_1(X0),X2)
% 3.84/1.03      | ~ v1_relat_1(X0) ),
% 3.84/1.03      inference(resolution,[status(thm)],[c_19,c_9]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1175,plain,
% 3.84/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.84/1.03      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.84/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_2084,plain,
% 3.84/1.03      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.84/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1183,c_1175]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1198,plain,
% 3.84/1.03      ( X0 = X1
% 3.84/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.84/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_2445,plain,
% 3.84/1.03      ( k2_relat_1(sK3) = sK0
% 3.84/1.03      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.84/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_2084,c_1198]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_10,plain,
% 3.84/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.84/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1195,plain,
% 3.84/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_5,plain,
% 3.84/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.84/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1196,plain,
% 3.84/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.84/1.03      | v1_relat_1(X1) != iProver_top
% 3.84/1.03      | v1_relat_1(X0) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_2564,plain,
% 3.84/1.03      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.84/1.03      | v1_relat_1(sK3) = iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1183,c_1196]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_2570,plain,
% 3.84/1.03      ( v1_relat_1(sK3) = iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1195,c_2564]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1180,plain,
% 3.84/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_2565,plain,
% 3.84/1.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.84/1.03      | v1_relat_1(sK2) = iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1180,c_1196]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3014,plain,
% 3.84/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1195,c_2565]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_699,plain,
% 3.84/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.84/1.03      theory(equality) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3221,plain,
% 3.84/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_699]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3222,plain,
% 3.84/1.03      ( sK0 != X0
% 3.84/1.03      | v1_xboole_0(X0) != iProver_top
% 3.84/1.03      | v1_xboole_0(sK0) = iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_3221]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3224,plain,
% 3.84/1.03      ( sK0 != k1_xboole_0
% 3.84/1.03      | v1_xboole_0(sK0) = iProver_top
% 3.84/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.84/1.03      inference(instantiation,[status(thm)],[c_3222]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_28,plain,
% 3.84/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.84/1.03      | ~ v1_funct_1(X0)
% 3.84/1.03      | ~ v1_funct_1(X3)
% 3.84/1.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.84/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1186,plain,
% 3.84/1.03      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.84/1.03      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.84/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.84/1.03      | v1_funct_1(X5) != iProver_top
% 3.84/1.03      | v1_funct_1(X4) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3382,plain,
% 3.84/1.03      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.84/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.84/1.03      | v1_funct_1(X2) != iProver_top
% 3.84/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1183,c_1186]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3414,plain,
% 3.84/1.03      ( v1_funct_1(X2) != iProver_top
% 3.84/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.84/1.03      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.84/1.03      inference(global_propositional_subsumption,[status(thm)],[c_3382,c_42]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3415,plain,
% 3.84/1.03      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.84/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.84/1.03      | v1_funct_1(X2) != iProver_top ),
% 3.84/1.03      inference(renaming,[status(thm)],[c_3414]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3422,plain,
% 3.84/1.03      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.84/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1180,c_3415]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3424,plain,
% 3.84/1.03      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.84/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.84/1.03      inference(light_normalisation,[status(thm)],[c_3422,c_1507]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3526,plain,
% 3.84/1.03      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.84/1.03      inference(global_propositional_subsumption,[status(thm)],[c_3424,c_39]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_13,plain,
% 3.84/1.03      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.84/1.03      | ~ v1_relat_1(X0)
% 3.84/1.03      | ~ v1_relat_1(X1) ),
% 3.84/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1192,plain,
% 3.84/1.03      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.84/1.03      | v1_relat_1(X0) != iProver_top
% 3.84/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3529,plain,
% 3.84/1.03      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.84/1.03      | v1_relat_1(sK2) != iProver_top
% 3.84/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_3526,c_1192]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_14,plain,
% 3.84/1.03      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.84/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3530,plain,
% 3.84/1.03      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.84/1.03      | v1_relat_1(sK2) != iProver_top
% 3.84/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.84/1.03      inference(demodulation,[status(thm)],[c_3529,c_14]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_12,plain,
% 3.84/1.03      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.84/1.03      | ~ v1_relat_1(X0)
% 3.84/1.03      | ~ v1_relat_1(X1) ),
% 3.84/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1193,plain,
% 3.84/1.03      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.84/1.03      | v1_relat_1(X0) != iProver_top
% 3.84/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3528,plain,
% 3.84/1.03      ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 3.84/1.03      | v1_relat_1(sK2) != iProver_top
% 3.84/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_3526,c_1193]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_15,plain,
% 3.84/1.03      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.84/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3531,plain,
% 3.84/1.03      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 3.84/1.03      | v1_relat_1(sK2) != iProver_top
% 3.84/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.84/1.03      inference(demodulation,[status(thm)],[c_3528,c_15]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_4207,plain,
% 3.84/1.03      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 3.84/1.03      inference(global_propositional_subsumption,
% 3.84/1.03                [status(thm)],
% 3.84/1.03                [c_3531,c_2570,c_3014]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_20,plain,
% 3.84/1.03      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.84/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_7,plain,
% 3.84/1.03      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.84/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_399,plain,
% 3.84/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 3.84/1.03      | ~ v1_relat_1(X0) ),
% 3.84/1.03      inference(resolution,[status(thm)],[c_20,c_7]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1177,plain,
% 3.84/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.84/1.03      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.84/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_2656,plain,
% 3.84/1.03      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 3.84/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1180,c_1177]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3049,plain,
% 3.84/1.03      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.84/1.03      inference(global_propositional_subsumption,[status(thm)],[c_2656,c_3014]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_3053,plain,
% 3.84/1.03      ( k1_relat_1(sK2) = sK0 | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_3049,c_1198]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_4212,plain,
% 3.84/1.03      ( k1_relat_1(sK2) = sK0 ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_4207,c_3053]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_11,plain,
% 3.84/1.03      ( ~ v1_relat_1(X0) | v1_xboole_0(X0) | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 3.84/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_1194,plain,
% 3.84/1.03      ( v1_relat_1(X0) != iProver_top
% 3.84/1.03      | v1_xboole_0(X0) = iProver_top
% 3.84/1.03      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 3.84/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_6309,plain,
% 3.84/1.03      ( v1_relat_1(sK2) != iProver_top
% 3.84/1.03      | v1_xboole_0(sK2) = iProver_top
% 3.84/1.03      | v1_xboole_0(sK0) != iProver_top ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_4212,c_1194]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_6596,plain,
% 3.84/1.03      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.84/1.03      inference(global_propositional_subsumption,
% 3.84/1.03                [status(thm)],
% 3.84/1.03                [c_3233,c_39,c_40,c_41,c_42,c_43,c_44,c_88,c_16,c_117,c_121,
% 3.84/1.03                 c_126,c_504,c_1252,c_1306,c_1424,c_1465,c_1535,c_1753,
% 3.84/1.03                 c_1834,c_2445,c_2570,c_3014,c_3224,c_3530,c_6309]) ).
% 3.84/1.03  
% 3.84/1.03  cnf(c_6600,plain,
% 3.84/1.03      ( $false ),
% 3.84/1.03      inference(superposition,[status(thm)],[c_1191,c_6596]) ).
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.03  
% 3.84/1.03  ------                               Statistics
% 3.84/1.03  
% 3.84/1.03  ------ General
% 3.84/1.03  
% 3.84/1.03  abstr_ref_over_cycles:                  0
% 3.84/1.03  abstr_ref_under_cycles:                 0
% 3.84/1.03  gc_basic_clause_elim:                   0
% 3.84/1.03  forced_gc_time:                         0
% 3.84/1.03  parsing_time:                           0.011
% 3.84/1.03  unif_index_cands_time:                  0.
% 3.84/1.03  unif_index_add_time:                    0.
% 3.84/1.03  orderings_time:                         0.
% 3.84/1.03  out_proof_time:                         0.012
% 3.84/1.03  total_time:                             0.283
% 3.84/1.03  num_of_symbols:                         54
% 3.84/1.03  num_of_terms:                           10760
% 3.84/1.03  
% 3.84/1.03  ------ Preprocessing
% 3.84/1.03  
% 3.84/1.03  num_of_splits:                          0
% 3.84/1.03  num_of_split_atoms:                     0
% 3.84/1.03  num_of_reused_defs:                     0
% 3.84/1.03  num_eq_ax_congr_red:                    9
% 3.84/1.03  num_of_sem_filtered_clauses:            1
% 3.84/1.03  num_of_subtypes:                        0
% 3.84/1.03  monotx_restored_types:                  0
% 3.84/1.03  sat_num_of_epr_types:                   0
% 3.84/1.03  sat_num_of_non_cyclic_types:            0
% 3.84/1.03  sat_guarded_non_collapsed_types:        0
% 3.84/1.03  num_pure_diseq_elim:                    0
% 3.84/1.03  simp_replaced_by:                       0
% 3.84/1.03  res_preprocessed:                       159
% 3.84/1.03  prep_upred:                             0
% 3.84/1.03  prep_unflattend:                        15
% 3.84/1.03  smt_new_axioms:                         0
% 3.84/1.03  pred_elim_cands:                        7
% 3.84/1.03  pred_elim:                              4
% 3.84/1.03  pred_elim_cl:                           8
% 3.84/1.03  pred_elim_cycles:                       6
% 3.84/1.03  merged_defs:                            0
% 3.84/1.03  merged_defs_ncl:                        0
% 3.84/1.03  bin_hyper_res:                          0
% 3.84/1.03  prep_cycles:                            4
% 3.84/1.03  pred_elim_time:                         0.003
% 3.84/1.03  splitting_time:                         0.
% 3.84/1.03  sem_filter_time:                        0.
% 3.84/1.03  monotx_time:                            0.
% 3.84/1.03  subtype_inf_time:                       0.
% 3.84/1.03  
% 3.84/1.03  ------ Problem properties
% 3.84/1.03  
% 3.84/1.03  clauses:                                30
% 3.84/1.03  conjectures:                            6
% 3.84/1.03  epr:                                    8
% 3.84/1.03  horn:                                   29
% 3.84/1.03  ground:                                 10
% 3.84/1.03  unary:                                  15
% 3.84/1.03  binary:                                 2
% 3.84/1.03  lits:                                   75
% 3.84/1.03  lits_eq:                                9
% 3.84/1.03  fd_pure:                                0
% 3.84/1.03  fd_pseudo:                              0
% 3.84/1.03  fd_cond:                                2
% 3.84/1.03  fd_pseudo_cond:                         1
% 3.84/1.03  ac_symbols:                             0
% 3.84/1.03  
% 3.84/1.03  ------ Propositional Solver
% 3.84/1.03  
% 3.84/1.03  prop_solver_calls:                      33
% 3.84/1.03  prop_fast_solver_calls:                 1146
% 3.84/1.03  smt_solver_calls:                       0
% 3.84/1.03  smt_fast_solver_calls:                  0
% 3.84/1.03  prop_num_of_clauses:                    3322
% 3.84/1.03  prop_preprocess_simplified:             8320
% 3.84/1.03  prop_fo_subsumed:                       59
% 3.84/1.03  prop_solver_time:                       0.
% 3.84/1.03  smt_solver_time:                        0.
% 3.84/1.03  smt_fast_solver_time:                   0.
% 3.84/1.03  prop_fast_solver_time:                  0.
% 3.84/1.03  prop_unsat_core_time:                   0.
% 3.84/1.03  
% 3.84/1.03  ------ QBF
% 3.84/1.03  
% 3.84/1.03  qbf_q_res:                              0
% 3.84/1.03  qbf_num_tautologies:                    0
% 3.84/1.03  qbf_prep_cycles:                        0
% 3.84/1.03  
% 3.84/1.03  ------ BMC1
% 3.84/1.03  
% 3.84/1.03  bmc1_current_bound:                     -1
% 3.84/1.03  bmc1_last_solved_bound:                 -1
% 3.84/1.03  bmc1_unsat_core_size:                   -1
% 3.84/1.03  bmc1_unsat_core_parents_size:           -1
% 3.84/1.03  bmc1_merge_next_fun:                    0
% 3.84/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.84/1.03  
% 3.84/1.03  ------ Instantiation
% 3.84/1.03  
% 3.84/1.03  inst_num_of_clauses:                    905
% 3.84/1.03  inst_num_in_passive:                    253
% 3.84/1.03  inst_num_in_active:                     458
% 3.84/1.03  inst_num_in_unprocessed:                194
% 3.84/1.03  inst_num_of_loops:                      490
% 3.84/1.03  inst_num_of_learning_restarts:          0
% 3.84/1.03  inst_num_moves_active_passive:          27
% 3.84/1.03  inst_lit_activity:                      0
% 3.84/1.03  inst_lit_activity_moves:                0
% 3.84/1.03  inst_num_tautologies:                   0
% 3.84/1.03  inst_num_prop_implied:                  0
% 3.84/1.03  inst_num_existing_simplified:           0
% 3.84/1.03  inst_num_eq_res_simplified:             0
% 3.84/1.03  inst_num_child_elim:                    0
% 3.84/1.03  inst_num_of_dismatching_blockings:      196
% 3.84/1.03  inst_num_of_non_proper_insts:           1030
% 3.84/1.03  inst_num_of_duplicates:                 0
% 3.84/1.03  inst_inst_num_from_inst_to_res:         0
% 3.84/1.03  inst_dismatching_checking_time:         0.
% 3.84/1.03  
% 3.84/1.03  ------ Resolution
% 3.84/1.03  
% 3.84/1.03  res_num_of_clauses:                     0
% 3.84/1.03  res_num_in_passive:                     0
% 3.84/1.03  res_num_in_active:                      0
% 3.84/1.03  res_num_of_loops:                       163
% 3.84/1.03  res_forward_subset_subsumed:            88
% 3.84/1.03  res_backward_subset_subsumed:           0
% 3.84/1.03  res_forward_subsumed:                   0
% 3.84/1.03  res_backward_subsumed:                  1
% 3.84/1.03  res_forward_subsumption_resolution:     2
% 3.84/1.03  res_backward_subsumption_resolution:    0
% 3.84/1.03  res_clause_to_clause_subsumption:       316
% 3.84/1.03  res_orphan_elimination:                 0
% 3.84/1.03  res_tautology_del:                      81
% 3.84/1.03  res_num_eq_res_simplified:              0
% 3.84/1.03  res_num_sel_changes:                    0
% 3.84/1.03  res_moves_from_active_to_pass:          0
% 3.84/1.03  
% 3.84/1.03  ------ Superposition
% 3.84/1.03  
% 3.84/1.03  sup_time_total:                         0.
% 3.84/1.03  sup_time_generating:                    0.
% 3.84/1.03  sup_time_sim_full:                      0.
% 3.84/1.03  sup_time_sim_immed:                     0.
% 3.84/1.03  
% 3.84/1.03  sup_num_of_clauses:                     139
% 3.84/1.03  sup_num_in_active:                      83
% 3.84/1.03  sup_num_in_passive:                     56
% 3.84/1.03  sup_num_of_loops:                       96
% 3.84/1.03  sup_fw_superposition:                   78
% 3.84/1.03  sup_bw_superposition:                   70
% 3.84/1.03  sup_immediate_simplified:               43
% 3.84/1.03  sup_given_eliminated:                   1
% 3.84/1.03  comparisons_done:                       0
% 3.84/1.03  comparisons_avoided:                    0
% 3.84/1.03  
% 3.84/1.03  ------ Simplifications
% 3.84/1.03  
% 3.84/1.03  
% 3.84/1.03  sim_fw_subset_subsumed:                 3
% 3.84/1.03  sim_bw_subset_subsumed:                 14
% 3.84/1.03  sim_fw_subsumed:                        9
% 3.84/1.03  sim_bw_subsumed:                        2
% 3.84/1.03  sim_fw_subsumption_res:                 0
% 3.84/1.03  sim_bw_subsumption_res:                 0
% 3.84/1.03  sim_tautology_del:                      2
% 3.84/1.03  sim_eq_tautology_del:                   9
% 3.84/1.03  sim_eq_res_simp:                        1
% 3.84/1.03  sim_fw_demodulated:                     2
% 3.84/1.03  sim_bw_demodulated:                     5
% 3.84/1.03  sim_light_normalised:                   30
% 3.84/1.03  sim_joinable_taut:                      0
% 3.84/1.03  sim_joinable_simp:                      0
% 3.84/1.03  sim_ac_normalised:                      0
% 3.84/1.03  sim_smt_subsumption:                    0
% 3.84/1.03  
%------------------------------------------------------------------------------
