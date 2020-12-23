%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:45 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 456 expanded)
%              Number of clauses        :   88 ( 133 expanded)
%              Number of leaves         :   24 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  567 (2694 expanded)
%              Number of equality atoms :  148 ( 207 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
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
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f62,f71,f70])).

fof(f116,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f72])).

fof(f119,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f72])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f57])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f117,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f120,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f72])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f54])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f25,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f111,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f122,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f92,f111])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f65])).

fof(f79,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f98,f111])).

fof(f26,axiom,(
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

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f112,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f115,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f118,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f96,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f131,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f104])).

fof(f121,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f129,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1651,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1654,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1657,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5337,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_1657])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_51,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_5703,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5337,c_51])).

cnf(c_5704,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5703])).

cnf(c_5712,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1651,c_5704])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_41,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_571,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_34,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_579,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_571,c_34])).

cnf(c_1647,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1729,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2015,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1647,c_47,c_45,c_44,c_42,c_579,c_1729])).

cnf(c_5714,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5712,c_2015])).

cnf(c_48,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_6534,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5714,c_48])).

cnf(c_15,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1668,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6538,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6534,c_1668])).

cnf(c_18,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_6541,plain,
    ( r1_tarski(sK1,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6538,c_18])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3927,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK4))
    | k2_relat_1(sK4) = sK1 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3931,plain,
    ( k2_relat_1(sK4) = sK1
    | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3927])).

cnf(c_24,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1664,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1655,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3381,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2015,c_1655])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_49,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_52,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_158,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_20,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_10,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_281,plain,
    ( v2_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_20,c_10])).

cnf(c_1738,plain,
    ( v2_funct_1(sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1739,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1738])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1764,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1813,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_1814,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1861,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | ~ v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1862,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1861])).

cnf(c_988,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1933,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_1934,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1933])).

cnf(c_1936,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_3654,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3381,c_48,c_49,c_50,c_51,c_52,c_53,c_158,c_1739,c_1814,c_1862,c_1936])).

cnf(c_3658,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_3654])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3251,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1651,c_1662])).

cnf(c_3250,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_1662])).

cnf(c_27,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_27,c_12])).

cnf(c_613,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_26])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_613])).

cnf(c_1646,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_2635,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_1646])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_30,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_40,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_588,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_40])).

cnf(c_589,plain,
    ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_647,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != X1
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_589])).

cnf(c_648,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_658,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_648,c_6])).

cnf(c_662,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6541,c_3931,c_3658,c_3251,c_3250,c_2635,c_662])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.65/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/1.00  
% 3.65/1.00  ------  iProver source info
% 3.65/1.00  
% 3.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/1.00  git: non_committed_changes: false
% 3.65/1.00  git: last_make_outside_of_git: false
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options
% 3.65/1.00  
% 3.65/1.00  --out_options                           all
% 3.65/1.00  --tptp_safe_out                         true
% 3.65/1.00  --problem_path                          ""
% 3.65/1.00  --include_path                          ""
% 3.65/1.00  --clausifier                            res/vclausify_rel
% 3.65/1.00  --clausifier_options                    ""
% 3.65/1.00  --stdin                                 false
% 3.65/1.00  --stats_out                             all
% 3.65/1.00  
% 3.65/1.00  ------ General Options
% 3.65/1.00  
% 3.65/1.00  --fof                                   false
% 3.65/1.00  --time_out_real                         305.
% 3.65/1.00  --time_out_virtual                      -1.
% 3.65/1.00  --symbol_type_check                     false
% 3.65/1.00  --clausify_out                          false
% 3.65/1.00  --sig_cnt_out                           false
% 3.65/1.00  --trig_cnt_out                          false
% 3.65/1.00  --trig_cnt_out_tolerance                1.
% 3.65/1.00  --trig_cnt_out_sk_spl                   false
% 3.65/1.00  --abstr_cl_out                          false
% 3.65/1.00  
% 3.65/1.00  ------ Global Options
% 3.65/1.00  
% 3.65/1.00  --schedule                              default
% 3.65/1.00  --add_important_lit                     false
% 3.65/1.00  --prop_solver_per_cl                    1000
% 3.65/1.00  --min_unsat_core                        false
% 3.65/1.00  --soft_assumptions                      false
% 3.65/1.00  --soft_lemma_size                       3
% 3.65/1.00  --prop_impl_unit_size                   0
% 3.65/1.00  --prop_impl_unit                        []
% 3.65/1.00  --share_sel_clauses                     true
% 3.65/1.00  --reset_solvers                         false
% 3.65/1.00  --bc_imp_inh                            [conj_cone]
% 3.65/1.00  --conj_cone_tolerance                   3.
% 3.65/1.00  --extra_neg_conj                        none
% 3.65/1.00  --large_theory_mode                     true
% 3.65/1.00  --prolific_symb_bound                   200
% 3.65/1.00  --lt_threshold                          2000
% 3.65/1.00  --clause_weak_htbl                      true
% 3.65/1.00  --gc_record_bc_elim                     false
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing Options
% 3.65/1.00  
% 3.65/1.00  --preprocessing_flag                    true
% 3.65/1.00  --time_out_prep_mult                    0.1
% 3.65/1.00  --splitting_mode                        input
% 3.65/1.00  --splitting_grd                         true
% 3.65/1.00  --splitting_cvd                         false
% 3.65/1.00  --splitting_cvd_svl                     false
% 3.65/1.00  --splitting_nvd                         32
% 3.65/1.00  --sub_typing                            true
% 3.65/1.00  --prep_gs_sim                           true
% 3.65/1.00  --prep_unflatten                        true
% 3.65/1.00  --prep_res_sim                          true
% 3.65/1.00  --prep_upred                            true
% 3.65/1.00  --prep_sem_filter                       exhaustive
% 3.65/1.00  --prep_sem_filter_out                   false
% 3.65/1.00  --pred_elim                             true
% 3.65/1.00  --res_sim_input                         true
% 3.65/1.00  --eq_ax_congr_red                       true
% 3.65/1.00  --pure_diseq_elim                       true
% 3.65/1.00  --brand_transform                       false
% 3.65/1.00  --non_eq_to_eq                          false
% 3.65/1.00  --prep_def_merge                        true
% 3.65/1.00  --prep_def_merge_prop_impl              false
% 3.65/1.00  --prep_def_merge_mbd                    true
% 3.65/1.00  --prep_def_merge_tr_red                 false
% 3.65/1.00  --prep_def_merge_tr_cl                  false
% 3.65/1.00  --smt_preprocessing                     true
% 3.65/1.00  --smt_ac_axioms                         fast
% 3.65/1.00  --preprocessed_out                      false
% 3.65/1.00  --preprocessed_stats                    false
% 3.65/1.00  
% 3.65/1.00  ------ Abstraction refinement Options
% 3.65/1.00  
% 3.65/1.00  --abstr_ref                             []
% 3.65/1.00  --abstr_ref_prep                        false
% 3.65/1.00  --abstr_ref_until_sat                   false
% 3.65/1.00  --abstr_ref_sig_restrict                funpre
% 3.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.00  --abstr_ref_under                       []
% 3.65/1.00  
% 3.65/1.00  ------ SAT Options
% 3.65/1.00  
% 3.65/1.00  --sat_mode                              false
% 3.65/1.00  --sat_fm_restart_options                ""
% 3.65/1.00  --sat_gr_def                            false
% 3.65/1.00  --sat_epr_types                         true
% 3.65/1.00  --sat_non_cyclic_types                  false
% 3.65/1.00  --sat_finite_models                     false
% 3.65/1.00  --sat_fm_lemmas                         false
% 3.65/1.00  --sat_fm_prep                           false
% 3.65/1.00  --sat_fm_uc_incr                        true
% 3.65/1.00  --sat_out_model                         small
% 3.65/1.00  --sat_out_clauses                       false
% 3.65/1.00  
% 3.65/1.00  ------ QBF Options
% 3.65/1.00  
% 3.65/1.00  --qbf_mode                              false
% 3.65/1.00  --qbf_elim_univ                         false
% 3.65/1.00  --qbf_dom_inst                          none
% 3.65/1.00  --qbf_dom_pre_inst                      false
% 3.65/1.00  --qbf_sk_in                             false
% 3.65/1.00  --qbf_pred_elim                         true
% 3.65/1.00  --qbf_split                             512
% 3.65/1.00  
% 3.65/1.00  ------ BMC1 Options
% 3.65/1.00  
% 3.65/1.00  --bmc1_incremental                      false
% 3.65/1.00  --bmc1_axioms                           reachable_all
% 3.65/1.00  --bmc1_min_bound                        0
% 3.65/1.00  --bmc1_max_bound                        -1
% 3.65/1.00  --bmc1_max_bound_default                -1
% 3.65/1.00  --bmc1_symbol_reachability              true
% 3.65/1.00  --bmc1_property_lemmas                  false
% 3.65/1.00  --bmc1_k_induction                      false
% 3.65/1.00  --bmc1_non_equiv_states                 false
% 3.65/1.00  --bmc1_deadlock                         false
% 3.65/1.00  --bmc1_ucm                              false
% 3.65/1.00  --bmc1_add_unsat_core                   none
% 3.65/1.00  --bmc1_unsat_core_children              false
% 3.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.00  --bmc1_out_stat                         full
% 3.65/1.00  --bmc1_ground_init                      false
% 3.65/1.00  --bmc1_pre_inst_next_state              false
% 3.65/1.00  --bmc1_pre_inst_state                   false
% 3.65/1.00  --bmc1_pre_inst_reach_state             false
% 3.65/1.00  --bmc1_out_unsat_core                   false
% 3.65/1.00  --bmc1_aig_witness_out                  false
% 3.65/1.00  --bmc1_verbose                          false
% 3.65/1.00  --bmc1_dump_clauses_tptp                false
% 3.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.00  --bmc1_dump_file                        -
% 3.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.00  --bmc1_ucm_extend_mode                  1
% 3.65/1.00  --bmc1_ucm_init_mode                    2
% 3.65/1.00  --bmc1_ucm_cone_mode                    none
% 3.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.00  --bmc1_ucm_relax_model                  4
% 3.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.00  --bmc1_ucm_layered_model                none
% 3.65/1.00  --bmc1_ucm_max_lemma_size               10
% 3.65/1.00  
% 3.65/1.00  ------ AIG Options
% 3.65/1.00  
% 3.65/1.00  --aig_mode                              false
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation Options
% 3.65/1.00  
% 3.65/1.00  --instantiation_flag                    true
% 3.65/1.00  --inst_sos_flag                         true
% 3.65/1.00  --inst_sos_phase                        true
% 3.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel_side                     num_symb
% 3.65/1.00  --inst_solver_per_active                1400
% 3.65/1.00  --inst_solver_calls_frac                1.
% 3.65/1.00  --inst_passive_queue_type               priority_queues
% 3.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.00  --inst_passive_queues_freq              [25;2]
% 3.65/1.00  --inst_dismatching                      true
% 3.65/1.00  --inst_eager_unprocessed_to_passive     true
% 3.65/1.00  --inst_prop_sim_given                   true
% 3.65/1.00  --inst_prop_sim_new                     false
% 3.65/1.00  --inst_subs_new                         false
% 3.65/1.00  --inst_eq_res_simp                      false
% 3.65/1.00  --inst_subs_given                       false
% 3.65/1.00  --inst_orphan_elimination               true
% 3.65/1.00  --inst_learning_loop_flag               true
% 3.65/1.00  --inst_learning_start                   3000
% 3.65/1.00  --inst_learning_factor                  2
% 3.65/1.00  --inst_start_prop_sim_after_learn       3
% 3.65/1.00  --inst_sel_renew                        solver
% 3.65/1.00  --inst_lit_activity_flag                true
% 3.65/1.00  --inst_restr_to_given                   false
% 3.65/1.00  --inst_activity_threshold               500
% 3.65/1.00  --inst_out_proof                        true
% 3.65/1.00  
% 3.65/1.00  ------ Resolution Options
% 3.65/1.00  
% 3.65/1.00  --resolution_flag                       true
% 3.65/1.00  --res_lit_sel                           adaptive
% 3.65/1.00  --res_lit_sel_side                      none
% 3.65/1.00  --res_ordering                          kbo
% 3.65/1.00  --res_to_prop_solver                    active
% 3.65/1.00  --res_prop_simpl_new                    false
% 3.65/1.00  --res_prop_simpl_given                  true
% 3.65/1.00  --res_passive_queue_type                priority_queues
% 3.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.00  --res_passive_queues_freq               [15;5]
% 3.65/1.00  --res_forward_subs                      full
% 3.65/1.00  --res_backward_subs                     full
% 3.65/1.00  --res_forward_subs_resolution           true
% 3.65/1.00  --res_backward_subs_resolution          true
% 3.65/1.00  --res_orphan_elimination                true
% 3.65/1.00  --res_time_limit                        2.
% 3.65/1.00  --res_out_proof                         true
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Options
% 3.65/1.00  
% 3.65/1.00  --superposition_flag                    true
% 3.65/1.00  --sup_passive_queue_type                priority_queues
% 3.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.00  --demod_completeness_check              fast
% 3.65/1.00  --demod_use_ground                      true
% 3.65/1.00  --sup_to_prop_solver                    passive
% 3.65/1.00  --sup_prop_simpl_new                    true
% 3.65/1.00  --sup_prop_simpl_given                  true
% 3.65/1.00  --sup_fun_splitting                     true
% 3.65/1.00  --sup_smt_interval                      50000
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Simplification Setup
% 3.65/1.00  
% 3.65/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/1.00  --sup_immed_triv                        [TrivRules]
% 3.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_bw_main                     []
% 3.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_input_bw                          []
% 3.65/1.00  
% 3.65/1.00  ------ Combination Options
% 3.65/1.00  
% 3.65/1.00  --comb_res_mult                         3
% 3.65/1.00  --comb_sup_mult                         2
% 3.65/1.00  --comb_inst_mult                        10
% 3.65/1.00  
% 3.65/1.00  ------ Debug Options
% 3.65/1.00  
% 3.65/1.00  --dbg_backtrace                         false
% 3.65/1.00  --dbg_dump_prop_clauses                 false
% 3.65/1.00  --dbg_dump_prop_clauses_file            -
% 3.65/1.00  --dbg_out_stat                          false
% 3.65/1.00  ------ Parsing...
% 3.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  ------ Proving...
% 3.65/1.00  ------ Problem Properties 
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  clauses                                 40
% 3.65/1.00  conjectures                             6
% 3.65/1.00  EPR                                     12
% 3.65/1.00  Horn                                    38
% 3.65/1.00  unary                                   13
% 3.65/1.00  binary                                  12
% 3.65/1.00  lits                                    99
% 3.65/1.00  lits eq                                 13
% 3.65/1.00  fd_pure                                 0
% 3.65/1.00  fd_pseudo                               0
% 3.65/1.00  fd_cond                                 3
% 3.65/1.00  fd_pseudo_cond                          2
% 3.65/1.00  AC symbols                              0
% 3.65/1.00  
% 3.65/1.00  ------ Schedule dynamic 5 is on 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  Current options:
% 3.65/1.00  ------ 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options
% 3.65/1.00  
% 3.65/1.00  --out_options                           all
% 3.65/1.00  --tptp_safe_out                         true
% 3.65/1.00  --problem_path                          ""
% 3.65/1.00  --include_path                          ""
% 3.65/1.00  --clausifier                            res/vclausify_rel
% 3.65/1.00  --clausifier_options                    ""
% 3.65/1.00  --stdin                                 false
% 3.65/1.00  --stats_out                             all
% 3.65/1.00  
% 3.65/1.00  ------ General Options
% 3.65/1.00  
% 3.65/1.00  --fof                                   false
% 3.65/1.00  --time_out_real                         305.
% 3.65/1.00  --time_out_virtual                      -1.
% 3.65/1.00  --symbol_type_check                     false
% 3.65/1.00  --clausify_out                          false
% 3.65/1.00  --sig_cnt_out                           false
% 3.65/1.00  --trig_cnt_out                          false
% 3.65/1.00  --trig_cnt_out_tolerance                1.
% 3.65/1.00  --trig_cnt_out_sk_spl                   false
% 3.65/1.00  --abstr_cl_out                          false
% 3.65/1.00  
% 3.65/1.00  ------ Global Options
% 3.65/1.00  
% 3.65/1.00  --schedule                              default
% 3.65/1.00  --add_important_lit                     false
% 3.65/1.00  --prop_solver_per_cl                    1000
% 3.65/1.00  --min_unsat_core                        false
% 3.65/1.00  --soft_assumptions                      false
% 3.65/1.00  --soft_lemma_size                       3
% 3.65/1.00  --prop_impl_unit_size                   0
% 3.65/1.00  --prop_impl_unit                        []
% 3.65/1.00  --share_sel_clauses                     true
% 3.65/1.00  --reset_solvers                         false
% 3.65/1.00  --bc_imp_inh                            [conj_cone]
% 3.65/1.00  --conj_cone_tolerance                   3.
% 3.65/1.00  --extra_neg_conj                        none
% 3.65/1.00  --large_theory_mode                     true
% 3.65/1.00  --prolific_symb_bound                   200
% 3.65/1.00  --lt_threshold                          2000
% 3.65/1.00  --clause_weak_htbl                      true
% 3.65/1.00  --gc_record_bc_elim                     false
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing Options
% 3.65/1.00  
% 3.65/1.00  --preprocessing_flag                    true
% 3.65/1.00  --time_out_prep_mult                    0.1
% 3.65/1.00  --splitting_mode                        input
% 3.65/1.00  --splitting_grd                         true
% 3.65/1.00  --splitting_cvd                         false
% 3.65/1.00  --splitting_cvd_svl                     false
% 3.65/1.00  --splitting_nvd                         32
% 3.65/1.00  --sub_typing                            true
% 3.65/1.00  --prep_gs_sim                           true
% 3.65/1.00  --prep_unflatten                        true
% 3.65/1.00  --prep_res_sim                          true
% 3.65/1.00  --prep_upred                            true
% 3.65/1.00  --prep_sem_filter                       exhaustive
% 3.65/1.00  --prep_sem_filter_out                   false
% 3.65/1.00  --pred_elim                             true
% 3.65/1.00  --res_sim_input                         true
% 3.65/1.00  --eq_ax_congr_red                       true
% 3.65/1.00  --pure_diseq_elim                       true
% 3.65/1.00  --brand_transform                       false
% 3.65/1.00  --non_eq_to_eq                          false
% 3.65/1.00  --prep_def_merge                        true
% 3.65/1.00  --prep_def_merge_prop_impl              false
% 3.65/1.00  --prep_def_merge_mbd                    true
% 3.65/1.00  --prep_def_merge_tr_red                 false
% 3.65/1.00  --prep_def_merge_tr_cl                  false
% 3.65/1.00  --smt_preprocessing                     true
% 3.65/1.00  --smt_ac_axioms                         fast
% 3.65/1.00  --preprocessed_out                      false
% 3.65/1.00  --preprocessed_stats                    false
% 3.65/1.00  
% 3.65/1.00  ------ Abstraction refinement Options
% 3.65/1.00  
% 3.65/1.00  --abstr_ref                             []
% 3.65/1.00  --abstr_ref_prep                        false
% 3.65/1.00  --abstr_ref_until_sat                   false
% 3.65/1.00  --abstr_ref_sig_restrict                funpre
% 3.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.00  --abstr_ref_under                       []
% 3.65/1.00  
% 3.65/1.00  ------ SAT Options
% 3.65/1.00  
% 3.65/1.00  --sat_mode                              false
% 3.65/1.00  --sat_fm_restart_options                ""
% 3.65/1.00  --sat_gr_def                            false
% 3.65/1.00  --sat_epr_types                         true
% 3.65/1.00  --sat_non_cyclic_types                  false
% 3.65/1.00  --sat_finite_models                     false
% 3.65/1.00  --sat_fm_lemmas                         false
% 3.65/1.00  --sat_fm_prep                           false
% 3.65/1.00  --sat_fm_uc_incr                        true
% 3.65/1.00  --sat_out_model                         small
% 3.65/1.00  --sat_out_clauses                       false
% 3.65/1.00  
% 3.65/1.00  ------ QBF Options
% 3.65/1.00  
% 3.65/1.00  --qbf_mode                              false
% 3.65/1.00  --qbf_elim_univ                         false
% 3.65/1.00  --qbf_dom_inst                          none
% 3.65/1.00  --qbf_dom_pre_inst                      false
% 3.65/1.00  --qbf_sk_in                             false
% 3.65/1.00  --qbf_pred_elim                         true
% 3.65/1.00  --qbf_split                             512
% 3.65/1.00  
% 3.65/1.00  ------ BMC1 Options
% 3.65/1.00  
% 3.65/1.00  --bmc1_incremental                      false
% 3.65/1.00  --bmc1_axioms                           reachable_all
% 3.65/1.00  --bmc1_min_bound                        0
% 3.65/1.00  --bmc1_max_bound                        -1
% 3.65/1.00  --bmc1_max_bound_default                -1
% 3.65/1.00  --bmc1_symbol_reachability              true
% 3.65/1.00  --bmc1_property_lemmas                  false
% 3.65/1.00  --bmc1_k_induction                      false
% 3.65/1.00  --bmc1_non_equiv_states                 false
% 3.65/1.00  --bmc1_deadlock                         false
% 3.65/1.00  --bmc1_ucm                              false
% 3.65/1.00  --bmc1_add_unsat_core                   none
% 3.65/1.00  --bmc1_unsat_core_children              false
% 3.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.00  --bmc1_out_stat                         full
% 3.65/1.00  --bmc1_ground_init                      false
% 3.65/1.00  --bmc1_pre_inst_next_state              false
% 3.65/1.00  --bmc1_pre_inst_state                   false
% 3.65/1.00  --bmc1_pre_inst_reach_state             false
% 3.65/1.00  --bmc1_out_unsat_core                   false
% 3.65/1.00  --bmc1_aig_witness_out                  false
% 3.65/1.00  --bmc1_verbose                          false
% 3.65/1.00  --bmc1_dump_clauses_tptp                false
% 3.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.00  --bmc1_dump_file                        -
% 3.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.00  --bmc1_ucm_extend_mode                  1
% 3.65/1.00  --bmc1_ucm_init_mode                    2
% 3.65/1.00  --bmc1_ucm_cone_mode                    none
% 3.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.00  --bmc1_ucm_relax_model                  4
% 3.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.00  --bmc1_ucm_layered_model                none
% 3.65/1.00  --bmc1_ucm_max_lemma_size               10
% 3.65/1.00  
% 3.65/1.00  ------ AIG Options
% 3.65/1.00  
% 3.65/1.00  --aig_mode                              false
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation Options
% 3.65/1.00  
% 3.65/1.00  --instantiation_flag                    true
% 3.65/1.00  --inst_sos_flag                         true
% 3.65/1.00  --inst_sos_phase                        true
% 3.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel_side                     none
% 3.65/1.00  --inst_solver_per_active                1400
% 3.65/1.00  --inst_solver_calls_frac                1.
% 3.65/1.00  --inst_passive_queue_type               priority_queues
% 3.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.00  --inst_passive_queues_freq              [25;2]
% 3.65/1.00  --inst_dismatching                      true
% 3.65/1.00  --inst_eager_unprocessed_to_passive     true
% 3.65/1.00  --inst_prop_sim_given                   true
% 3.65/1.00  --inst_prop_sim_new                     false
% 3.65/1.00  --inst_subs_new                         false
% 3.65/1.00  --inst_eq_res_simp                      false
% 3.65/1.00  --inst_subs_given                       false
% 3.65/1.00  --inst_orphan_elimination               true
% 3.65/1.00  --inst_learning_loop_flag               true
% 3.65/1.00  --inst_learning_start                   3000
% 3.65/1.00  --inst_learning_factor                  2
% 3.65/1.00  --inst_start_prop_sim_after_learn       3
% 3.65/1.00  --inst_sel_renew                        solver
% 3.65/1.00  --inst_lit_activity_flag                true
% 3.65/1.00  --inst_restr_to_given                   false
% 3.65/1.00  --inst_activity_threshold               500
% 3.65/1.00  --inst_out_proof                        true
% 3.65/1.00  
% 3.65/1.00  ------ Resolution Options
% 3.65/1.00  
% 3.65/1.00  --resolution_flag                       false
% 3.65/1.00  --res_lit_sel                           adaptive
% 3.65/1.00  --res_lit_sel_side                      none
% 3.65/1.00  --res_ordering                          kbo
% 3.65/1.00  --res_to_prop_solver                    active
% 3.65/1.00  --res_prop_simpl_new                    false
% 3.65/1.00  --res_prop_simpl_given                  true
% 3.65/1.00  --res_passive_queue_type                priority_queues
% 3.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.00  --res_passive_queues_freq               [15;5]
% 3.65/1.00  --res_forward_subs                      full
% 3.65/1.00  --res_backward_subs                     full
% 3.65/1.00  --res_forward_subs_resolution           true
% 3.65/1.00  --res_backward_subs_resolution          true
% 3.65/1.00  --res_orphan_elimination                true
% 3.65/1.00  --res_time_limit                        2.
% 3.65/1.00  --res_out_proof                         true
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Options
% 3.65/1.00  
% 3.65/1.00  --superposition_flag                    true
% 3.65/1.00  --sup_passive_queue_type                priority_queues
% 3.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.00  --demod_completeness_check              fast
% 3.65/1.00  --demod_use_ground                      true
% 3.65/1.00  --sup_to_prop_solver                    passive
% 3.65/1.00  --sup_prop_simpl_new                    true
% 3.65/1.00  --sup_prop_simpl_given                  true
% 3.65/1.00  --sup_fun_splitting                     true
% 3.65/1.00  --sup_smt_interval                      50000
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Simplification Setup
% 3.65/1.00  
% 3.65/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/1.00  --sup_immed_triv                        [TrivRules]
% 3.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_bw_main                     []
% 3.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_input_bw                          []
% 3.65/1.00  
% 3.65/1.00  ------ Combination Options
% 3.65/1.00  
% 3.65/1.00  --comb_res_mult                         3
% 3.65/1.00  --comb_sup_mult                         2
% 3.65/1.00  --comb_inst_mult                        10
% 3.65/1.00  
% 3.65/1.00  ------ Debug Options
% 3.65/1.00  
% 3.65/1.00  --dbg_backtrace                         false
% 3.65/1.00  --dbg_dump_prop_clauses                 false
% 3.65/1.00  --dbg_dump_prop_clauses_file            -
% 3.65/1.00  --dbg_out_stat                          false
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS status Theorem for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  fof(f27,conjecture,(
% 3.65/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f28,negated_conjecture,(
% 3.65/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.65/1.00    inference(negated_conjecture,[],[f27])).
% 3.65/1.00  
% 3.65/1.00  fof(f61,plain,(
% 3.65/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.65/1.00    inference(ennf_transformation,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  fof(f62,plain,(
% 3.65/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.65/1.00    inference(flattening,[],[f61])).
% 3.65/1.00  
% 3.65/1.00  fof(f71,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f70,plain,(
% 3.65/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f72,plain,(
% 3.65/1.00    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f62,f71,f70])).
% 3.65/1.00  
% 3.65/1.00  fof(f116,plain,(
% 3.65/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.65/1.00    inference(cnf_transformation,[],[f72])).
% 3.65/1.00  
% 3.65/1.00  fof(f119,plain,(
% 3.65/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.65/1.00    inference(cnf_transformation,[],[f72])).
% 3.65/1.00  
% 3.65/1.00  fof(f24,axiom,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f57,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.65/1.00    inference(ennf_transformation,[],[f24])).
% 3.65/1.00  
% 3.65/1.00  fof(f58,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.65/1.00    inference(flattening,[],[f57])).
% 3.65/1.00  
% 3.65/1.00  fof(f110,plain,(
% 3.65/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f58])).
% 3.65/1.00  
% 3.65/1.00  fof(f117,plain,(
% 3.65/1.00    v1_funct_1(sK4)),
% 3.65/1.00    inference(cnf_transformation,[],[f72])).
% 3.65/1.00  
% 3.65/1.00  fof(f19,axiom,(
% 3.65/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f50,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.65/1.00    inference(ennf_transformation,[],[f19])).
% 3.65/1.00  
% 3.65/1.00  fof(f51,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(flattening,[],[f50])).
% 3.65/1.00  
% 3.65/1.00  fof(f68,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(nnf_transformation,[],[f51])).
% 3.65/1.00  
% 3.65/1.00  fof(f101,plain,(
% 3.65/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f68])).
% 3.65/1.00  
% 3.65/1.00  fof(f120,plain,(
% 3.65/1.00    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 3.65/1.00    inference(cnf_transformation,[],[f72])).
% 3.65/1.00  
% 3.65/1.00  fof(f22,axiom,(
% 3.65/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f30,plain,(
% 3.65/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.65/1.00    inference(pure_predicate_removal,[],[f22])).
% 3.65/1.00  
% 3.65/1.00  fof(f107,plain,(
% 3.65/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f30])).
% 3.65/1.00  
% 3.65/1.00  fof(f114,plain,(
% 3.65/1.00    v1_funct_1(sK3)),
% 3.65/1.00    inference(cnf_transformation,[],[f72])).
% 3.65/1.00  
% 3.65/1.00  fof(f21,axiom,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f54,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.65/1.00    inference(ennf_transformation,[],[f21])).
% 3.65/1.00  
% 3.65/1.00  fof(f55,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.65/1.00    inference(flattening,[],[f54])).
% 3.65/1.00  
% 3.65/1.00  fof(f106,plain,(
% 3.65/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f55])).
% 3.65/1.00  
% 3.65/1.00  fof(f11,axiom,(
% 3.65/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f42,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f11])).
% 3.65/1.00  
% 3.65/1.00  fof(f88,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f42])).
% 3.65/1.00  
% 3.65/1.00  fof(f13,axiom,(
% 3.65/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f92,plain,(
% 3.65/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.65/1.00    inference(cnf_transformation,[],[f13])).
% 3.65/1.00  
% 3.65/1.00  fof(f25,axiom,(
% 3.65/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f111,plain,(
% 3.65/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f25])).
% 3.65/1.00  
% 3.65/1.00  fof(f122,plain,(
% 3.65/1.00    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.65/1.00    inference(definition_unfolding,[],[f92,f111])).
% 3.65/1.00  
% 3.65/1.00  fof(f4,axiom,(
% 3.65/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f65,plain,(
% 3.65/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.65/1.00    inference(nnf_transformation,[],[f4])).
% 3.65/1.00  
% 3.65/1.00  fof(f66,plain,(
% 3.65/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.65/1.00    inference(flattening,[],[f65])).
% 3.65/1.00  
% 3.65/1.00  fof(f79,plain,(
% 3.65/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f66])).
% 3.65/1.00  
% 3.65/1.00  fof(f16,axiom,(
% 3.65/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f98,plain,(
% 3.65/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f16])).
% 3.65/1.00  
% 3.65/1.00  fof(f124,plain,(
% 3.65/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.65/1.00    inference(definition_unfolding,[],[f98,f111])).
% 3.65/1.00  
% 3.65/1.00  fof(f26,axiom,(
% 3.65/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f59,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.65/1.00    inference(ennf_transformation,[],[f26])).
% 3.65/1.00  
% 3.65/1.00  fof(f60,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.65/1.00    inference(flattening,[],[f59])).
% 3.65/1.00  
% 3.65/1.00  fof(f112,plain,(
% 3.65/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f60])).
% 3.65/1.00  
% 3.65/1.00  fof(f115,plain,(
% 3.65/1.00    v1_funct_2(sK3,sK1,sK2)),
% 3.65/1.00    inference(cnf_transformation,[],[f72])).
% 3.65/1.00  
% 3.65/1.00  fof(f118,plain,(
% 3.65/1.00    v1_funct_2(sK4,sK2,sK1)),
% 3.65/1.00    inference(cnf_transformation,[],[f72])).
% 3.65/1.00  
% 3.65/1.00  fof(f2,axiom,(
% 3.65/1.00    v1_xboole_0(k1_xboole_0)),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f74,plain,(
% 3.65/1.00    v1_xboole_0(k1_xboole_0)),
% 3.65/1.00    inference(cnf_transformation,[],[f2])).
% 3.65/1.00  
% 3.65/1.00  fof(f15,axiom,(
% 3.65/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f46,plain,(
% 3.65/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 3.65/1.00    inference(ennf_transformation,[],[f15])).
% 3.65/1.00  
% 3.65/1.00  fof(f47,plain,(
% 3.65/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.65/1.00    inference(flattening,[],[f46])).
% 3.65/1.00  
% 3.65/1.00  fof(f96,plain,(
% 3.65/1.00    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f47])).
% 3.65/1.00  
% 3.65/1.00  fof(f14,axiom,(
% 3.65/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f45,plain,(
% 3.65/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f14])).
% 3.65/1.00  
% 3.65/1.00  fof(f93,plain,(
% 3.65/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f45])).
% 3.65/1.00  
% 3.65/1.00  fof(f8,axiom,(
% 3.65/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f38,plain,(
% 3.65/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f8])).
% 3.65/1.00  
% 3.65/1.00  fof(f83,plain,(
% 3.65/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f38])).
% 3.65/1.00  
% 3.65/1.00  fof(f7,axiom,(
% 3.65/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f37,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f7])).
% 3.65/1.00  
% 3.65/1.00  fof(f82,plain,(
% 3.65/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f37])).
% 3.65/1.00  
% 3.65/1.00  fof(f6,axiom,(
% 3.65/1.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f36,plain,(
% 3.65/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f6])).
% 3.65/1.00  
% 3.65/1.00  fof(f81,plain,(
% 3.65/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f36])).
% 3.65/1.00  
% 3.65/1.00  fof(f17,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f48,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(ennf_transformation,[],[f17])).
% 3.65/1.00  
% 3.65/1.00  fof(f99,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f48])).
% 3.65/1.00  
% 3.65/1.00  fof(f18,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f31,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.65/1.00    inference(pure_predicate_removal,[],[f18])).
% 3.65/1.00  
% 3.65/1.00  fof(f49,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(ennf_transformation,[],[f31])).
% 3.65/1.00  
% 3.65/1.00  fof(f100,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f49])).
% 3.65/1.00  
% 3.65/1.00  fof(f9,axiom,(
% 3.65/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f39,plain,(
% 3.65/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(ennf_transformation,[],[f9])).
% 3.65/1.00  
% 3.65/1.00  fof(f67,plain,(
% 3.65/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(nnf_transformation,[],[f39])).
% 3.65/1.00  
% 3.65/1.00  fof(f84,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f67])).
% 3.65/1.00  
% 3.65/1.00  fof(f85,plain,(
% 3.65/1.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f67])).
% 3.65/1.00  
% 3.65/1.00  fof(f20,axiom,(
% 3.65/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f52,plain,(
% 3.65/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f20])).
% 3.65/1.00  
% 3.65/1.00  fof(f53,plain,(
% 3.65/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(flattening,[],[f52])).
% 3.65/1.00  
% 3.65/1.00  fof(f69,plain,(
% 3.65/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(nnf_transformation,[],[f53])).
% 3.65/1.00  
% 3.65/1.00  fof(f104,plain,(
% 3.65/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f69])).
% 3.65/1.00  
% 3.65/1.00  fof(f131,plain,(
% 3.65/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.65/1.00    inference(equality_resolution,[],[f104])).
% 3.65/1.00  
% 3.65/1.00  fof(f121,plain,(
% 3.65/1.00    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 3.65/1.00    inference(cnf_transformation,[],[f72])).
% 3.65/1.00  
% 3.65/1.00  fof(f77,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.65/1.00    inference(cnf_transformation,[],[f66])).
% 3.65/1.00  
% 3.65/1.00  fof(f129,plain,(
% 3.65/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.65/1.00    inference(equality_resolution,[],[f77])).
% 3.65/1.00  
% 3.65/1.00  cnf(c_45,negated_conjecture,
% 3.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1651,plain,
% 3.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_42,negated_conjecture,
% 3.65/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1654,plain,
% 3.65/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_37,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v1_funct_1(X3)
% 3.65/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1657,plain,
% 3.65/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.65/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.65/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X5) != iProver_top
% 3.65/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5337,plain,
% 3.65/1.00      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X2) != iProver_top
% 3.65/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1654,c_1657]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_44,negated_conjecture,
% 3.65/1.00      ( v1_funct_1(sK4) ),
% 3.65/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_51,plain,
% 3.65/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5703,plain,
% 3.65/1.00      ( v1_funct_1(X2) != iProver_top
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_5337,c_51]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5704,plain,
% 3.65/1.00      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_5703]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5712,plain,
% 3.65/1.00      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.65/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1651,c_5704]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_29,plain,
% 3.65/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.65/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.65/1.00      | X3 = X2 ),
% 3.65/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_41,negated_conjecture,
% 3.65/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_570,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | X3 = X0
% 3.65/1.00      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 3.65/1.00      | k6_partfun1(sK1) != X3
% 3.65/1.00      | sK1 != X2
% 3.65/1.00      | sK1 != X1 ),
% 3.65/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_571,plain,
% 3.65/1.00      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.65/1.00      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.65/1.00      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.65/1.00      inference(unflattening,[status(thm)],[c_570]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_34,plain,
% 3.65/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_579,plain,
% 3.65/1.00      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.65/1.00      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.65/1.00      inference(forward_subsumption_resolution,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_571,c_34]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1647,plain,
% 3.65/1.00      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.65/1.00      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_47,negated_conjecture,
% 3.65/1.00      ( v1_funct_1(sK3) ),
% 3.65/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_32,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.65/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v1_funct_1(X3) ),
% 3.65/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1729,plain,
% 3.65/1.00      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.65/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.65/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.65/1.00      | ~ v1_funct_1(sK3)
% 3.65/1.00      | ~ v1_funct_1(sK4) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2015,plain,
% 3.65/1.00      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_1647,c_47,c_45,c_44,c_42,c_579,c_1729]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5714,plain,
% 3.65/1.00      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 3.65/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_5712,c_2015]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_48,plain,
% 3.65/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6534,plain,
% 3.65/1.00      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_5714,c_48]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_15,plain,
% 3.65/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.65/1.00      | ~ v1_relat_1(X1)
% 3.65/1.00      | ~ v1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1668,plain,
% 3.65/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.65/1.00      | v1_relat_1(X0) != iProver_top
% 3.65/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6538,plain,
% 3.65/1.00      ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK4)) = iProver_top
% 3.65/1.00      | v1_relat_1(sK3) != iProver_top
% 3.65/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_6534,c_1668]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_18,plain,
% 3.65/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f122]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6541,plain,
% 3.65/1.00      ( r1_tarski(sK1,k2_relat_1(sK4)) = iProver_top
% 3.65/1.00      | v1_relat_1(sK3) != iProver_top
% 3.65/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_6538,c_18]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4,plain,
% 3.65/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3927,plain,
% 3.65/1.00      ( ~ r1_tarski(k2_relat_1(sK4),sK1)
% 3.65/1.00      | ~ r1_tarski(sK1,k2_relat_1(sK4))
% 3.65/1.00      | k2_relat_1(sK4) = sK1 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3931,plain,
% 3.65/1.00      ( k2_relat_1(sK4) = sK1
% 3.65/1.00      | r1_tarski(k2_relat_1(sK4),sK1) != iProver_top
% 3.65/1.00      | r1_tarski(sK1,k2_relat_1(sK4)) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_3927]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_24,plain,
% 3.65/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f124]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1664,plain,
% 3.65/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_39,plain,
% 3.65/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.65/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | v2_funct_1(X3)
% 3.65/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v1_funct_1(X3)
% 3.65/1.00      | k1_xboole_0 = X2 ),
% 3.65/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1655,plain,
% 3.65/1.00      ( k1_xboole_0 = X0
% 3.65/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.65/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.65/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.65/1.00      | v2_funct_1(X3) = iProver_top
% 3.65/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
% 3.65/1.00      | v1_funct_1(X1) != iProver_top
% 3.65/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3381,plain,
% 3.65/1.00      ( sK1 = k1_xboole_0
% 3.65/1.00      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.65/1.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.65/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.65/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.65/1.00      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.65/1.00      | v2_funct_1(sK3) = iProver_top
% 3.65/1.00      | v1_funct_1(sK3) != iProver_top
% 3.65/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_2015,c_1655]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_46,negated_conjecture,
% 3.65/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.65/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_49,plain,
% 3.65/1.00      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_50,plain,
% 3.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_43,negated_conjecture,
% 3.65/1.00      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_52,plain,
% 3.65/1.00      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_53,plain,
% 3.65/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1,plain,
% 3.65/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_158,plain,
% 3.65/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_21,plain,
% 3.65/1.00      ( v2_funct_1(X0)
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v1_relat_1(X0)
% 3.65/1.00      | ~ v1_xboole_0(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_20,plain,
% 3.65/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_10,plain,
% 3.65/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_281,plain,
% 3.65/1.00      ( v2_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_21,c_20,c_10]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1738,plain,
% 3.65/1.00      ( v2_funct_1(sK3) | ~ v1_xboole_0(sK3) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_281]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1739,plain,
% 3.65/1.00      ( v2_funct_1(sK3) = iProver_top | v1_xboole_0(sK3) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1738]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/1.00      | ~ v1_xboole_0(X1)
% 3.65/1.00      | v1_xboole_0(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1764,plain,
% 3.65/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.65/1.00      | ~ v1_xboole_0(X0)
% 3.65/1.00      | v1_xboole_0(sK3) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1813,plain,
% 3.65/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.65/1.00      | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
% 3.65/1.00      | v1_xboole_0(sK3) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1764]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1814,plain,
% 3.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.65/1.00      | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.65/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8,plain,
% 3.65/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1861,plain,
% 3.65/1.00      ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | ~ v1_xboole_0(sK1) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1862,plain,
% 3.65/1.00      ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) = iProver_top
% 3.65/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1861]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_988,plain,
% 3.65/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.65/1.00      theory(equality) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1933,plain,
% 3.65/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_988]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1934,plain,
% 3.65/1.00      ( sK1 != X0
% 3.65/1.00      | v1_xboole_0(X0) != iProver_top
% 3.65/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1933]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1936,plain,
% 3.65/1.00      ( sK1 != k1_xboole_0
% 3.65/1.00      | v1_xboole_0(sK1) = iProver_top
% 3.65/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1934]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3654,plain,
% 3.65/1.00      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.65/1.00      | v2_funct_1(sK3) = iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_3381,c_48,c_49,c_50,c_51,c_52,c_53,c_158,c_1739,
% 3.65/1.00                 c_1814,c_1862,c_1936]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3658,plain,
% 3.65/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1664,c_3654]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_26,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | v1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1662,plain,
% 3.65/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.65/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3251,plain,
% 3.65/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1651,c_1662]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3250,plain,
% 3.65/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1654,c_1662]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_27,plain,
% 3.65/1.00      ( v5_relat_1(X0,X1)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_12,plain,
% 3.65/1.00      ( ~ v5_relat_1(X0,X1)
% 3.65/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.65/1.00      | ~ v1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_609,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.65/1.00      | ~ v1_relat_1(X0) ),
% 3.65/1.00      inference(resolution,[status(thm)],[c_27,c_12]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_613,plain,
% 3.65/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_609,c_26]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_614,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_613]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1646,plain,
% 3.65/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.65/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2635,plain,
% 3.65/1.00      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1654,c_1646]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11,plain,
% 3.65/1.00      ( v5_relat_1(X0,X1)
% 3.65/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.65/1.00      | ~ v1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_30,plain,
% 3.65/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.65/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.65/1.00      | ~ v1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f131]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_40,negated_conjecture,
% 3.65/1.00      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 3.65/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_588,plain,
% 3.65/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.65/1.00      | ~ v2_funct_1(sK3)
% 3.65/1.00      | ~ v1_relat_1(X0)
% 3.65/1.00      | k2_relat_1(X0) != sK1
% 3.65/1.00      | sK4 != X0 ),
% 3.65/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_40]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_589,plain,
% 3.65/1.00      ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
% 3.65/1.00      | ~ v2_funct_1(sK3)
% 3.65/1.00      | ~ v1_relat_1(sK4)
% 3.65/1.00      | k2_relat_1(sK4) != sK1 ),
% 3.65/1.00      inference(unflattening,[status(thm)],[c_588]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_647,plain,
% 3.65/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.65/1.00      | ~ v2_funct_1(sK3)
% 3.65/1.00      | ~ v1_relat_1(X0)
% 3.65/1.00      | ~ v1_relat_1(sK4)
% 3.65/1.00      | k2_relat_1(sK4) != X1
% 3.65/1.00      | k2_relat_1(sK4) != sK1
% 3.65/1.00      | sK4 != X0 ),
% 3.65/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_589]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_648,plain,
% 3.65/1.00      ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
% 3.65/1.00      | ~ v2_funct_1(sK3)
% 3.65/1.00      | ~ v1_relat_1(sK4)
% 3.65/1.00      | k2_relat_1(sK4) != sK1 ),
% 3.65/1.00      inference(unflattening,[status(thm)],[c_647]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6,plain,
% 3.65/1.00      ( r1_tarski(X0,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f129]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_658,plain,
% 3.65/1.00      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK4) | k2_relat_1(sK4) != sK1 ),
% 3.65/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_648,c_6]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_662,plain,
% 3.65/1.00      ( k2_relat_1(sK4) != sK1
% 3.65/1.00      | v2_funct_1(sK3) != iProver_top
% 3.65/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(contradiction,plain,
% 3.65/1.00      ( $false ),
% 3.65/1.00      inference(minisat,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_6541,c_3931,c_3658,c_3251,c_3250,c_2635,c_662]) ).
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  ------                               Statistics
% 3.65/1.00  
% 3.65/1.00  ------ General
% 3.65/1.00  
% 3.65/1.00  abstr_ref_over_cycles:                  0
% 3.65/1.00  abstr_ref_under_cycles:                 0
% 3.65/1.00  gc_basic_clause_elim:                   0
% 3.65/1.00  forced_gc_time:                         0
% 3.65/1.00  parsing_time:                           0.021
% 3.65/1.00  unif_index_cands_time:                  0.
% 3.65/1.00  unif_index_add_time:                    0.
% 3.65/1.00  orderings_time:                         0.
% 3.65/1.00  out_proof_time:                         0.013
% 3.65/1.00  total_time:                             0.208
% 3.65/1.00  num_of_symbols:                         57
% 3.65/1.00  num_of_terms:                           6484
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing
% 3.65/1.00  
% 3.65/1.00  num_of_splits:                          1
% 3.65/1.00  num_of_split_atoms:                     1
% 3.65/1.00  num_of_reused_defs:                     0
% 3.65/1.00  num_eq_ax_congr_red:                    22
% 3.65/1.00  num_of_sem_filtered_clauses:            1
% 3.65/1.00  num_of_subtypes:                        0
% 3.65/1.00  monotx_restored_types:                  0
% 3.65/1.00  sat_num_of_epr_types:                   0
% 3.65/1.00  sat_num_of_non_cyclic_types:            0
% 3.65/1.00  sat_guarded_non_collapsed_types:        0
% 3.65/1.00  num_pure_diseq_elim:                    0
% 3.65/1.00  simp_replaced_by:                       0
% 3.65/1.00  res_preprocessed:                       196
% 3.65/1.00  prep_upred:                             0
% 3.65/1.00  prep_unflattend:                        21
% 3.65/1.00  smt_new_axioms:                         0
% 3.65/1.00  pred_elim_cands:                        9
% 3.65/1.00  pred_elim:                              3
% 3.65/1.00  pred_elim_cl:                           5
% 3.65/1.00  pred_elim_cycles:                       8
% 3.65/1.00  merged_defs:                            0
% 3.65/1.00  merged_defs_ncl:                        0
% 3.65/1.00  bin_hyper_res:                          0
% 3.65/1.00  prep_cycles:                            4
% 3.65/1.00  pred_elim_time:                         0.005
% 3.65/1.00  splitting_time:                         0.
% 3.65/1.00  sem_filter_time:                        0.
% 3.65/1.00  monotx_time:                            0.001
% 3.65/1.00  subtype_inf_time:                       0.
% 3.65/1.00  
% 3.65/1.00  ------ Problem properties
% 3.65/1.00  
% 3.65/1.00  clauses:                                40
% 3.65/1.00  conjectures:                            6
% 3.65/1.00  epr:                                    12
% 3.65/1.00  horn:                                   38
% 3.65/1.00  ground:                                 10
% 3.65/1.00  unary:                                  13
% 3.65/1.00  binary:                                 12
% 3.65/1.00  lits:                                   99
% 3.65/1.00  lits_eq:                                13
% 3.65/1.00  fd_pure:                                0
% 3.65/1.00  fd_pseudo:                              0
% 3.65/1.00  fd_cond:                                3
% 3.65/1.00  fd_pseudo_cond:                         2
% 3.65/1.00  ac_symbols:                             0
% 3.65/1.00  
% 3.65/1.00  ------ Propositional Solver
% 3.65/1.00  
% 3.65/1.00  prop_solver_calls:                      33
% 3.65/1.00  prop_fast_solver_calls:                 1275
% 3.65/1.00  smt_solver_calls:                       0
% 3.65/1.00  smt_fast_solver_calls:                  0
% 3.65/1.00  prop_num_of_clauses:                    2705
% 3.65/1.00  prop_preprocess_simplified:             8997
% 3.65/1.00  prop_fo_subsumed:                       26
% 3.65/1.00  prop_solver_time:                       0.
% 3.65/1.00  smt_solver_time:                        0.
% 3.65/1.00  smt_fast_solver_time:                   0.
% 3.65/1.00  prop_fast_solver_time:                  0.
% 3.65/1.00  prop_unsat_core_time:                   0.
% 3.65/1.00  
% 3.65/1.00  ------ QBF
% 3.65/1.00  
% 3.65/1.00  qbf_q_res:                              0
% 3.65/1.00  qbf_num_tautologies:                    0
% 3.65/1.00  qbf_prep_cycles:                        0
% 3.65/1.00  
% 3.65/1.00  ------ BMC1
% 3.65/1.00  
% 3.65/1.00  bmc1_current_bound:                     -1
% 3.65/1.00  bmc1_last_solved_bound:                 -1
% 3.65/1.00  bmc1_unsat_core_size:                   -1
% 3.65/1.00  bmc1_unsat_core_parents_size:           -1
% 3.65/1.00  bmc1_merge_next_fun:                    0
% 3.65/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation
% 3.65/1.00  
% 3.65/1.00  inst_num_of_clauses:                    812
% 3.65/1.00  inst_num_in_passive:                    416
% 3.65/1.00  inst_num_in_active:                     386
% 3.65/1.00  inst_num_in_unprocessed:                11
% 3.65/1.00  inst_num_of_loops:                      420
% 3.65/1.00  inst_num_of_learning_restarts:          0
% 3.65/1.00  inst_num_moves_active_passive:          29
% 3.65/1.00  inst_lit_activity:                      0
% 3.65/1.00  inst_lit_activity_moves:                0
% 3.65/1.00  inst_num_tautologies:                   0
% 3.65/1.00  inst_num_prop_implied:                  0
% 3.65/1.00  inst_num_existing_simplified:           0
% 3.65/1.00  inst_num_eq_res_simplified:             0
% 3.65/1.00  inst_num_child_elim:                    0
% 3.65/1.00  inst_num_of_dismatching_blockings:      256
% 3.65/1.00  inst_num_of_non_proper_insts:           964
% 3.65/1.00  inst_num_of_duplicates:                 0
% 3.65/1.00  inst_inst_num_from_inst_to_res:         0
% 3.65/1.00  inst_dismatching_checking_time:         0.
% 3.65/1.00  
% 3.65/1.00  ------ Resolution
% 3.65/1.00  
% 3.65/1.00  res_num_of_clauses:                     0
% 3.65/1.00  res_num_in_passive:                     0
% 3.65/1.00  res_num_in_active:                      0
% 3.65/1.00  res_num_of_loops:                       200
% 3.65/1.00  res_forward_subset_subsumed:            93
% 3.65/1.00  res_backward_subset_subsumed:           2
% 3.65/1.00  res_forward_subsumed:                   0
% 3.65/1.00  res_backward_subsumed:                  0
% 3.65/1.00  res_forward_subsumption_resolution:     3
% 3.65/1.00  res_backward_subsumption_resolution:    0
% 3.65/1.00  res_clause_to_clause_subsumption:       204
% 3.65/1.00  res_orphan_elimination:                 0
% 3.65/1.00  res_tautology_del:                      101
% 3.65/1.00  res_num_eq_res_simplified:              0
% 3.65/1.00  res_num_sel_changes:                    0
% 3.65/1.00  res_moves_from_active_to_pass:          0
% 3.65/1.00  
% 3.65/1.00  ------ Superposition
% 3.65/1.00  
% 3.65/1.00  sup_time_total:                         0.
% 3.65/1.00  sup_time_generating:                    0.
% 3.65/1.00  sup_time_sim_full:                      0.
% 3.65/1.00  sup_time_sim_immed:                     0.
% 3.65/1.00  
% 3.65/1.00  sup_num_of_clauses:                     110
% 3.65/1.00  sup_num_in_active:                      82
% 3.65/1.00  sup_num_in_passive:                     28
% 3.65/1.00  sup_num_of_loops:                       82
% 3.65/1.00  sup_fw_superposition:                   49
% 3.65/1.00  sup_bw_superposition:                   45
% 3.65/1.00  sup_immediate_simplified:               14
% 3.65/1.00  sup_given_eliminated:                   0
% 3.65/1.00  comparisons_done:                       0
% 3.65/1.00  comparisons_avoided:                    0
% 3.65/1.00  
% 3.65/1.00  ------ Simplifications
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  sim_fw_subset_subsumed:                 6
% 3.65/1.00  sim_bw_subset_subsumed:                 0
% 3.65/1.00  sim_fw_subsumed:                        4
% 3.65/1.00  sim_bw_subsumed:                        1
% 3.65/1.00  sim_fw_subsumption_res:                 0
% 3.65/1.00  sim_bw_subsumption_res:                 0
% 3.65/1.00  sim_tautology_del:                      3
% 3.65/1.00  sim_eq_tautology_del:                   3
% 3.65/1.00  sim_eq_res_simp:                        0
% 3.65/1.00  sim_fw_demodulated:                     1
% 3.65/1.00  sim_bw_demodulated:                     0
% 3.65/1.00  sim_light_normalised:                   4
% 3.65/1.00  sim_joinable_taut:                      0
% 3.65/1.00  sim_joinable_simp:                      0
% 3.65/1.00  sim_ac_normalised:                      0
% 3.65/1.00  sim_smt_subsumption:                    0
% 3.65/1.00  
%------------------------------------------------------------------------------
