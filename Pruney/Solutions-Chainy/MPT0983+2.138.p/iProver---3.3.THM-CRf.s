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
% DateTime   : Thu Dec  3 12:02:14 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 462 expanded)
%              Number of clauses        :  106 ( 156 expanded)
%              Number of leaves         :   26 ( 112 expanded)
%              Depth                    :   17
%              Number of atoms          :  593 (2598 expanded)
%              Number of equality atoms :  212 ( 271 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
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

fof(f27,negated_conjecture,(
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
    inference(negated_conjecture,[],[f26])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK5,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK5,X1,X0)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
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
          ( ( ~ v2_funct_2(X3,sK2)
            | ~ v2_funct_1(sK4) )
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
          & v1_funct_2(X3,sK3,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ( ~ v2_funct_2(sK5,sK2)
      | ~ v2_funct_1(sK4) )
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f53,f66,f65])).

fof(f110,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f67])).

fof(f113,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f67])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f111,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f114,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f67])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f116,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f86,f105])).

fof(f25,axiom,(
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

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f106,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f109,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f112,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f93,f105])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f125,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f100])).

fof(f115,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1436,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1439,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1442,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7483,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1442])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_50,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_9081,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7483,c_50])).

cnf(c_9082,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9081])).

cnf(c_9094,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_9082])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1445,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_40,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
    | k6_partfun1(sK2) != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_40])).

cnf(c_470,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_35,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_478,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_470,c_35])).

cnf(c_1433,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_4984,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1433])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_47,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_49,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_52,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5360,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4984,c_47,c_49,c_50,c_52])).

cnf(c_9111,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9094,c_5360])).

cnf(c_9367,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9111,c_47])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1455,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9370,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9367,c_1455])).

cnf(c_17,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_9371,plain,
    ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9370,c_17])).

cnf(c_798,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3214,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_6609,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3214])).

cnf(c_6610,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_6609])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1440,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5367,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_1440])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_48,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_51,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5499,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5367,c_47,c_48,c_49,c_50,c_51,c_52])).

cnf(c_24,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1449,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5506,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5499,c_1449])).

cnf(c_799,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5429,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_5431,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5429])).

cnf(c_809,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4615,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_4616,plain,
    ( sK4 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4615])).

cnf(c_4618,plain,
    ( sK4 != k1_xboole_0
    | v2_funct_1(sK4) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4616])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1447,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4462,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_1447])).

cnf(c_4474,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4462])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1458,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3639,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_1458])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1456,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4325,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3639,c_1456])).

cnf(c_3638,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1458])).

cnf(c_3959,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3638,c_1456])).

cnf(c_1443,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3658,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_1446])).

cnf(c_3682,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3658])).

cnf(c_26,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_26,c_13])).

cnf(c_1432,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_2837,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1432])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1463,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3491,plain,
    ( k2_relat_1(sK5) = sK2
    | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2837,c_1463])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2219,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0))
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2223,plain,
    ( k1_xboole_0 = k6_partfun1(X0)
    | v1_xboole_0(k6_partfun1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2219])).

cnf(c_2225,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | v1_xboole_0(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_797,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2036,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_1966,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1777,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1778,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1777])).

cnf(c_1780,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_31,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_39,negated_conjecture,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_487,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_39])).

cnf(c_488,plain,
    ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_541,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != X1
    | k2_relat_1(sK5) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_488])).

cnf(c_542,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_552,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_542,c_3])).

cnf(c_553,plain,
    ( k2_relat_1(sK5) != sK2
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_150,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_93,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_95,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9371,c_6610,c_5506,c_5431,c_4618,c_4474,c_4325,c_3959,c_3682,c_3491,c_2225,c_2036,c_1966,c_1780,c_553,c_150,c_0,c_95])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.31/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.03  
% 3.31/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/1.03  
% 3.31/1.03  ------  iProver source info
% 3.31/1.03  
% 3.31/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.31/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/1.03  git: non_committed_changes: false
% 3.31/1.03  git: last_make_outside_of_git: false
% 3.31/1.03  
% 3.31/1.03  ------ 
% 3.31/1.03  
% 3.31/1.03  ------ Input Options
% 3.31/1.03  
% 3.31/1.03  --out_options                           all
% 3.31/1.03  --tptp_safe_out                         true
% 3.31/1.03  --problem_path                          ""
% 3.31/1.03  --include_path                          ""
% 3.31/1.03  --clausifier                            res/vclausify_rel
% 3.31/1.03  --clausifier_options                    --mode clausify
% 3.31/1.03  --stdin                                 false
% 3.31/1.03  --stats_out                             all
% 3.31/1.03  
% 3.31/1.03  ------ General Options
% 3.31/1.03  
% 3.31/1.03  --fof                                   false
% 3.31/1.03  --time_out_real                         305.
% 3.31/1.03  --time_out_virtual                      -1.
% 3.31/1.03  --symbol_type_check                     false
% 3.31/1.03  --clausify_out                          false
% 3.31/1.03  --sig_cnt_out                           false
% 3.31/1.03  --trig_cnt_out                          false
% 3.31/1.03  --trig_cnt_out_tolerance                1.
% 3.31/1.03  --trig_cnt_out_sk_spl                   false
% 3.31/1.03  --abstr_cl_out                          false
% 3.31/1.03  
% 3.31/1.03  ------ Global Options
% 3.31/1.03  
% 3.31/1.03  --schedule                              default
% 3.31/1.03  --add_important_lit                     false
% 3.31/1.03  --prop_solver_per_cl                    1000
% 3.31/1.03  --min_unsat_core                        false
% 3.31/1.03  --soft_assumptions                      false
% 3.31/1.03  --soft_lemma_size                       3
% 3.31/1.03  --prop_impl_unit_size                   0
% 3.31/1.03  --prop_impl_unit                        []
% 3.31/1.03  --share_sel_clauses                     true
% 3.31/1.03  --reset_solvers                         false
% 3.31/1.03  --bc_imp_inh                            [conj_cone]
% 3.31/1.03  --conj_cone_tolerance                   3.
% 3.31/1.03  --extra_neg_conj                        none
% 3.31/1.03  --large_theory_mode                     true
% 3.31/1.03  --prolific_symb_bound                   200
% 3.31/1.03  --lt_threshold                          2000
% 3.31/1.03  --clause_weak_htbl                      true
% 3.31/1.03  --gc_record_bc_elim                     false
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing Options
% 3.31/1.03  
% 3.31/1.03  --preprocessing_flag                    true
% 3.31/1.03  --time_out_prep_mult                    0.1
% 3.31/1.03  --splitting_mode                        input
% 3.31/1.03  --splitting_grd                         true
% 3.31/1.03  --splitting_cvd                         false
% 3.31/1.03  --splitting_cvd_svl                     false
% 3.31/1.03  --splitting_nvd                         32
% 3.31/1.03  --sub_typing                            true
% 3.31/1.03  --prep_gs_sim                           true
% 3.31/1.03  --prep_unflatten                        true
% 3.31/1.03  --prep_res_sim                          true
% 3.31/1.03  --prep_upred                            true
% 3.31/1.03  --prep_sem_filter                       exhaustive
% 3.31/1.03  --prep_sem_filter_out                   false
% 3.31/1.03  --pred_elim                             true
% 3.31/1.03  --res_sim_input                         true
% 3.31/1.03  --eq_ax_congr_red                       true
% 3.31/1.03  --pure_diseq_elim                       true
% 3.31/1.03  --brand_transform                       false
% 3.31/1.03  --non_eq_to_eq                          false
% 3.31/1.03  --prep_def_merge                        true
% 3.31/1.03  --prep_def_merge_prop_impl              false
% 3.31/1.03  --prep_def_merge_mbd                    true
% 3.31/1.03  --prep_def_merge_tr_red                 false
% 3.31/1.03  --prep_def_merge_tr_cl                  false
% 3.31/1.03  --smt_preprocessing                     true
% 3.31/1.03  --smt_ac_axioms                         fast
% 3.31/1.03  --preprocessed_out                      false
% 3.31/1.03  --preprocessed_stats                    false
% 3.31/1.03  
% 3.31/1.03  ------ Abstraction refinement Options
% 3.31/1.03  
% 3.31/1.03  --abstr_ref                             []
% 3.31/1.03  --abstr_ref_prep                        false
% 3.31/1.03  --abstr_ref_until_sat                   false
% 3.31/1.03  --abstr_ref_sig_restrict                funpre
% 3.31/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.03  --abstr_ref_under                       []
% 3.31/1.03  
% 3.31/1.03  ------ SAT Options
% 3.31/1.03  
% 3.31/1.03  --sat_mode                              false
% 3.31/1.03  --sat_fm_restart_options                ""
% 3.31/1.03  --sat_gr_def                            false
% 3.31/1.03  --sat_epr_types                         true
% 3.31/1.03  --sat_non_cyclic_types                  false
% 3.31/1.03  --sat_finite_models                     false
% 3.31/1.03  --sat_fm_lemmas                         false
% 3.31/1.03  --sat_fm_prep                           false
% 3.31/1.03  --sat_fm_uc_incr                        true
% 3.31/1.03  --sat_out_model                         small
% 3.31/1.03  --sat_out_clauses                       false
% 3.31/1.03  
% 3.31/1.03  ------ QBF Options
% 3.31/1.03  
% 3.31/1.03  --qbf_mode                              false
% 3.31/1.03  --qbf_elim_univ                         false
% 3.31/1.03  --qbf_dom_inst                          none
% 3.31/1.03  --qbf_dom_pre_inst                      false
% 3.31/1.03  --qbf_sk_in                             false
% 3.31/1.03  --qbf_pred_elim                         true
% 3.31/1.03  --qbf_split                             512
% 3.31/1.03  
% 3.31/1.03  ------ BMC1 Options
% 3.31/1.03  
% 3.31/1.03  --bmc1_incremental                      false
% 3.31/1.03  --bmc1_axioms                           reachable_all
% 3.31/1.03  --bmc1_min_bound                        0
% 3.31/1.03  --bmc1_max_bound                        -1
% 3.31/1.03  --bmc1_max_bound_default                -1
% 3.31/1.03  --bmc1_symbol_reachability              true
% 3.31/1.03  --bmc1_property_lemmas                  false
% 3.31/1.03  --bmc1_k_induction                      false
% 3.31/1.03  --bmc1_non_equiv_states                 false
% 3.31/1.03  --bmc1_deadlock                         false
% 3.31/1.03  --bmc1_ucm                              false
% 3.31/1.03  --bmc1_add_unsat_core                   none
% 3.31/1.03  --bmc1_unsat_core_children              false
% 3.31/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.03  --bmc1_out_stat                         full
% 3.31/1.03  --bmc1_ground_init                      false
% 3.31/1.03  --bmc1_pre_inst_next_state              false
% 3.31/1.03  --bmc1_pre_inst_state                   false
% 3.31/1.03  --bmc1_pre_inst_reach_state             false
% 3.31/1.03  --bmc1_out_unsat_core                   false
% 3.31/1.03  --bmc1_aig_witness_out                  false
% 3.31/1.03  --bmc1_verbose                          false
% 3.31/1.03  --bmc1_dump_clauses_tptp                false
% 3.31/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.03  --bmc1_dump_file                        -
% 3.31/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.03  --bmc1_ucm_extend_mode                  1
% 3.31/1.03  --bmc1_ucm_init_mode                    2
% 3.31/1.03  --bmc1_ucm_cone_mode                    none
% 3.31/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.03  --bmc1_ucm_relax_model                  4
% 3.31/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.03  --bmc1_ucm_layered_model                none
% 3.31/1.03  --bmc1_ucm_max_lemma_size               10
% 3.31/1.03  
% 3.31/1.03  ------ AIG Options
% 3.31/1.03  
% 3.31/1.03  --aig_mode                              false
% 3.31/1.03  
% 3.31/1.03  ------ Instantiation Options
% 3.31/1.03  
% 3.31/1.03  --instantiation_flag                    true
% 3.31/1.03  --inst_sos_flag                         false
% 3.31/1.03  --inst_sos_phase                        true
% 3.31/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.03  --inst_lit_sel_side                     num_symb
% 3.31/1.03  --inst_solver_per_active                1400
% 3.31/1.03  --inst_solver_calls_frac                1.
% 3.31/1.03  --inst_passive_queue_type               priority_queues
% 3.31/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.03  --inst_passive_queues_freq              [25;2]
% 3.31/1.03  --inst_dismatching                      true
% 3.31/1.03  --inst_eager_unprocessed_to_passive     true
% 3.31/1.03  --inst_prop_sim_given                   true
% 3.31/1.03  --inst_prop_sim_new                     false
% 3.31/1.03  --inst_subs_new                         false
% 3.31/1.03  --inst_eq_res_simp                      false
% 3.31/1.03  --inst_subs_given                       false
% 3.31/1.03  --inst_orphan_elimination               true
% 3.31/1.03  --inst_learning_loop_flag               true
% 3.31/1.03  --inst_learning_start                   3000
% 3.31/1.03  --inst_learning_factor                  2
% 3.31/1.03  --inst_start_prop_sim_after_learn       3
% 3.31/1.03  --inst_sel_renew                        solver
% 3.31/1.03  --inst_lit_activity_flag                true
% 3.31/1.03  --inst_restr_to_given                   false
% 3.31/1.03  --inst_activity_threshold               500
% 3.31/1.03  --inst_out_proof                        true
% 3.31/1.03  
% 3.31/1.03  ------ Resolution Options
% 3.31/1.03  
% 3.31/1.03  --resolution_flag                       true
% 3.31/1.03  --res_lit_sel                           adaptive
% 3.31/1.03  --res_lit_sel_side                      none
% 3.31/1.03  --res_ordering                          kbo
% 3.31/1.03  --res_to_prop_solver                    active
% 3.31/1.03  --res_prop_simpl_new                    false
% 3.31/1.03  --res_prop_simpl_given                  true
% 3.31/1.03  --res_passive_queue_type                priority_queues
% 3.31/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.03  --res_passive_queues_freq               [15;5]
% 3.31/1.03  --res_forward_subs                      full
% 3.31/1.03  --res_backward_subs                     full
% 3.31/1.03  --res_forward_subs_resolution           true
% 3.31/1.03  --res_backward_subs_resolution          true
% 3.31/1.03  --res_orphan_elimination                true
% 3.31/1.03  --res_time_limit                        2.
% 3.31/1.03  --res_out_proof                         true
% 3.31/1.03  
% 3.31/1.03  ------ Superposition Options
% 3.31/1.03  
% 3.31/1.03  --superposition_flag                    true
% 3.31/1.03  --sup_passive_queue_type                priority_queues
% 3.31/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.03  --demod_completeness_check              fast
% 3.31/1.03  --demod_use_ground                      true
% 3.31/1.03  --sup_to_prop_solver                    passive
% 3.31/1.03  --sup_prop_simpl_new                    true
% 3.31/1.03  --sup_prop_simpl_given                  true
% 3.31/1.03  --sup_fun_splitting                     false
% 3.31/1.03  --sup_smt_interval                      50000
% 3.31/1.03  
% 3.31/1.03  ------ Superposition Simplification Setup
% 3.31/1.03  
% 3.31/1.03  --sup_indices_passive                   []
% 3.31/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.03  --sup_full_bw                           [BwDemod]
% 3.31/1.03  --sup_immed_triv                        [TrivRules]
% 3.31/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.03  --sup_immed_bw_main                     []
% 3.31/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.03  
% 3.31/1.03  ------ Combination Options
% 3.31/1.03  
% 3.31/1.03  --comb_res_mult                         3
% 3.31/1.03  --comb_sup_mult                         2
% 3.31/1.03  --comb_inst_mult                        10
% 3.31/1.03  
% 3.31/1.03  ------ Debug Options
% 3.31/1.03  
% 3.31/1.03  --dbg_backtrace                         false
% 3.31/1.03  --dbg_dump_prop_clauses                 false
% 3.31/1.03  --dbg_dump_prop_clauses_file            -
% 3.31/1.03  --dbg_out_stat                          false
% 3.31/1.03  ------ Parsing...
% 3.31/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.03  ------ Proving...
% 3.31/1.03  ------ Problem Properties 
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  clauses                                 40
% 3.31/1.03  conjectures                             6
% 3.31/1.03  EPR                                     8
% 3.31/1.03  Horn                                    35
% 3.31/1.03  unary                                   18
% 3.31/1.03  binary                                  3
% 3.31/1.03  lits                                    106
% 3.31/1.03  lits eq                                 17
% 3.31/1.03  fd_pure                                 0
% 3.31/1.03  fd_pseudo                               0
% 3.31/1.03  fd_cond                                 3
% 3.31/1.03  fd_pseudo_cond                          2
% 3.31/1.03  AC symbols                              0
% 3.31/1.03  
% 3.31/1.03  ------ Schedule dynamic 5 is on 
% 3.31/1.03  
% 3.31/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  ------ 
% 3.31/1.03  Current options:
% 3.31/1.03  ------ 
% 3.31/1.03  
% 3.31/1.03  ------ Input Options
% 3.31/1.03  
% 3.31/1.03  --out_options                           all
% 3.31/1.03  --tptp_safe_out                         true
% 3.31/1.03  --problem_path                          ""
% 3.31/1.03  --include_path                          ""
% 3.31/1.03  --clausifier                            res/vclausify_rel
% 3.31/1.03  --clausifier_options                    --mode clausify
% 3.31/1.03  --stdin                                 false
% 3.31/1.03  --stats_out                             all
% 3.31/1.03  
% 3.31/1.03  ------ General Options
% 3.31/1.03  
% 3.31/1.03  --fof                                   false
% 3.31/1.03  --time_out_real                         305.
% 3.31/1.03  --time_out_virtual                      -1.
% 3.31/1.03  --symbol_type_check                     false
% 3.31/1.03  --clausify_out                          false
% 3.31/1.03  --sig_cnt_out                           false
% 3.31/1.03  --trig_cnt_out                          false
% 3.31/1.03  --trig_cnt_out_tolerance                1.
% 3.31/1.03  --trig_cnt_out_sk_spl                   false
% 3.31/1.03  --abstr_cl_out                          false
% 3.31/1.03  
% 3.31/1.03  ------ Global Options
% 3.31/1.03  
% 3.31/1.03  --schedule                              default
% 3.31/1.03  --add_important_lit                     false
% 3.31/1.03  --prop_solver_per_cl                    1000
% 3.31/1.03  --min_unsat_core                        false
% 3.31/1.03  --soft_assumptions                      false
% 3.31/1.03  --soft_lemma_size                       3
% 3.31/1.03  --prop_impl_unit_size                   0
% 3.31/1.03  --prop_impl_unit                        []
% 3.31/1.03  --share_sel_clauses                     true
% 3.31/1.03  --reset_solvers                         false
% 3.31/1.03  --bc_imp_inh                            [conj_cone]
% 3.31/1.03  --conj_cone_tolerance                   3.
% 3.31/1.03  --extra_neg_conj                        none
% 3.31/1.03  --large_theory_mode                     true
% 3.31/1.03  --prolific_symb_bound                   200
% 3.31/1.03  --lt_threshold                          2000
% 3.31/1.03  --clause_weak_htbl                      true
% 3.31/1.03  --gc_record_bc_elim                     false
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing Options
% 3.31/1.03  
% 3.31/1.03  --preprocessing_flag                    true
% 3.31/1.03  --time_out_prep_mult                    0.1
% 3.31/1.03  --splitting_mode                        input
% 3.31/1.03  --splitting_grd                         true
% 3.31/1.03  --splitting_cvd                         false
% 3.31/1.03  --splitting_cvd_svl                     false
% 3.31/1.03  --splitting_nvd                         32
% 3.31/1.03  --sub_typing                            true
% 3.31/1.03  --prep_gs_sim                           true
% 3.31/1.03  --prep_unflatten                        true
% 3.31/1.03  --prep_res_sim                          true
% 3.31/1.03  --prep_upred                            true
% 3.31/1.03  --prep_sem_filter                       exhaustive
% 3.31/1.03  --prep_sem_filter_out                   false
% 3.31/1.03  --pred_elim                             true
% 3.31/1.03  --res_sim_input                         true
% 3.31/1.03  --eq_ax_congr_red                       true
% 3.31/1.03  --pure_diseq_elim                       true
% 3.31/1.03  --brand_transform                       false
% 3.31/1.03  --non_eq_to_eq                          false
% 3.31/1.03  --prep_def_merge                        true
% 3.31/1.03  --prep_def_merge_prop_impl              false
% 3.31/1.03  --prep_def_merge_mbd                    true
% 3.31/1.03  --prep_def_merge_tr_red                 false
% 3.31/1.03  --prep_def_merge_tr_cl                  false
% 3.31/1.03  --smt_preprocessing                     true
% 3.31/1.03  --smt_ac_axioms                         fast
% 3.31/1.03  --preprocessed_out                      false
% 3.31/1.03  --preprocessed_stats                    false
% 3.31/1.03  
% 3.31/1.03  ------ Abstraction refinement Options
% 3.31/1.03  
% 3.31/1.03  --abstr_ref                             []
% 3.31/1.03  --abstr_ref_prep                        false
% 3.31/1.03  --abstr_ref_until_sat                   false
% 3.31/1.03  --abstr_ref_sig_restrict                funpre
% 3.31/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.03  --abstr_ref_under                       []
% 3.31/1.03  
% 3.31/1.03  ------ SAT Options
% 3.31/1.03  
% 3.31/1.03  --sat_mode                              false
% 3.31/1.03  --sat_fm_restart_options                ""
% 3.31/1.03  --sat_gr_def                            false
% 3.31/1.03  --sat_epr_types                         true
% 3.31/1.03  --sat_non_cyclic_types                  false
% 3.31/1.03  --sat_finite_models                     false
% 3.31/1.03  --sat_fm_lemmas                         false
% 3.31/1.03  --sat_fm_prep                           false
% 3.31/1.03  --sat_fm_uc_incr                        true
% 3.31/1.03  --sat_out_model                         small
% 3.31/1.03  --sat_out_clauses                       false
% 3.31/1.03  
% 3.31/1.03  ------ QBF Options
% 3.31/1.03  
% 3.31/1.03  --qbf_mode                              false
% 3.31/1.03  --qbf_elim_univ                         false
% 3.31/1.03  --qbf_dom_inst                          none
% 3.31/1.03  --qbf_dom_pre_inst                      false
% 3.31/1.03  --qbf_sk_in                             false
% 3.31/1.03  --qbf_pred_elim                         true
% 3.31/1.03  --qbf_split                             512
% 3.31/1.03  
% 3.31/1.03  ------ BMC1 Options
% 3.31/1.03  
% 3.31/1.03  --bmc1_incremental                      false
% 3.31/1.03  --bmc1_axioms                           reachable_all
% 3.31/1.03  --bmc1_min_bound                        0
% 3.31/1.03  --bmc1_max_bound                        -1
% 3.31/1.03  --bmc1_max_bound_default                -1
% 3.31/1.03  --bmc1_symbol_reachability              true
% 3.31/1.03  --bmc1_property_lemmas                  false
% 3.31/1.03  --bmc1_k_induction                      false
% 3.31/1.03  --bmc1_non_equiv_states                 false
% 3.31/1.03  --bmc1_deadlock                         false
% 3.31/1.03  --bmc1_ucm                              false
% 3.31/1.03  --bmc1_add_unsat_core                   none
% 3.31/1.03  --bmc1_unsat_core_children              false
% 3.31/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.03  --bmc1_out_stat                         full
% 3.31/1.03  --bmc1_ground_init                      false
% 3.31/1.03  --bmc1_pre_inst_next_state              false
% 3.31/1.03  --bmc1_pre_inst_state                   false
% 3.31/1.03  --bmc1_pre_inst_reach_state             false
% 3.31/1.03  --bmc1_out_unsat_core                   false
% 3.31/1.03  --bmc1_aig_witness_out                  false
% 3.31/1.03  --bmc1_verbose                          false
% 3.31/1.03  --bmc1_dump_clauses_tptp                false
% 3.31/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.03  --bmc1_dump_file                        -
% 3.31/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.03  --bmc1_ucm_extend_mode                  1
% 3.31/1.03  --bmc1_ucm_init_mode                    2
% 3.31/1.03  --bmc1_ucm_cone_mode                    none
% 3.31/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.03  --bmc1_ucm_relax_model                  4
% 3.31/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.03  --bmc1_ucm_layered_model                none
% 3.31/1.03  --bmc1_ucm_max_lemma_size               10
% 3.31/1.03  
% 3.31/1.03  ------ AIG Options
% 3.31/1.03  
% 3.31/1.03  --aig_mode                              false
% 3.31/1.03  
% 3.31/1.03  ------ Instantiation Options
% 3.31/1.03  
% 3.31/1.03  --instantiation_flag                    true
% 3.31/1.03  --inst_sos_flag                         false
% 3.31/1.03  --inst_sos_phase                        true
% 3.31/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.03  --inst_lit_sel_side                     none
% 3.31/1.03  --inst_solver_per_active                1400
% 3.31/1.03  --inst_solver_calls_frac                1.
% 3.31/1.03  --inst_passive_queue_type               priority_queues
% 3.31/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.03  --inst_passive_queues_freq              [25;2]
% 3.31/1.03  --inst_dismatching                      true
% 3.31/1.03  --inst_eager_unprocessed_to_passive     true
% 3.31/1.03  --inst_prop_sim_given                   true
% 3.31/1.03  --inst_prop_sim_new                     false
% 3.31/1.03  --inst_subs_new                         false
% 3.31/1.03  --inst_eq_res_simp                      false
% 3.31/1.03  --inst_subs_given                       false
% 3.31/1.03  --inst_orphan_elimination               true
% 3.31/1.03  --inst_learning_loop_flag               true
% 3.31/1.03  --inst_learning_start                   3000
% 3.31/1.03  --inst_learning_factor                  2
% 3.31/1.03  --inst_start_prop_sim_after_learn       3
% 3.31/1.03  --inst_sel_renew                        solver
% 3.31/1.03  --inst_lit_activity_flag                true
% 3.31/1.03  --inst_restr_to_given                   false
% 3.31/1.03  --inst_activity_threshold               500
% 3.31/1.03  --inst_out_proof                        true
% 3.31/1.03  
% 3.31/1.03  ------ Resolution Options
% 3.31/1.03  
% 3.31/1.03  --resolution_flag                       false
% 3.31/1.03  --res_lit_sel                           adaptive
% 3.31/1.03  --res_lit_sel_side                      none
% 3.31/1.03  --res_ordering                          kbo
% 3.31/1.03  --res_to_prop_solver                    active
% 3.31/1.03  --res_prop_simpl_new                    false
% 3.31/1.03  --res_prop_simpl_given                  true
% 3.31/1.03  --res_passive_queue_type                priority_queues
% 3.31/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.03  --res_passive_queues_freq               [15;5]
% 3.31/1.03  --res_forward_subs                      full
% 3.31/1.03  --res_backward_subs                     full
% 3.31/1.03  --res_forward_subs_resolution           true
% 3.31/1.03  --res_backward_subs_resolution          true
% 3.31/1.03  --res_orphan_elimination                true
% 3.31/1.03  --res_time_limit                        2.
% 3.31/1.03  --res_out_proof                         true
% 3.31/1.03  
% 3.31/1.03  ------ Superposition Options
% 3.31/1.03  
% 3.31/1.03  --superposition_flag                    true
% 3.31/1.03  --sup_passive_queue_type                priority_queues
% 3.31/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.03  --demod_completeness_check              fast
% 3.31/1.03  --demod_use_ground                      true
% 3.31/1.03  --sup_to_prop_solver                    passive
% 3.31/1.03  --sup_prop_simpl_new                    true
% 3.31/1.03  --sup_prop_simpl_given                  true
% 3.31/1.03  --sup_fun_splitting                     false
% 3.31/1.03  --sup_smt_interval                      50000
% 3.31/1.03  
% 3.31/1.03  ------ Superposition Simplification Setup
% 3.31/1.03  
% 3.31/1.03  --sup_indices_passive                   []
% 3.31/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.03  --sup_full_bw                           [BwDemod]
% 3.31/1.03  --sup_immed_triv                        [TrivRules]
% 3.31/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.03  --sup_immed_bw_main                     []
% 3.31/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.03  
% 3.31/1.03  ------ Combination Options
% 3.31/1.03  
% 3.31/1.03  --comb_res_mult                         3
% 3.31/1.03  --comb_sup_mult                         2
% 3.31/1.03  --comb_inst_mult                        10
% 3.31/1.03  
% 3.31/1.03  ------ Debug Options
% 3.31/1.03  
% 3.31/1.03  --dbg_backtrace                         false
% 3.31/1.03  --dbg_dump_prop_clauses                 false
% 3.31/1.03  --dbg_dump_prop_clauses_file            -
% 3.31/1.03  --dbg_out_stat                          false
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  ------ Proving...
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  % SZS status Theorem for theBenchmark.p
% 3.31/1.03  
% 3.31/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/1.03  
% 3.31/1.03  fof(f26,conjecture,(
% 3.31/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f27,negated_conjecture,(
% 3.31/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.31/1.03    inference(negated_conjecture,[],[f26])).
% 3.31/1.03  
% 3.31/1.03  fof(f52,plain,(
% 3.31/1.03    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.31/1.03    inference(ennf_transformation,[],[f27])).
% 3.31/1.03  
% 3.31/1.03  fof(f53,plain,(
% 3.31/1.03    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.31/1.03    inference(flattening,[],[f52])).
% 3.31/1.03  
% 3.31/1.03  fof(f66,plain,(
% 3.31/1.03    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK5,X1,X0) & v1_funct_1(sK5))) )),
% 3.31/1.03    introduced(choice_axiom,[])).
% 3.31/1.03  
% 3.31/1.03  fof(f65,plain,(
% 3.31/1.03    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.31/1.03    introduced(choice_axiom,[])).
% 3.31/1.03  
% 3.31/1.03  fof(f67,plain,(
% 3.31/1.03    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.31/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f53,f66,f65])).
% 3.31/1.03  
% 3.31/1.03  fof(f110,plain,(
% 3.31/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.31/1.03    inference(cnf_transformation,[],[f67])).
% 3.31/1.03  
% 3.31/1.03  fof(f113,plain,(
% 3.31/1.03    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 3.31/1.03    inference(cnf_transformation,[],[f67])).
% 3.31/1.03  
% 3.31/1.03  fof(f23,axiom,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f48,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.31/1.03    inference(ennf_transformation,[],[f23])).
% 3.31/1.03  
% 3.31/1.03  fof(f49,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.31/1.03    inference(flattening,[],[f48])).
% 3.31/1.03  
% 3.31/1.03  fof(f104,plain,(
% 3.31/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f49])).
% 3.31/1.03  
% 3.31/1.03  fof(f111,plain,(
% 3.31/1.03    v1_funct_1(sK5)),
% 3.31/1.03    inference(cnf_transformation,[],[f67])).
% 3.31/1.03  
% 3.31/1.03  fof(f21,axiom,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f46,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.31/1.03    inference(ennf_transformation,[],[f21])).
% 3.31/1.03  
% 3.31/1.03  fof(f47,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.31/1.03    inference(flattening,[],[f46])).
% 3.31/1.03  
% 3.31/1.03  fof(f102,plain,(
% 3.31/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f47])).
% 3.31/1.03  
% 3.31/1.03  fof(f19,axiom,(
% 3.31/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f42,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.31/1.03    inference(ennf_transformation,[],[f19])).
% 3.31/1.03  
% 3.31/1.03  fof(f43,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/1.03    inference(flattening,[],[f42])).
% 3.31/1.03  
% 3.31/1.03  fof(f63,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/1.03    inference(nnf_transformation,[],[f43])).
% 3.31/1.03  
% 3.31/1.03  fof(f97,plain,(
% 3.31/1.03    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/1.03    inference(cnf_transformation,[],[f63])).
% 3.31/1.03  
% 3.31/1.03  fof(f114,plain,(
% 3.31/1.03    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 3.31/1.03    inference(cnf_transformation,[],[f67])).
% 3.31/1.03  
% 3.31/1.03  fof(f22,axiom,(
% 3.31/1.03    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f28,plain,(
% 3.31/1.03    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.31/1.03    inference(pure_predicate_removal,[],[f22])).
% 3.31/1.03  
% 3.31/1.03  fof(f103,plain,(
% 3.31/1.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.31/1.03    inference(cnf_transformation,[],[f28])).
% 3.31/1.03  
% 3.31/1.03  fof(f108,plain,(
% 3.31/1.03    v1_funct_1(sK4)),
% 3.31/1.03    inference(cnf_transformation,[],[f67])).
% 3.31/1.03  
% 3.31/1.03  fof(f12,axiom,(
% 3.31/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f36,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f12])).
% 3.31/1.03  
% 3.31/1.03  fof(f84,plain,(
% 3.31/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f36])).
% 3.31/1.03  
% 3.31/1.03  fof(f13,axiom,(
% 3.31/1.03    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f86,plain,(
% 3.31/1.03    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.31/1.03    inference(cnf_transformation,[],[f13])).
% 3.31/1.03  
% 3.31/1.03  fof(f24,axiom,(
% 3.31/1.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f105,plain,(
% 3.31/1.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f24])).
% 3.31/1.03  
% 3.31/1.03  fof(f116,plain,(
% 3.31/1.03    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.31/1.03    inference(definition_unfolding,[],[f86,f105])).
% 3.31/1.03  
% 3.31/1.03  fof(f25,axiom,(
% 3.31/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f50,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.31/1.03    inference(ennf_transformation,[],[f25])).
% 3.31/1.03  
% 3.31/1.03  fof(f51,plain,(
% 3.31/1.03    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.31/1.03    inference(flattening,[],[f50])).
% 3.31/1.03  
% 3.31/1.03  fof(f106,plain,(
% 3.31/1.03    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f51])).
% 3.31/1.03  
% 3.31/1.03  fof(f109,plain,(
% 3.31/1.03    v1_funct_2(sK4,sK2,sK3)),
% 3.31/1.03    inference(cnf_transformation,[],[f67])).
% 3.31/1.03  
% 3.31/1.03  fof(f112,plain,(
% 3.31/1.03    v1_funct_2(sK5,sK3,sK2)),
% 3.31/1.03    inference(cnf_transformation,[],[f67])).
% 3.31/1.03  
% 3.31/1.03  fof(f15,axiom,(
% 3.31/1.03    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f93,plain,(
% 3.31/1.03    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.31/1.03    inference(cnf_transformation,[],[f15])).
% 3.31/1.03  
% 3.31/1.03  fof(f118,plain,(
% 3.31/1.03    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.31/1.03    inference(definition_unfolding,[],[f93,f105])).
% 3.31/1.03  
% 3.31/1.03  fof(f17,axiom,(
% 3.31/1.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f40,plain,(
% 3.31/1.03    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f17])).
% 3.31/1.03  
% 3.31/1.03  fof(f95,plain,(
% 3.31/1.03    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f40])).
% 3.31/1.03  
% 3.31/1.03  fof(f8,axiom,(
% 3.31/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f33,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f8])).
% 3.31/1.03  
% 3.31/1.03  fof(f79,plain,(
% 3.31/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f33])).
% 3.31/1.03  
% 3.31/1.03  fof(f11,axiom,(
% 3.31/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f83,plain,(
% 3.31/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.31/1.03    inference(cnf_transformation,[],[f11])).
% 3.31/1.03  
% 3.31/1.03  fof(f18,axiom,(
% 3.31/1.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f41,plain,(
% 3.31/1.03    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f18])).
% 3.31/1.03  
% 3.31/1.03  fof(f96,plain,(
% 3.31/1.03    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f41])).
% 3.31/1.03  
% 3.31/1.03  fof(f16,axiom,(
% 3.31/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f29,plain,(
% 3.31/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.31/1.03    inference(pure_predicate_removal,[],[f16])).
% 3.31/1.03  
% 3.31/1.03  fof(f39,plain,(
% 3.31/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/1.03    inference(ennf_transformation,[],[f29])).
% 3.31/1.03  
% 3.31/1.03  fof(f94,plain,(
% 3.31/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/1.03    inference(cnf_transformation,[],[f39])).
% 3.31/1.03  
% 3.31/1.03  fof(f9,axiom,(
% 3.31/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f34,plain,(
% 3.31/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.31/1.03    inference(ennf_transformation,[],[f9])).
% 3.31/1.03  
% 3.31/1.03  fof(f58,plain,(
% 3.31/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.31/1.03    inference(nnf_transformation,[],[f34])).
% 3.31/1.03  
% 3.31/1.03  fof(f80,plain,(
% 3.31/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f58])).
% 3.31/1.03  
% 3.31/1.03  fof(f3,axiom,(
% 3.31/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f54,plain,(
% 3.31/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.03    inference(nnf_transformation,[],[f3])).
% 3.31/1.03  
% 3.31/1.03  fof(f55,plain,(
% 3.31/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.03    inference(flattening,[],[f54])).
% 3.31/1.03  
% 3.31/1.03  fof(f72,plain,(
% 3.31/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f55])).
% 3.31/1.03  
% 3.31/1.03  fof(f2,axiom,(
% 3.31/1.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f30,plain,(
% 3.31/1.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f2])).
% 3.31/1.03  
% 3.31/1.03  fof(f69,plain,(
% 3.31/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f30])).
% 3.31/1.03  
% 3.31/1.03  fof(f81,plain,(
% 3.31/1.03    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f58])).
% 3.31/1.03  
% 3.31/1.03  fof(f20,axiom,(
% 3.31/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f44,plain,(
% 3.31/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.31/1.03    inference(ennf_transformation,[],[f20])).
% 3.31/1.03  
% 3.31/1.03  fof(f45,plain,(
% 3.31/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.31/1.03    inference(flattening,[],[f44])).
% 3.31/1.03  
% 3.31/1.03  fof(f64,plain,(
% 3.31/1.03    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.31/1.03    inference(nnf_transformation,[],[f45])).
% 3.31/1.03  
% 3.31/1.03  fof(f100,plain,(
% 3.31/1.03    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f64])).
% 3.31/1.03  
% 3.31/1.03  fof(f125,plain,(
% 3.31/1.03    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.31/1.03    inference(equality_resolution,[],[f100])).
% 3.31/1.03  
% 3.31/1.03  fof(f115,plain,(
% 3.31/1.03    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 3.31/1.03    inference(cnf_transformation,[],[f67])).
% 3.31/1.03  
% 3.31/1.03  fof(f71,plain,(
% 3.31/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.31/1.03    inference(cnf_transformation,[],[f55])).
% 3.31/1.03  
% 3.31/1.03  fof(f120,plain,(
% 3.31/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.31/1.03    inference(equality_resolution,[],[f71])).
% 3.31/1.03  
% 3.31/1.03  fof(f1,axiom,(
% 3.31/1.03    v1_xboole_0(k1_xboole_0)),
% 3.31/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f68,plain,(
% 3.31/1.03    v1_xboole_0(k1_xboole_0)),
% 3.31/1.03    inference(cnf_transformation,[],[f1])).
% 3.31/1.03  
% 3.31/1.03  cnf(c_44,negated_conjecture,
% 3.31/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.31/1.03      inference(cnf_transformation,[],[f110]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1436,plain,
% 3.31/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_41,negated_conjecture,
% 3.31/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 3.31/1.03      inference(cnf_transformation,[],[f113]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1439,plain,
% 3.31/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_36,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.31/1.03      | ~ v1_funct_1(X0)
% 3.31/1.03      | ~ v1_funct_1(X3)
% 3.31/1.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f104]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1442,plain,
% 3.31/1.03      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.31/1.03      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.31/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.31/1.03      | v1_funct_1(X5) != iProver_top
% 3.31/1.03      | v1_funct_1(X4) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_7483,plain,
% 3.31/1.03      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 3.31/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.31/1.03      | v1_funct_1(X2) != iProver_top
% 3.31/1.03      | v1_funct_1(sK5) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1439,c_1442]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_43,negated_conjecture,
% 3.31/1.03      ( v1_funct_1(sK5) ),
% 3.31/1.03      inference(cnf_transformation,[],[f111]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_50,plain,
% 3.31/1.03      ( v1_funct_1(sK5) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9081,plain,
% 3.31/1.03      ( v1_funct_1(X2) != iProver_top
% 3.31/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.31/1.03      | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_7483,c_50]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9082,plain,
% 3.31/1.03      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 3.31/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.31/1.03      | v1_funct_1(X2) != iProver_top ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_9081]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9094,plain,
% 3.31/1.03      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
% 3.31/1.03      | v1_funct_1(sK4) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1436,c_9082]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_33,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.31/1.03      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.31/1.03      | ~ v1_funct_1(X0)
% 3.31/1.03      | ~ v1_funct_1(X3) ),
% 3.31/1.03      inference(cnf_transformation,[],[f102]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1445,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.31/1.03      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.31/1.03      | v1_funct_1(X0) != iProver_top
% 3.31/1.03      | v1_funct_1(X3) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_30,plain,
% 3.31/1.03      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.31/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.31/1.03      | X3 = X2 ),
% 3.31/1.03      inference(cnf_transformation,[],[f97]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_40,negated_conjecture,
% 3.31/1.03      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f114]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_469,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | X3 = X0
% 3.31/1.03      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
% 3.31/1.03      | k6_partfun1(sK2) != X3
% 3.31/1.03      | sK2 != X2
% 3.31/1.03      | sK2 != X1 ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_30,c_40]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_470,plain,
% 3.31/1.03      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.31/1.03      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.31/1.03      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 3.31/1.03      inference(unflattening,[status(thm)],[c_469]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_35,plain,
% 3.31/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.31/1.03      inference(cnf_transformation,[],[f103]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_478,plain,
% 3.31/1.03      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.31/1.03      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 3.31/1.03      inference(forward_subsumption_resolution,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_470,c_35]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1433,plain,
% 3.31/1.03      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 3.31/1.03      | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4984,plain,
% 3.31/1.03      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2)
% 3.31/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.31/1.03      | v1_funct_1(sK4) != iProver_top
% 3.31/1.03      | v1_funct_1(sK5) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1445,c_1433]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_46,negated_conjecture,
% 3.31/1.03      ( v1_funct_1(sK4) ),
% 3.31/1.03      inference(cnf_transformation,[],[f108]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_47,plain,
% 3.31/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_49,plain,
% 3.31/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_52,plain,
% 3.31/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5360,plain,
% 3.31/1.03      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_4984,c_47,c_49,c_50,c_52]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9111,plain,
% 3.31/1.03      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
% 3.31/1.03      | v1_funct_1(sK4) != iProver_top ),
% 3.31/1.03      inference(light_normalisation,[status(thm)],[c_9094,c_5360]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9367,plain,
% 3.31/1.03      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_9111,c_47]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_16,plain,
% 3.31/1.03      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.31/1.03      | ~ v1_relat_1(X0)
% 3.31/1.03      | ~ v1_relat_1(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1455,plain,
% 3.31/1.03      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.31/1.03      | v1_relat_1(X0) != iProver_top
% 3.31/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9370,plain,
% 3.31/1.03      ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
% 3.31/1.03      | v1_relat_1(sK4) != iProver_top
% 3.31/1.03      | v1_relat_1(sK5) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_9367,c_1455]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_17,plain,
% 3.31/1.03      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.31/1.03      inference(cnf_transformation,[],[f116]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9371,plain,
% 3.31/1.03      ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
% 3.31/1.03      | v1_relat_1(sK4) != iProver_top
% 3.31/1.03      | v1_relat_1(sK5) != iProver_top ),
% 3.31/1.03      inference(demodulation,[status(thm)],[c_9370,c_17]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_798,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3214,plain,
% 3.31/1.03      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_798]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_6609,plain,
% 3.31/1.03      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_3214]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_6610,plain,
% 3.31/1.03      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_6609]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_38,plain,
% 3.31/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.31/1.03      | ~ v1_funct_2(X3,X4,X1)
% 3.31/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | ~ v1_funct_1(X0)
% 3.31/1.03      | ~ v1_funct_1(X3)
% 3.31/1.03      | v2_funct_1(X3)
% 3.31/1.03      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.31/1.03      | k1_xboole_0 = X2 ),
% 3.31/1.03      inference(cnf_transformation,[],[f106]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1440,plain,
% 3.31/1.03      ( k1_xboole_0 = X0
% 3.31/1.03      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.31/1.03      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.31/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.31/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.31/1.03      | v1_funct_1(X1) != iProver_top
% 3.31/1.03      | v1_funct_1(X3) != iProver_top
% 3.31/1.03      | v2_funct_1(X3) = iProver_top
% 3.31/1.03      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5367,plain,
% 3.31/1.03      ( sK2 = k1_xboole_0
% 3.31/1.03      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.31/1.03      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.31/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.31/1.03      | v1_funct_1(sK4) != iProver_top
% 3.31/1.03      | v1_funct_1(sK5) != iProver_top
% 3.31/1.03      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 3.31/1.03      | v2_funct_1(sK4) = iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_5360,c_1440]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_45,negated_conjecture,
% 3.31/1.03      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.31/1.03      inference(cnf_transformation,[],[f109]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_48,plain,
% 3.31/1.03      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_42,negated_conjecture,
% 3.31/1.03      ( v1_funct_2(sK5,sK3,sK2) ),
% 3.31/1.03      inference(cnf_transformation,[],[f112]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_51,plain,
% 3.31/1.03      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5499,plain,
% 3.31/1.03      ( sK2 = k1_xboole_0
% 3.31/1.03      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 3.31/1.03      | v2_funct_1(sK4) = iProver_top ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_5367,c_47,c_48,c_49,c_50,c_51,c_52]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_24,plain,
% 3.31/1.03      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f118]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1449,plain,
% 3.31/1.03      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5506,plain,
% 3.31/1.03      ( sK2 = k1_xboole_0 | v2_funct_1(sK4) = iProver_top ),
% 3.31/1.03      inference(forward_subsumption_resolution,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_5499,c_1449]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_799,plain,
% 3.31/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.31/1.03      theory(equality) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5429,plain,
% 3.31/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_799]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5431,plain,
% 3.31/1.03      ( v1_xboole_0(sK2)
% 3.31/1.03      | ~ v1_xboole_0(k1_xboole_0)
% 3.31/1.03      | sK2 != k1_xboole_0 ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_5429]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_809,plain,
% 3.31/1.03      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.31/1.03      theory(equality) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4615,plain,
% 3.31/1.03      ( ~ v2_funct_1(X0) | v2_funct_1(sK4) | sK4 != X0 ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_809]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4616,plain,
% 3.31/1.03      ( sK4 != X0
% 3.31/1.03      | v2_funct_1(X0) != iProver_top
% 3.31/1.03      | v2_funct_1(sK4) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_4615]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4618,plain,
% 3.31/1.03      ( sK4 != k1_xboole_0
% 3.31/1.03      | v2_funct_1(sK4) = iProver_top
% 3.31/1.03      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_4616]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_27,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | ~ v1_xboole_0(X1)
% 3.31/1.03      | v1_xboole_0(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1447,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/1.03      | v1_xboole_0(X1) != iProver_top
% 3.31/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4462,plain,
% 3.31/1.03      ( v1_xboole_0(sK4) = iProver_top
% 3.31/1.03      | v1_xboole_0(sK2) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1436,c_1447]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4474,plain,
% 3.31/1.03      ( v1_xboole_0(sK4) | ~ v1_xboole_0(sK2) ),
% 3.31/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_4462]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_11,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.31/1.03      | ~ v1_relat_1(X1)
% 3.31/1.03      | v1_relat_1(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1458,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.31/1.03      | v1_relat_1(X1) != iProver_top
% 3.31/1.03      | v1_relat_1(X0) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3639,plain,
% 3.31/1.03      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.31/1.03      | v1_relat_1(sK4) = iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1436,c_1458]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_15,plain,
% 3.31/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1456,plain,
% 3.31/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4325,plain,
% 3.31/1.03      ( v1_relat_1(sK4) = iProver_top ),
% 3.31/1.03      inference(forward_subsumption_resolution,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_3639,c_1456]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3638,plain,
% 3.31/1.03      ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
% 3.31/1.03      | v1_relat_1(sK5) = iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1439,c_1458]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3959,plain,
% 3.31/1.03      ( v1_relat_1(sK5) = iProver_top ),
% 3.31/1.03      inference(forward_subsumption_resolution,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_3638,c_1456]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1443,plain,
% 3.31/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_28,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | ~ v1_xboole_0(X2)
% 3.31/1.03      | v1_xboole_0(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1446,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/1.03      | v1_xboole_0(X2) != iProver_top
% 3.31/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3658,plain,
% 3.31/1.03      ( v1_xboole_0(X0) != iProver_top
% 3.31/1.03      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1443,c_1446]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3682,plain,
% 3.31/1.03      ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
% 3.31/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_3658]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_26,plain,
% 3.31/1.03      ( v5_relat_1(X0,X1)
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.31/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_13,plain,
% 3.31/1.03      ( ~ v5_relat_1(X0,X1)
% 3.31/1.03      | r1_tarski(k2_relat_1(X0),X1)
% 3.31/1.03      | ~ v1_relat_1(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_508,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/1.03      | r1_tarski(k2_relat_1(X0),X2)
% 3.31/1.03      | ~ v1_relat_1(X0) ),
% 3.31/1.03      inference(resolution,[status(thm)],[c_26,c_13]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1432,plain,
% 3.31/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/1.03      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.31/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2837,plain,
% 3.31/1.03      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
% 3.31/1.03      | v1_relat_1(sK5) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_1439,c_1432]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2,plain,
% 3.31/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.31/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1463,plain,
% 3.31/1.03      ( X0 = X1
% 3.31/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.31/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3491,plain,
% 3.31/1.03      ( k2_relat_1(sK5) = sK2
% 3.31/1.03      | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top
% 3.31/1.03      | v1_relat_1(sK5) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_2837,c_1463]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1,plain,
% 3.31/1.03      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.31/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2219,plain,
% 3.31/1.03      ( ~ v1_xboole_0(k6_partfun1(X0)) | k1_xboole_0 = k6_partfun1(X0) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2223,plain,
% 3.31/1.03      ( k1_xboole_0 = k6_partfun1(X0)
% 3.31/1.03      | v1_xboole_0(k6_partfun1(X0)) != iProver_top ),
% 3.31/1.04      inference(predicate_to_equality,[status(thm)],[c_2219]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_2225,plain,
% 3.31/1.04      ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.31/1.04      | v1_xboole_0(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.31/1.04      inference(instantiation,[status(thm)],[c_2223]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_797,plain,( X0 = X0 ),theory(equality) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_2036,plain,
% 3.31/1.04      ( sK4 = sK4 ),
% 3.31/1.04      inference(instantiation,[status(thm)],[c_797]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_1966,plain,
% 3.31/1.04      ( ~ v1_xboole_0(sK4) | k1_xboole_0 = sK4 ),
% 3.31/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_1777,plain,
% 3.31/1.04      ( v2_funct_1(X0)
% 3.31/1.04      | ~ v2_funct_1(k6_partfun1(X1))
% 3.31/1.04      | X0 != k6_partfun1(X1) ),
% 3.31/1.04      inference(instantiation,[status(thm)],[c_809]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_1778,plain,
% 3.31/1.04      ( X0 != k6_partfun1(X1)
% 3.31/1.04      | v2_funct_1(X0) = iProver_top
% 3.31/1.04      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.31/1.04      inference(predicate_to_equality,[status(thm)],[c_1777]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_1780,plain,
% 3.31/1.04      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.31/1.04      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.31/1.04      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.31/1.04      inference(instantiation,[status(thm)],[c_1778]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_12,plain,
% 3.31/1.04      ( v5_relat_1(X0,X1)
% 3.31/1.04      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.31/1.04      | ~ v1_relat_1(X0) ),
% 3.31/1.04      inference(cnf_transformation,[],[f81]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_31,plain,
% 3.31/1.04      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.31/1.04      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.31/1.04      | ~ v1_relat_1(X0) ),
% 3.31/1.04      inference(cnf_transformation,[],[f125]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_39,negated_conjecture,
% 3.31/1.04      ( ~ v2_funct_2(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 3.31/1.04      inference(cnf_transformation,[],[f115]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_487,plain,
% 3.31/1.04      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.31/1.04      | ~ v2_funct_1(sK4)
% 3.31/1.04      | ~ v1_relat_1(X0)
% 3.31/1.04      | k2_relat_1(X0) != sK2
% 3.31/1.04      | sK5 != X0 ),
% 3.31/1.04      inference(resolution_lifted,[status(thm)],[c_31,c_39]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_488,plain,
% 3.31/1.04      ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
% 3.31/1.04      | ~ v2_funct_1(sK4)
% 3.31/1.04      | ~ v1_relat_1(sK5)
% 3.31/1.04      | k2_relat_1(sK5) != sK2 ),
% 3.31/1.04      inference(unflattening,[status(thm)],[c_487]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_541,plain,
% 3.31/1.04      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.31/1.04      | ~ v2_funct_1(sK4)
% 3.31/1.04      | ~ v1_relat_1(X0)
% 3.31/1.04      | ~ v1_relat_1(sK5)
% 3.31/1.04      | k2_relat_1(sK5) != X1
% 3.31/1.04      | k2_relat_1(sK5) != sK2
% 3.31/1.04      | sK5 != X0 ),
% 3.31/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_488]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_542,plain,
% 3.31/1.04      ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
% 3.31/1.04      | ~ v2_funct_1(sK4)
% 3.31/1.04      | ~ v1_relat_1(sK5)
% 3.31/1.04      | k2_relat_1(sK5) != sK2 ),
% 3.31/1.04      inference(unflattening,[status(thm)],[c_541]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_3,plain,
% 3.31/1.04      ( r1_tarski(X0,X0) ),
% 3.31/1.04      inference(cnf_transformation,[],[f120]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_552,plain,
% 3.31/1.04      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK5) | k2_relat_1(sK5) != sK2 ),
% 3.31/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_542,c_3]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_553,plain,
% 3.31/1.04      ( k2_relat_1(sK5) != sK2
% 3.31/1.04      | v2_funct_1(sK4) != iProver_top
% 3.31/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.31/1.04      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_0,plain,
% 3.31/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 3.31/1.04      inference(cnf_transformation,[],[f68]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_150,plain,
% 3.31/1.04      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.31/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_93,plain,
% 3.31/1.04      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.31/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(c_95,plain,
% 3.31/1.04      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.31/1.04      inference(instantiation,[status(thm)],[c_93]) ).
% 3.31/1.04  
% 3.31/1.04  cnf(contradiction,plain,
% 3.31/1.04      ( $false ),
% 3.31/1.04      inference(minisat,
% 3.31/1.04                [status(thm)],
% 3.31/1.04                [c_9371,c_6610,c_5506,c_5431,c_4618,c_4474,c_4325,c_3959,
% 3.31/1.04                 c_3682,c_3491,c_2225,c_2036,c_1966,c_1780,c_553,c_150,
% 3.31/1.04                 c_0,c_95]) ).
% 3.31/1.04  
% 3.31/1.04  
% 3.31/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/1.04  
% 3.31/1.04  ------                               Statistics
% 3.31/1.04  
% 3.31/1.04  ------ General
% 3.31/1.04  
% 3.31/1.04  abstr_ref_over_cycles:                  0
% 3.31/1.04  abstr_ref_under_cycles:                 0
% 3.31/1.04  gc_basic_clause_elim:                   0
% 3.31/1.04  forced_gc_time:                         0
% 3.31/1.04  parsing_time:                           0.016
% 3.31/1.04  unif_index_cands_time:                  0.
% 3.31/1.04  unif_index_add_time:                    0.
% 3.31/1.04  orderings_time:                         0.
% 3.31/1.04  out_proof_time:                         0.011
% 3.31/1.04  total_time:                             0.338
% 3.31/1.04  num_of_symbols:                         57
% 3.31/1.04  num_of_terms:                           11272
% 3.31/1.04  
% 3.31/1.04  ------ Preprocessing
% 3.31/1.04  
% 3.31/1.04  num_of_splits:                          0
% 3.31/1.04  num_of_split_atoms:                     0
% 3.31/1.04  num_of_reused_defs:                     0
% 3.31/1.04  num_eq_ax_congr_red:                    16
% 3.31/1.04  num_of_sem_filtered_clauses:            1
% 3.31/1.04  num_of_subtypes:                        0
% 3.31/1.04  monotx_restored_types:                  0
% 3.31/1.04  sat_num_of_epr_types:                   0
% 3.31/1.04  sat_num_of_non_cyclic_types:            0
% 3.31/1.04  sat_guarded_non_collapsed_types:        0
% 3.31/1.04  num_pure_diseq_elim:                    0
% 3.31/1.04  simp_replaced_by:                       0
% 3.31/1.04  res_preprocessed:                       201
% 3.31/1.04  prep_upred:                             0
% 3.31/1.04  prep_unflattend:                        15
% 3.31/1.04  smt_new_axioms:                         0
% 3.31/1.04  pred_elim_cands:                        8
% 3.31/1.04  pred_elim:                              3
% 3.31/1.04  pred_elim_cl:                           6
% 3.31/1.04  pred_elim_cycles:                       5
% 3.31/1.04  merged_defs:                            0
% 3.31/1.04  merged_defs_ncl:                        0
% 3.31/1.04  bin_hyper_res:                          0
% 3.31/1.04  prep_cycles:                            4
% 3.31/1.04  pred_elim_time:                         0.005
% 3.31/1.04  splitting_time:                         0.
% 3.31/1.04  sem_filter_time:                        0.
% 3.31/1.04  monotx_time:                            0.001
% 3.31/1.04  subtype_inf_time:                       0.
% 3.31/1.04  
% 3.31/1.04  ------ Problem properties
% 3.31/1.04  
% 3.31/1.04  clauses:                                40
% 3.31/1.04  conjectures:                            6
% 3.31/1.04  epr:                                    8
% 3.31/1.04  horn:                                   35
% 3.31/1.04  ground:                                 9
% 3.31/1.04  unary:                                  18
% 3.31/1.04  binary:                                 3
% 3.31/1.04  lits:                                   106
% 3.31/1.04  lits_eq:                                17
% 3.31/1.04  fd_pure:                                0
% 3.31/1.04  fd_pseudo:                              0
% 3.31/1.04  fd_cond:                                3
% 3.31/1.04  fd_pseudo_cond:                         2
% 3.31/1.04  ac_symbols:                             0
% 3.31/1.04  
% 3.31/1.04  ------ Propositional Solver
% 3.31/1.04  
% 3.31/1.04  prop_solver_calls:                      27
% 3.31/1.04  prop_fast_solver_calls:                 1404
% 3.31/1.04  smt_solver_calls:                       0
% 3.31/1.04  smt_fast_solver_calls:                  0
% 3.31/1.04  prop_num_of_clauses:                    3988
% 3.31/1.04  prop_preprocess_simplified:             11789
% 3.31/1.04  prop_fo_subsumed:                       29
% 3.31/1.04  prop_solver_time:                       0.
% 3.31/1.04  smt_solver_time:                        0.
% 3.31/1.04  smt_fast_solver_time:                   0.
% 3.31/1.04  prop_fast_solver_time:                  0.
% 3.31/1.04  prop_unsat_core_time:                   0.
% 3.31/1.04  
% 3.31/1.04  ------ QBF
% 3.31/1.04  
% 3.31/1.04  qbf_q_res:                              0
% 3.31/1.04  qbf_num_tautologies:                    0
% 3.31/1.04  qbf_prep_cycles:                        0
% 3.31/1.04  
% 3.31/1.04  ------ BMC1
% 3.31/1.04  
% 3.31/1.04  bmc1_current_bound:                     -1
% 3.31/1.04  bmc1_last_solved_bound:                 -1
% 3.31/1.04  bmc1_unsat_core_size:                   -1
% 3.31/1.04  bmc1_unsat_core_parents_size:           -1
% 3.31/1.04  bmc1_merge_next_fun:                    0
% 3.31/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.31/1.04  
% 3.31/1.04  ------ Instantiation
% 3.31/1.04  
% 3.31/1.04  inst_num_of_clauses:                    1161
% 3.31/1.04  inst_num_in_passive:                    537
% 3.31/1.04  inst_num_in_active:                     445
% 3.31/1.04  inst_num_in_unprocessed:                179
% 3.31/1.04  inst_num_of_loops:                      470
% 3.31/1.04  inst_num_of_learning_restarts:          0
% 3.31/1.04  inst_num_moves_active_passive:          24
% 3.31/1.04  inst_lit_activity:                      0
% 3.31/1.04  inst_lit_activity_moves:                0
% 3.31/1.04  inst_num_tautologies:                   0
% 3.31/1.04  inst_num_prop_implied:                  0
% 3.31/1.04  inst_num_existing_simplified:           0
% 3.31/1.04  inst_num_eq_res_simplified:             0
% 3.31/1.04  inst_num_child_elim:                    0
% 3.31/1.04  inst_num_of_dismatching_blockings:      98
% 3.31/1.04  inst_num_of_non_proper_insts:           867
% 3.31/1.04  inst_num_of_duplicates:                 0
% 3.31/1.04  inst_inst_num_from_inst_to_res:         0
% 3.31/1.04  inst_dismatching_checking_time:         0.
% 3.31/1.04  
% 3.31/1.04  ------ Resolution
% 3.31/1.04  
% 3.31/1.04  res_num_of_clauses:                     0
% 3.31/1.04  res_num_in_passive:                     0
% 3.31/1.04  res_num_in_active:                      0
% 3.31/1.04  res_num_of_loops:                       205
% 3.31/1.04  res_forward_subset_subsumed:            24
% 3.31/1.04  res_backward_subset_subsumed:           0
% 3.31/1.04  res_forward_subsumed:                   0
% 3.31/1.04  res_backward_subsumed:                  1
% 3.31/1.04  res_forward_subsumption_resolution:     2
% 3.31/1.04  res_backward_subsumption_resolution:    0
% 3.31/1.04  res_clause_to_clause_subsumption:       469
% 3.31/1.04  res_orphan_elimination:                 0
% 3.31/1.04  res_tautology_del:                      27
% 3.31/1.04  res_num_eq_res_simplified:              0
% 3.31/1.04  res_num_sel_changes:                    0
% 3.31/1.04  res_moves_from_active_to_pass:          0
% 3.31/1.04  
% 3.31/1.04  ------ Superposition
% 3.31/1.04  
% 3.31/1.04  sup_time_total:                         0.
% 3.31/1.04  sup_time_generating:                    0.
% 3.31/1.04  sup_time_sim_full:                      0.
% 3.31/1.04  sup_time_sim_immed:                     0.
% 3.31/1.04  
% 3.31/1.04  sup_num_of_clauses:                     161
% 3.31/1.04  sup_num_in_active:                      92
% 3.31/1.04  sup_num_in_passive:                     69
% 3.31/1.04  sup_num_of_loops:                       93
% 3.31/1.04  sup_fw_superposition:                   121
% 3.31/1.04  sup_bw_superposition:                   48
% 3.31/1.04  sup_immediate_simplified:               35
% 3.31/1.04  sup_given_eliminated:                   0
% 3.31/1.04  comparisons_done:                       0
% 3.31/1.04  comparisons_avoided:                    0
% 3.31/1.04  
% 3.31/1.04  ------ Simplifications
% 3.31/1.04  
% 3.31/1.04  
% 3.31/1.04  sim_fw_subset_subsumed:                 9
% 3.31/1.04  sim_bw_subset_subsumed:                 1
% 3.31/1.04  sim_fw_subsumed:                        10
% 3.31/1.04  sim_bw_subsumed:                        1
% 3.31/1.04  sim_fw_subsumption_res:                 4
% 3.31/1.04  sim_bw_subsumption_res:                 0
% 3.31/1.04  sim_tautology_del:                      1
% 3.31/1.04  sim_eq_tautology_del:                   8
% 3.31/1.04  sim_eq_res_simp:                        0
% 3.31/1.04  sim_fw_demodulated:                     7
% 3.31/1.04  sim_bw_demodulated:                     2
% 3.31/1.04  sim_light_normalised:                   14
% 3.31/1.04  sim_joinable_taut:                      0
% 3.31/1.04  sim_joinable_simp:                      0
% 3.31/1.04  sim_ac_normalised:                      0
% 3.31/1.04  sim_smt_subsumption:                    0
% 3.31/1.04  
%------------------------------------------------------------------------------
