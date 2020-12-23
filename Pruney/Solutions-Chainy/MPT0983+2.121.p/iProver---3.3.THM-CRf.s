%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:11 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 928 expanded)
%              Number of clauses        :  109 ( 276 expanded)
%              Number of leaves         :   25 ( 233 expanded)
%              Depth                    :   17
%              Number of atoms          :  624 (5783 expanded)
%              Number of equality atoms :  190 ( 444 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f54,f53])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f78,f84])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f22,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

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
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f94,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f73,f84])).

fof(f91,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_698,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7529,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_7531,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(sK0)
    | sK2 != sK0 ),
    inference(instantiation,[status(thm)],[c_7529])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1225,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1228,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1231,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4211,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1231])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4380,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4211,c_41])).

cnf(c_4381,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4380])).

cnf(c_4392,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_4381])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1585,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1850,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_2402,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_3803,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2402])).

cnf(c_4571,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4392,c_37,c_35,c_34,c_32,c_3803])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_397,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_22,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_68,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_68])).

cnf(c_1222,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_4574,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4571,c_1222])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4576,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4571,c_1233])).

cnf(c_4993,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_38,c_40,c_41,c_43,c_4576])).

cnf(c_4996,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_4993,c_4571])).

cnf(c_29,plain,
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

cnf(c_1229,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5003,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4996,c_1229])).

cnf(c_14,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1237,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4997,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_1237])).

cnf(c_15,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4998,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4997,c_15])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_11])).

cnf(c_1221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_2669,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1221])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1247,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2960,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_1247])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1240,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2870,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1240])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1239,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3020,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2870,c_1239])).

cnf(c_3825,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2960,c_3020])).

cnf(c_3826,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3825])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1242,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2888,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1241])).

cnf(c_3095,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_2888])).

cnf(c_3105,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3095])).

cnf(c_2871,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1240])).

cnf(c_3025,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2871,c_1239])).

cnf(c_3021,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3020])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1238,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2833,plain,
    ( v1_relat_1(k6_partfun1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1238])).

cnf(c_2834,plain,
    ( ~ v1_relat_1(k6_partfun1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2833])).

cnf(c_2836,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2734,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2736,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0)
    | sK2 = sK0 ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_2604,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k6_partfun1(X1))
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2606,plain,
    ( ~ v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0)
    | sK0 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_689,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1615,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1617,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_1486,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1488,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK0)
    | sK0 != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_30,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_415,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_416,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_469,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_416])).

cnf(c_470,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_480,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_470,c_2])).

cnf(c_481,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_83,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_80,plain,
    ( v1_relat_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7531,c_5003,c_4998,c_3826,c_3105,c_3025,c_3021,c_3020,c_2836,c_2736,c_2606,c_1617,c_1488,c_481,c_480,c_0,c_84,c_83,c_80,c_43,c_42,c_41,c_40,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.78/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.04  
% 2.78/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.04  
% 2.78/1.04  ------  iProver source info
% 2.78/1.04  
% 2.78/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.04  git: non_committed_changes: false
% 2.78/1.04  git: last_make_outside_of_git: false
% 2.78/1.04  
% 2.78/1.04  ------ 
% 2.78/1.04  
% 2.78/1.04  ------ Input Options
% 2.78/1.04  
% 2.78/1.04  --out_options                           all
% 2.78/1.04  --tptp_safe_out                         true
% 2.78/1.04  --problem_path                          ""
% 2.78/1.04  --include_path                          ""
% 2.78/1.04  --clausifier                            res/vclausify_rel
% 2.78/1.04  --clausifier_options                    --mode clausify
% 2.78/1.04  --stdin                                 false
% 2.78/1.04  --stats_out                             all
% 2.78/1.04  
% 2.78/1.04  ------ General Options
% 2.78/1.04  
% 2.78/1.04  --fof                                   false
% 2.78/1.04  --time_out_real                         305.
% 2.78/1.04  --time_out_virtual                      -1.
% 2.78/1.04  --symbol_type_check                     false
% 2.78/1.04  --clausify_out                          false
% 2.78/1.04  --sig_cnt_out                           false
% 2.78/1.04  --trig_cnt_out                          false
% 2.78/1.04  --trig_cnt_out_tolerance                1.
% 2.78/1.04  --trig_cnt_out_sk_spl                   false
% 2.78/1.04  --abstr_cl_out                          false
% 2.78/1.04  
% 2.78/1.04  ------ Global Options
% 2.78/1.04  
% 2.78/1.04  --schedule                              default
% 2.78/1.04  --add_important_lit                     false
% 2.78/1.04  --prop_solver_per_cl                    1000
% 2.78/1.04  --min_unsat_core                        false
% 2.78/1.04  --soft_assumptions                      false
% 2.78/1.04  --soft_lemma_size                       3
% 2.78/1.04  --prop_impl_unit_size                   0
% 2.78/1.04  --prop_impl_unit                        []
% 2.78/1.04  --share_sel_clauses                     true
% 2.78/1.04  --reset_solvers                         false
% 2.78/1.04  --bc_imp_inh                            [conj_cone]
% 2.78/1.04  --conj_cone_tolerance                   3.
% 2.78/1.04  --extra_neg_conj                        none
% 2.78/1.04  --large_theory_mode                     true
% 2.78/1.04  --prolific_symb_bound                   200
% 2.78/1.04  --lt_threshold                          2000
% 2.78/1.04  --clause_weak_htbl                      true
% 2.78/1.04  --gc_record_bc_elim                     false
% 2.78/1.04  
% 2.78/1.04  ------ Preprocessing Options
% 2.78/1.04  
% 2.78/1.04  --preprocessing_flag                    true
% 2.78/1.04  --time_out_prep_mult                    0.1
% 2.78/1.04  --splitting_mode                        input
% 2.78/1.04  --splitting_grd                         true
% 2.78/1.04  --splitting_cvd                         false
% 2.78/1.04  --splitting_cvd_svl                     false
% 2.78/1.04  --splitting_nvd                         32
% 2.78/1.04  --sub_typing                            true
% 2.78/1.04  --prep_gs_sim                           true
% 2.78/1.04  --prep_unflatten                        true
% 2.78/1.04  --prep_res_sim                          true
% 2.78/1.04  --prep_upred                            true
% 2.78/1.04  --prep_sem_filter                       exhaustive
% 2.78/1.04  --prep_sem_filter_out                   false
% 2.78/1.04  --pred_elim                             true
% 2.78/1.04  --res_sim_input                         true
% 2.78/1.04  --eq_ax_congr_red                       true
% 2.78/1.04  --pure_diseq_elim                       true
% 2.78/1.04  --brand_transform                       false
% 2.78/1.04  --non_eq_to_eq                          false
% 2.78/1.04  --prep_def_merge                        true
% 2.78/1.04  --prep_def_merge_prop_impl              false
% 2.78/1.04  --prep_def_merge_mbd                    true
% 2.78/1.04  --prep_def_merge_tr_red                 false
% 2.78/1.04  --prep_def_merge_tr_cl                  false
% 2.78/1.04  --smt_preprocessing                     true
% 2.78/1.04  --smt_ac_axioms                         fast
% 2.78/1.04  --preprocessed_out                      false
% 2.78/1.04  --preprocessed_stats                    false
% 2.78/1.04  
% 2.78/1.04  ------ Abstraction refinement Options
% 2.78/1.04  
% 2.78/1.04  --abstr_ref                             []
% 2.78/1.04  --abstr_ref_prep                        false
% 2.78/1.04  --abstr_ref_until_sat                   false
% 2.78/1.04  --abstr_ref_sig_restrict                funpre
% 2.78/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.04  --abstr_ref_under                       []
% 2.78/1.04  
% 2.78/1.04  ------ SAT Options
% 2.78/1.04  
% 2.78/1.04  --sat_mode                              false
% 2.78/1.04  --sat_fm_restart_options                ""
% 2.78/1.04  --sat_gr_def                            false
% 2.78/1.04  --sat_epr_types                         true
% 2.78/1.04  --sat_non_cyclic_types                  false
% 2.78/1.04  --sat_finite_models                     false
% 2.78/1.04  --sat_fm_lemmas                         false
% 2.78/1.04  --sat_fm_prep                           false
% 2.78/1.04  --sat_fm_uc_incr                        true
% 2.78/1.04  --sat_out_model                         small
% 2.78/1.04  --sat_out_clauses                       false
% 2.78/1.04  
% 2.78/1.04  ------ QBF Options
% 2.78/1.04  
% 2.78/1.04  --qbf_mode                              false
% 2.78/1.04  --qbf_elim_univ                         false
% 2.78/1.04  --qbf_dom_inst                          none
% 2.78/1.04  --qbf_dom_pre_inst                      false
% 2.78/1.04  --qbf_sk_in                             false
% 2.78/1.04  --qbf_pred_elim                         true
% 2.78/1.04  --qbf_split                             512
% 2.78/1.04  
% 2.78/1.04  ------ BMC1 Options
% 2.78/1.04  
% 2.78/1.04  --bmc1_incremental                      false
% 2.78/1.04  --bmc1_axioms                           reachable_all
% 2.78/1.04  --bmc1_min_bound                        0
% 2.78/1.04  --bmc1_max_bound                        -1
% 2.78/1.04  --bmc1_max_bound_default                -1
% 2.78/1.04  --bmc1_symbol_reachability              true
% 2.78/1.04  --bmc1_property_lemmas                  false
% 2.78/1.04  --bmc1_k_induction                      false
% 2.78/1.04  --bmc1_non_equiv_states                 false
% 2.78/1.04  --bmc1_deadlock                         false
% 2.78/1.04  --bmc1_ucm                              false
% 2.78/1.04  --bmc1_add_unsat_core                   none
% 2.78/1.04  --bmc1_unsat_core_children              false
% 2.78/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.04  --bmc1_out_stat                         full
% 2.78/1.04  --bmc1_ground_init                      false
% 2.78/1.04  --bmc1_pre_inst_next_state              false
% 2.78/1.04  --bmc1_pre_inst_state                   false
% 2.78/1.04  --bmc1_pre_inst_reach_state             false
% 2.78/1.04  --bmc1_out_unsat_core                   false
% 2.78/1.04  --bmc1_aig_witness_out                  false
% 2.78/1.04  --bmc1_verbose                          false
% 2.78/1.04  --bmc1_dump_clauses_tptp                false
% 2.78/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.04  --bmc1_dump_file                        -
% 2.78/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.04  --bmc1_ucm_extend_mode                  1
% 2.78/1.04  --bmc1_ucm_init_mode                    2
% 2.78/1.04  --bmc1_ucm_cone_mode                    none
% 2.78/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.04  --bmc1_ucm_relax_model                  4
% 2.78/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.04  --bmc1_ucm_layered_model                none
% 2.78/1.04  --bmc1_ucm_max_lemma_size               10
% 2.78/1.04  
% 2.78/1.04  ------ AIG Options
% 2.78/1.04  
% 2.78/1.04  --aig_mode                              false
% 2.78/1.04  
% 2.78/1.04  ------ Instantiation Options
% 2.78/1.04  
% 2.78/1.04  --instantiation_flag                    true
% 2.78/1.04  --inst_sos_flag                         false
% 2.78/1.04  --inst_sos_phase                        true
% 2.78/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.04  --inst_lit_sel_side                     num_symb
% 2.78/1.04  --inst_solver_per_active                1400
% 2.78/1.04  --inst_solver_calls_frac                1.
% 2.78/1.04  --inst_passive_queue_type               priority_queues
% 2.78/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.04  --inst_passive_queues_freq              [25;2]
% 2.78/1.04  --inst_dismatching                      true
% 2.78/1.04  --inst_eager_unprocessed_to_passive     true
% 2.78/1.04  --inst_prop_sim_given                   true
% 2.78/1.04  --inst_prop_sim_new                     false
% 2.78/1.04  --inst_subs_new                         false
% 2.78/1.04  --inst_eq_res_simp                      false
% 2.78/1.04  --inst_subs_given                       false
% 2.78/1.04  --inst_orphan_elimination               true
% 2.78/1.04  --inst_learning_loop_flag               true
% 2.78/1.04  --inst_learning_start                   3000
% 2.78/1.04  --inst_learning_factor                  2
% 2.78/1.04  --inst_start_prop_sim_after_learn       3
% 2.78/1.04  --inst_sel_renew                        solver
% 2.78/1.04  --inst_lit_activity_flag                true
% 2.78/1.04  --inst_restr_to_given                   false
% 2.78/1.04  --inst_activity_threshold               500
% 2.78/1.04  --inst_out_proof                        true
% 2.78/1.04  
% 2.78/1.04  ------ Resolution Options
% 2.78/1.04  
% 2.78/1.04  --resolution_flag                       true
% 2.78/1.04  --res_lit_sel                           adaptive
% 2.78/1.04  --res_lit_sel_side                      none
% 2.78/1.04  --res_ordering                          kbo
% 2.78/1.04  --res_to_prop_solver                    active
% 2.78/1.04  --res_prop_simpl_new                    false
% 2.78/1.04  --res_prop_simpl_given                  true
% 2.78/1.04  --res_passive_queue_type                priority_queues
% 2.78/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.04  --res_passive_queues_freq               [15;5]
% 2.78/1.04  --res_forward_subs                      full
% 2.78/1.04  --res_backward_subs                     full
% 2.78/1.04  --res_forward_subs_resolution           true
% 2.78/1.04  --res_backward_subs_resolution          true
% 2.78/1.04  --res_orphan_elimination                true
% 2.78/1.04  --res_time_limit                        2.
% 2.78/1.04  --res_out_proof                         true
% 2.78/1.04  
% 2.78/1.04  ------ Superposition Options
% 2.78/1.04  
% 2.78/1.04  --superposition_flag                    true
% 2.78/1.04  --sup_passive_queue_type                priority_queues
% 2.78/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.04  --demod_completeness_check              fast
% 2.78/1.04  --demod_use_ground                      true
% 2.78/1.04  --sup_to_prop_solver                    passive
% 2.78/1.04  --sup_prop_simpl_new                    true
% 2.78/1.04  --sup_prop_simpl_given                  true
% 2.78/1.04  --sup_fun_splitting                     false
% 2.78/1.04  --sup_smt_interval                      50000
% 2.78/1.04  
% 2.78/1.04  ------ Superposition Simplification Setup
% 2.78/1.04  
% 2.78/1.04  --sup_indices_passive                   []
% 2.78/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.04  --sup_full_bw                           [BwDemod]
% 2.78/1.04  --sup_immed_triv                        [TrivRules]
% 2.78/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.04  --sup_immed_bw_main                     []
% 2.78/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.04  
% 2.78/1.04  ------ Combination Options
% 2.78/1.04  
% 2.78/1.04  --comb_res_mult                         3
% 2.78/1.04  --comb_sup_mult                         2
% 2.78/1.04  --comb_inst_mult                        10
% 2.78/1.04  
% 2.78/1.04  ------ Debug Options
% 2.78/1.04  
% 2.78/1.04  --dbg_backtrace                         false
% 2.78/1.04  --dbg_dump_prop_clauses                 false
% 2.78/1.04  --dbg_dump_prop_clauses_file            -
% 2.78/1.04  --dbg_out_stat                          false
% 2.78/1.04  ------ Parsing...
% 2.78/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.04  
% 2.78/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.78/1.04  
% 2.78/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.04  
% 2.78/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.04  ------ Proving...
% 2.78/1.04  ------ Problem Properties 
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  clauses                                 31
% 2.78/1.04  conjectures                             6
% 2.78/1.04  EPR                                     9
% 2.78/1.04  Horn                                    30
% 2.78/1.04  unary                                   15
% 2.78/1.04  binary                                  3
% 2.78/1.04  lits                                    77
% 2.78/1.04  lits eq                                 8
% 2.78/1.04  fd_pure                                 0
% 2.78/1.04  fd_pseudo                               0
% 2.78/1.04  fd_cond                                 1
% 2.78/1.04  fd_pseudo_cond                          2
% 2.78/1.04  AC symbols                              0
% 2.78/1.04  
% 2.78/1.04  ------ Schedule dynamic 5 is on 
% 2.78/1.04  
% 2.78/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  ------ 
% 2.78/1.04  Current options:
% 2.78/1.04  ------ 
% 2.78/1.04  
% 2.78/1.04  ------ Input Options
% 2.78/1.04  
% 2.78/1.04  --out_options                           all
% 2.78/1.04  --tptp_safe_out                         true
% 2.78/1.04  --problem_path                          ""
% 2.78/1.04  --include_path                          ""
% 2.78/1.04  --clausifier                            res/vclausify_rel
% 2.78/1.04  --clausifier_options                    --mode clausify
% 2.78/1.04  --stdin                                 false
% 2.78/1.04  --stats_out                             all
% 2.78/1.04  
% 2.78/1.04  ------ General Options
% 2.78/1.04  
% 2.78/1.04  --fof                                   false
% 2.78/1.04  --time_out_real                         305.
% 2.78/1.04  --time_out_virtual                      -1.
% 2.78/1.04  --symbol_type_check                     false
% 2.78/1.04  --clausify_out                          false
% 2.78/1.04  --sig_cnt_out                           false
% 2.78/1.04  --trig_cnt_out                          false
% 2.78/1.04  --trig_cnt_out_tolerance                1.
% 2.78/1.04  --trig_cnt_out_sk_spl                   false
% 2.78/1.04  --abstr_cl_out                          false
% 2.78/1.04  
% 2.78/1.04  ------ Global Options
% 2.78/1.04  
% 2.78/1.04  --schedule                              default
% 2.78/1.04  --add_important_lit                     false
% 2.78/1.04  --prop_solver_per_cl                    1000
% 2.78/1.04  --min_unsat_core                        false
% 2.78/1.04  --soft_assumptions                      false
% 2.78/1.04  --soft_lemma_size                       3
% 2.78/1.04  --prop_impl_unit_size                   0
% 2.78/1.04  --prop_impl_unit                        []
% 2.78/1.04  --share_sel_clauses                     true
% 2.78/1.04  --reset_solvers                         false
% 2.78/1.04  --bc_imp_inh                            [conj_cone]
% 2.78/1.04  --conj_cone_tolerance                   3.
% 2.78/1.04  --extra_neg_conj                        none
% 2.78/1.04  --large_theory_mode                     true
% 2.78/1.04  --prolific_symb_bound                   200
% 2.78/1.04  --lt_threshold                          2000
% 2.78/1.04  --clause_weak_htbl                      true
% 2.78/1.04  --gc_record_bc_elim                     false
% 2.78/1.04  
% 2.78/1.04  ------ Preprocessing Options
% 2.78/1.04  
% 2.78/1.04  --preprocessing_flag                    true
% 2.78/1.04  --time_out_prep_mult                    0.1
% 2.78/1.04  --splitting_mode                        input
% 2.78/1.04  --splitting_grd                         true
% 2.78/1.04  --splitting_cvd                         false
% 2.78/1.04  --splitting_cvd_svl                     false
% 2.78/1.04  --splitting_nvd                         32
% 2.78/1.04  --sub_typing                            true
% 2.78/1.04  --prep_gs_sim                           true
% 2.78/1.04  --prep_unflatten                        true
% 2.78/1.04  --prep_res_sim                          true
% 2.78/1.04  --prep_upred                            true
% 2.78/1.04  --prep_sem_filter                       exhaustive
% 2.78/1.04  --prep_sem_filter_out                   false
% 2.78/1.04  --pred_elim                             true
% 2.78/1.04  --res_sim_input                         true
% 2.78/1.04  --eq_ax_congr_red                       true
% 2.78/1.04  --pure_diseq_elim                       true
% 2.78/1.04  --brand_transform                       false
% 2.78/1.04  --non_eq_to_eq                          false
% 2.78/1.04  --prep_def_merge                        true
% 2.78/1.04  --prep_def_merge_prop_impl              false
% 2.78/1.04  --prep_def_merge_mbd                    true
% 2.78/1.04  --prep_def_merge_tr_red                 false
% 2.78/1.04  --prep_def_merge_tr_cl                  false
% 2.78/1.04  --smt_preprocessing                     true
% 2.78/1.04  --smt_ac_axioms                         fast
% 2.78/1.04  --preprocessed_out                      false
% 2.78/1.04  --preprocessed_stats                    false
% 2.78/1.04  
% 2.78/1.04  ------ Abstraction refinement Options
% 2.78/1.04  
% 2.78/1.04  --abstr_ref                             []
% 2.78/1.04  --abstr_ref_prep                        false
% 2.78/1.04  --abstr_ref_until_sat                   false
% 2.78/1.04  --abstr_ref_sig_restrict                funpre
% 2.78/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.04  --abstr_ref_under                       []
% 2.78/1.04  
% 2.78/1.04  ------ SAT Options
% 2.78/1.04  
% 2.78/1.04  --sat_mode                              false
% 2.78/1.04  --sat_fm_restart_options                ""
% 2.78/1.04  --sat_gr_def                            false
% 2.78/1.04  --sat_epr_types                         true
% 2.78/1.04  --sat_non_cyclic_types                  false
% 2.78/1.04  --sat_finite_models                     false
% 2.78/1.04  --sat_fm_lemmas                         false
% 2.78/1.04  --sat_fm_prep                           false
% 2.78/1.04  --sat_fm_uc_incr                        true
% 2.78/1.04  --sat_out_model                         small
% 2.78/1.04  --sat_out_clauses                       false
% 2.78/1.04  
% 2.78/1.04  ------ QBF Options
% 2.78/1.04  
% 2.78/1.04  --qbf_mode                              false
% 2.78/1.04  --qbf_elim_univ                         false
% 2.78/1.04  --qbf_dom_inst                          none
% 2.78/1.04  --qbf_dom_pre_inst                      false
% 2.78/1.04  --qbf_sk_in                             false
% 2.78/1.04  --qbf_pred_elim                         true
% 2.78/1.04  --qbf_split                             512
% 2.78/1.04  
% 2.78/1.04  ------ BMC1 Options
% 2.78/1.04  
% 2.78/1.04  --bmc1_incremental                      false
% 2.78/1.04  --bmc1_axioms                           reachable_all
% 2.78/1.04  --bmc1_min_bound                        0
% 2.78/1.04  --bmc1_max_bound                        -1
% 2.78/1.04  --bmc1_max_bound_default                -1
% 2.78/1.04  --bmc1_symbol_reachability              true
% 2.78/1.04  --bmc1_property_lemmas                  false
% 2.78/1.04  --bmc1_k_induction                      false
% 2.78/1.04  --bmc1_non_equiv_states                 false
% 2.78/1.04  --bmc1_deadlock                         false
% 2.78/1.04  --bmc1_ucm                              false
% 2.78/1.04  --bmc1_add_unsat_core                   none
% 2.78/1.04  --bmc1_unsat_core_children              false
% 2.78/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.04  --bmc1_out_stat                         full
% 2.78/1.04  --bmc1_ground_init                      false
% 2.78/1.04  --bmc1_pre_inst_next_state              false
% 2.78/1.04  --bmc1_pre_inst_state                   false
% 2.78/1.04  --bmc1_pre_inst_reach_state             false
% 2.78/1.04  --bmc1_out_unsat_core                   false
% 2.78/1.04  --bmc1_aig_witness_out                  false
% 2.78/1.04  --bmc1_verbose                          false
% 2.78/1.04  --bmc1_dump_clauses_tptp                false
% 2.78/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.04  --bmc1_dump_file                        -
% 2.78/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.04  --bmc1_ucm_extend_mode                  1
% 2.78/1.04  --bmc1_ucm_init_mode                    2
% 2.78/1.04  --bmc1_ucm_cone_mode                    none
% 2.78/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.04  --bmc1_ucm_relax_model                  4
% 2.78/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.04  --bmc1_ucm_layered_model                none
% 2.78/1.04  --bmc1_ucm_max_lemma_size               10
% 2.78/1.04  
% 2.78/1.04  ------ AIG Options
% 2.78/1.04  
% 2.78/1.04  --aig_mode                              false
% 2.78/1.04  
% 2.78/1.04  ------ Instantiation Options
% 2.78/1.04  
% 2.78/1.04  --instantiation_flag                    true
% 2.78/1.04  --inst_sos_flag                         false
% 2.78/1.04  --inst_sos_phase                        true
% 2.78/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.04  --inst_lit_sel_side                     none
% 2.78/1.04  --inst_solver_per_active                1400
% 2.78/1.04  --inst_solver_calls_frac                1.
% 2.78/1.04  --inst_passive_queue_type               priority_queues
% 2.78/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.04  --inst_passive_queues_freq              [25;2]
% 2.78/1.04  --inst_dismatching                      true
% 2.78/1.04  --inst_eager_unprocessed_to_passive     true
% 2.78/1.04  --inst_prop_sim_given                   true
% 2.78/1.04  --inst_prop_sim_new                     false
% 2.78/1.04  --inst_subs_new                         false
% 2.78/1.04  --inst_eq_res_simp                      false
% 2.78/1.04  --inst_subs_given                       false
% 2.78/1.04  --inst_orphan_elimination               true
% 2.78/1.04  --inst_learning_loop_flag               true
% 2.78/1.04  --inst_learning_start                   3000
% 2.78/1.04  --inst_learning_factor                  2
% 2.78/1.04  --inst_start_prop_sim_after_learn       3
% 2.78/1.04  --inst_sel_renew                        solver
% 2.78/1.04  --inst_lit_activity_flag                true
% 2.78/1.04  --inst_restr_to_given                   false
% 2.78/1.04  --inst_activity_threshold               500
% 2.78/1.04  --inst_out_proof                        true
% 2.78/1.04  
% 2.78/1.04  ------ Resolution Options
% 2.78/1.04  
% 2.78/1.04  --resolution_flag                       false
% 2.78/1.04  --res_lit_sel                           adaptive
% 2.78/1.04  --res_lit_sel_side                      none
% 2.78/1.04  --res_ordering                          kbo
% 2.78/1.04  --res_to_prop_solver                    active
% 2.78/1.04  --res_prop_simpl_new                    false
% 2.78/1.04  --res_prop_simpl_given                  true
% 2.78/1.04  --res_passive_queue_type                priority_queues
% 2.78/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.04  --res_passive_queues_freq               [15;5]
% 2.78/1.04  --res_forward_subs                      full
% 2.78/1.04  --res_backward_subs                     full
% 2.78/1.04  --res_forward_subs_resolution           true
% 2.78/1.04  --res_backward_subs_resolution          true
% 2.78/1.04  --res_orphan_elimination                true
% 2.78/1.04  --res_time_limit                        2.
% 2.78/1.04  --res_out_proof                         true
% 2.78/1.04  
% 2.78/1.04  ------ Superposition Options
% 2.78/1.04  
% 2.78/1.04  --superposition_flag                    true
% 2.78/1.04  --sup_passive_queue_type                priority_queues
% 2.78/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.04  --demod_completeness_check              fast
% 2.78/1.04  --demod_use_ground                      true
% 2.78/1.04  --sup_to_prop_solver                    passive
% 2.78/1.04  --sup_prop_simpl_new                    true
% 2.78/1.04  --sup_prop_simpl_given                  true
% 2.78/1.04  --sup_fun_splitting                     false
% 2.78/1.04  --sup_smt_interval                      50000
% 2.78/1.04  
% 2.78/1.04  ------ Superposition Simplification Setup
% 2.78/1.04  
% 2.78/1.04  --sup_indices_passive                   []
% 2.78/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.04  --sup_full_bw                           [BwDemod]
% 2.78/1.04  --sup_immed_triv                        [TrivRules]
% 2.78/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.04  --sup_immed_bw_main                     []
% 2.78/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.04  
% 2.78/1.04  ------ Combination Options
% 2.78/1.04  
% 2.78/1.04  --comb_res_mult                         3
% 2.78/1.04  --comb_sup_mult                         2
% 2.78/1.04  --comb_inst_mult                        10
% 2.78/1.04  
% 2.78/1.04  ------ Debug Options
% 2.78/1.04  
% 2.78/1.04  --dbg_backtrace                         false
% 2.78/1.04  --dbg_dump_prop_clauses                 false
% 2.78/1.04  --dbg_dump_prop_clauses_file            -
% 2.78/1.04  --dbg_out_stat                          false
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  ------ Proving...
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  % SZS status Theorem for theBenchmark.p
% 2.78/1.04  
% 2.78/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.04  
% 2.78/1.04  fof(f23,conjecture,(
% 2.78/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f24,negated_conjecture,(
% 2.78/1.04    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.78/1.04    inference(negated_conjecture,[],[f23])).
% 2.78/1.04  
% 2.78/1.04  fof(f46,plain,(
% 2.78/1.04    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.78/1.04    inference(ennf_transformation,[],[f24])).
% 2.78/1.04  
% 2.78/1.04  fof(f47,plain,(
% 2.78/1.04    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.78/1.04    inference(flattening,[],[f46])).
% 2.78/1.04  
% 2.78/1.04  fof(f54,plain,(
% 2.78/1.04    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.78/1.04    introduced(choice_axiom,[])).
% 2.78/1.04  
% 2.78/1.04  fof(f53,plain,(
% 2.78/1.04    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.78/1.04    introduced(choice_axiom,[])).
% 2.78/1.04  
% 2.78/1.04  fof(f55,plain,(
% 2.78/1.04    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.78/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f54,f53])).
% 2.78/1.04  
% 2.78/1.04  fof(f89,plain,(
% 2.78/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.78/1.04    inference(cnf_transformation,[],[f55])).
% 2.78/1.04  
% 2.78/1.04  fof(f92,plain,(
% 2.78/1.04    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.78/1.04    inference(cnf_transformation,[],[f55])).
% 2.78/1.04  
% 2.78/1.04  fof(f20,axiom,(
% 2.78/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f42,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.78/1.04    inference(ennf_transformation,[],[f20])).
% 2.78/1.04  
% 2.78/1.04  fof(f43,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.78/1.04    inference(flattening,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  fof(f83,plain,(
% 2.78/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f43])).
% 2.78/1.04  
% 2.78/1.04  fof(f90,plain,(
% 2.78/1.04    v1_funct_1(sK3)),
% 2.78/1.04    inference(cnf_transformation,[],[f55])).
% 2.78/1.04  
% 2.78/1.04  fof(f87,plain,(
% 2.78/1.04    v1_funct_1(sK2)),
% 2.78/1.04    inference(cnf_transformation,[],[f55])).
% 2.78/1.04  
% 2.78/1.04  fof(f16,axiom,(
% 2.78/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f36,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.78/1.04    inference(ennf_transformation,[],[f16])).
% 2.78/1.04  
% 2.78/1.04  fof(f37,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.04    inference(flattening,[],[f36])).
% 2.78/1.04  
% 2.78/1.04  fof(f51,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.04    inference(nnf_transformation,[],[f37])).
% 2.78/1.04  
% 2.78/1.04  fof(f76,plain,(
% 2.78/1.04    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.04    inference(cnf_transformation,[],[f51])).
% 2.78/1.04  
% 2.78/1.04  fof(f93,plain,(
% 2.78/1.04    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.78/1.04    inference(cnf_transformation,[],[f55])).
% 2.78/1.04  
% 2.78/1.04  fof(f17,axiom,(
% 2.78/1.04    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f78,plain,(
% 2.78/1.04    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.78/1.04    inference(cnf_transformation,[],[f17])).
% 2.78/1.04  
% 2.78/1.04  fof(f21,axiom,(
% 2.78/1.04    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f84,plain,(
% 2.78/1.04    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f21])).
% 2.78/1.04  
% 2.78/1.04  fof(f99,plain,(
% 2.78/1.04    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.78/1.04    inference(definition_unfolding,[],[f78,f84])).
% 2.78/1.04  
% 2.78/1.04  fof(f19,axiom,(
% 2.78/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f40,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.78/1.04    inference(ennf_transformation,[],[f19])).
% 2.78/1.04  
% 2.78/1.04  fof(f41,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.78/1.04    inference(flattening,[],[f40])).
% 2.78/1.04  
% 2.78/1.04  fof(f82,plain,(
% 2.78/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f41])).
% 2.78/1.04  
% 2.78/1.04  fof(f22,axiom,(
% 2.78/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f44,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.78/1.04    inference(ennf_transformation,[],[f22])).
% 2.78/1.04  
% 2.78/1.04  fof(f45,plain,(
% 2.78/1.04    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.78/1.04    inference(flattening,[],[f44])).
% 2.78/1.04  
% 2.78/1.04  fof(f85,plain,(
% 2.78/1.04    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f45])).
% 2.78/1.04  
% 2.78/1.04  fof(f12,axiom,(
% 2.78/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f34,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.78/1.04    inference(ennf_transformation,[],[f12])).
% 2.78/1.04  
% 2.78/1.04  fof(f70,plain,(
% 2.78/1.04    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f34])).
% 2.78/1.04  
% 2.78/1.04  fof(f13,axiom,(
% 2.78/1.04    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f72,plain,(
% 2.78/1.04    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.78/1.04    inference(cnf_transformation,[],[f13])).
% 2.78/1.04  
% 2.78/1.04  fof(f95,plain,(
% 2.78/1.04    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.78/1.04    inference(definition_unfolding,[],[f72,f84])).
% 2.78/1.04  
% 2.78/1.04  fof(f15,axiom,(
% 2.78/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f25,plain,(
% 2.78/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.78/1.04    inference(pure_predicate_removal,[],[f15])).
% 2.78/1.04  
% 2.78/1.04  fof(f35,plain,(
% 2.78/1.04    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.04    inference(ennf_transformation,[],[f25])).
% 2.78/1.04  
% 2.78/1.04  fof(f75,plain,(
% 2.78/1.04    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.04    inference(cnf_transformation,[],[f35])).
% 2.78/1.04  
% 2.78/1.04  fof(f9,axiom,(
% 2.78/1.04    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f31,plain,(
% 2.78/1.04    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.78/1.04    inference(ennf_transformation,[],[f9])).
% 2.78/1.04  
% 2.78/1.04  fof(f50,plain,(
% 2.78/1.04    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.78/1.04    inference(nnf_transformation,[],[f31])).
% 2.78/1.04  
% 2.78/1.04  fof(f66,plain,(
% 2.78/1.04    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f50])).
% 2.78/1.04  
% 2.78/1.04  fof(f2,axiom,(
% 2.78/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f48,plain,(
% 2.78/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/1.04    inference(nnf_transformation,[],[f2])).
% 2.78/1.04  
% 2.78/1.04  fof(f49,plain,(
% 2.78/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/1.04    inference(flattening,[],[f48])).
% 2.78/1.04  
% 2.78/1.04  fof(f59,plain,(
% 2.78/1.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f49])).
% 2.78/1.04  
% 2.78/1.04  fof(f8,axiom,(
% 2.78/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f30,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.78/1.04    inference(ennf_transformation,[],[f8])).
% 2.78/1.04  
% 2.78/1.04  fof(f65,plain,(
% 2.78/1.04    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f30])).
% 2.78/1.04  
% 2.78/1.04  fof(f10,axiom,(
% 2.78/1.04    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f68,plain,(
% 2.78/1.04    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.78/1.04    inference(cnf_transformation,[],[f10])).
% 2.78/1.04  
% 2.78/1.04  fof(f6,axiom,(
% 2.78/1.04    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f28,plain,(
% 2.78/1.04    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.78/1.04    inference(ennf_transformation,[],[f6])).
% 2.78/1.04  
% 2.78/1.04  fof(f63,plain,(
% 2.78/1.04    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f28])).
% 2.78/1.04  
% 2.78/1.04  fof(f7,axiom,(
% 2.78/1.04    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f29,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.78/1.04    inference(ennf_transformation,[],[f7])).
% 2.78/1.04  
% 2.78/1.04  fof(f64,plain,(
% 2.78/1.04    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f29])).
% 2.78/1.04  
% 2.78/1.04  fof(f11,axiom,(
% 2.78/1.04    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f32,plain,(
% 2.78/1.04    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.78/1.04    inference(ennf_transformation,[],[f11])).
% 2.78/1.04  
% 2.78/1.04  fof(f33,plain,(
% 2.78/1.04    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.78/1.04    inference(flattening,[],[f32])).
% 2.78/1.04  
% 2.78/1.04  fof(f69,plain,(
% 2.78/1.04    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f33])).
% 2.78/1.04  
% 2.78/1.04  fof(f4,axiom,(
% 2.78/1.04    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f26,plain,(
% 2.78/1.04    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.78/1.04    inference(ennf_transformation,[],[f4])).
% 2.78/1.04  
% 2.78/1.04  fof(f61,plain,(
% 2.78/1.04    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f26])).
% 2.78/1.04  
% 2.78/1.04  fof(f67,plain,(
% 2.78/1.04    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f50])).
% 2.78/1.04  
% 2.78/1.04  fof(f18,axiom,(
% 2.78/1.04    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f38,plain,(
% 2.78/1.04    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.78/1.04    inference(ennf_transformation,[],[f18])).
% 2.78/1.04  
% 2.78/1.04  fof(f39,plain,(
% 2.78/1.04    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/1.04    inference(flattening,[],[f38])).
% 2.78/1.04  
% 2.78/1.04  fof(f52,plain,(
% 2.78/1.04    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/1.04    inference(nnf_transformation,[],[f39])).
% 2.78/1.04  
% 2.78/1.04  fof(f80,plain,(
% 2.78/1.04    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f52])).
% 2.78/1.04  
% 2.78/1.04  fof(f103,plain,(
% 2.78/1.04    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.78/1.04    inference(equality_resolution,[],[f80])).
% 2.78/1.04  
% 2.78/1.04  fof(f94,plain,(
% 2.78/1.04    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.78/1.04    inference(cnf_transformation,[],[f55])).
% 2.78/1.04  
% 2.78/1.04  fof(f58,plain,(
% 2.78/1.04    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.78/1.04    inference(cnf_transformation,[],[f49])).
% 2.78/1.04  
% 2.78/1.04  fof(f100,plain,(
% 2.78/1.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.78/1.04    inference(equality_resolution,[],[f58])).
% 2.78/1.04  
% 2.78/1.04  fof(f1,axiom,(
% 2.78/1.04    v1_xboole_0(k1_xboole_0)),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f56,plain,(
% 2.78/1.04    v1_xboole_0(k1_xboole_0)),
% 2.78/1.04    inference(cnf_transformation,[],[f1])).
% 2.78/1.04  
% 2.78/1.04  fof(f14,axiom,(
% 2.78/1.04    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.78/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f74,plain,(
% 2.78/1.04    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.78/1.04    inference(cnf_transformation,[],[f14])).
% 2.78/1.04  
% 2.78/1.04  fof(f97,plain,(
% 2.78/1.04    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.78/1.04    inference(definition_unfolding,[],[f74,f84])).
% 2.78/1.04  
% 2.78/1.04  fof(f73,plain,(
% 2.78/1.04    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.78/1.04    inference(cnf_transformation,[],[f14])).
% 2.78/1.04  
% 2.78/1.04  fof(f98,plain,(
% 2.78/1.04    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.78/1.04    inference(definition_unfolding,[],[f73,f84])).
% 2.78/1.04  
% 2.78/1.04  fof(f91,plain,(
% 2.78/1.04    v1_funct_2(sK3,sK1,sK0)),
% 2.78/1.04    inference(cnf_transformation,[],[f55])).
% 2.78/1.04  
% 2.78/1.04  fof(f88,plain,(
% 2.78/1.04    v1_funct_2(sK2,sK0,sK1)),
% 2.78/1.04    inference(cnf_transformation,[],[f55])).
% 2.78/1.04  
% 2.78/1.04  cnf(c_698,plain,
% 2.78/1.04      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.78/1.04      theory(equality) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_7529,plain,
% 2.78/1.04      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_698]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_7531,plain,
% 2.78/1.04      ( v2_funct_1(sK2) | ~ v2_funct_1(sK0) | sK2 != sK0 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_7529]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_35,negated_conjecture,
% 2.78/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.78/1.04      inference(cnf_transformation,[],[f89]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1225,plain,
% 2.78/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_32,negated_conjecture,
% 2.78/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.78/1.04      inference(cnf_transformation,[],[f92]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1228,plain,
% 2.78/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_27,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.78/1.04      | ~ v1_funct_1(X0)
% 2.78/1.04      | ~ v1_funct_1(X3)
% 2.78/1.04      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f83]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1231,plain,
% 2.78/1.04      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.78/1.04      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.78/1.04      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.78/1.04      | v1_funct_1(X5) != iProver_top
% 2.78/1.04      | v1_funct_1(X4) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4211,plain,
% 2.78/1.04      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 2.78/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.78/1.04      | v1_funct_1(X2) != iProver_top
% 2.78/1.04      | v1_funct_1(sK3) != iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_1228,c_1231]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_34,negated_conjecture,
% 2.78/1.04      ( v1_funct_1(sK3) ),
% 2.78/1.04      inference(cnf_transformation,[],[f90]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_41,plain,
% 2.78/1.04      ( v1_funct_1(sK3) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4380,plain,
% 2.78/1.04      ( v1_funct_1(X2) != iProver_top
% 2.78/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.78/1.04      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_4211,c_41]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4381,plain,
% 2.78/1.04      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 2.78/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.78/1.04      | v1_funct_1(X2) != iProver_top ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_4380]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4392,plain,
% 2.78/1.04      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 2.78/1.04      | v1_funct_1(sK2) != iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_1225,c_4381]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_37,negated_conjecture,
% 2.78/1.04      ( v1_funct_1(sK2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f87]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1585,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.78/1.04      | ~ v1_funct_1(X0)
% 2.78/1.04      | ~ v1_funct_1(sK3)
% 2.78/1.04      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_27]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1850,plain,
% 2.78/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.78/1.04      | ~ v1_funct_1(sK2)
% 2.78/1.04      | ~ v1_funct_1(sK3)
% 2.78/1.04      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1585]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2402,plain,
% 2.78/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.78/1.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.04      | ~ v1_funct_1(sK2)
% 2.78/1.04      | ~ v1_funct_1(sK3)
% 2.78/1.04      | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1850]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3803,plain,
% 2.78/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.78/1.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.78/1.04      | ~ v1_funct_1(sK2)
% 2.78/1.04      | ~ v1_funct_1(sK3)
% 2.78/1.04      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_2402]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4571,plain,
% 2.78/1.04      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_4392,c_37,c_35,c_34,c_32,c_3803]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_21,plain,
% 2.78/1.04      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.78/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.04      | X3 = X2 ),
% 2.78/1.04      inference(cnf_transformation,[],[f76]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_31,negated_conjecture,
% 2.78/1.04      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.78/1.04      inference(cnf_transformation,[],[f93]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_396,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.04      | X3 = X0
% 2.78/1.04      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.78/1.04      | k6_partfun1(sK0) != X3
% 2.78/1.04      | sK0 != X2
% 2.78/1.04      | sK0 != X1 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_397,plain,
% 2.78/1.04      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.78/1.04      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.78/1.04      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_396]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_22,plain,
% 2.78/1.04      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.78/1.04      inference(cnf_transformation,[],[f99]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_68,plain,
% 2.78/1.04      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_22]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_399,plain,
% 2.78/1.04      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.78/1.04      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_397,c_68]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1222,plain,
% 2.78/1.04      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.78/1.04      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4574,plain,
% 2.78/1.04      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 2.78/1.04      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.78/1.04      inference(demodulation,[status(thm)],[c_4571,c_1222]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_38,plain,
% 2.78/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_40,plain,
% 2.78/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_43,plain,
% 2.78/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_25,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.78/1.04      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.78/1.04      | ~ v1_funct_1(X0)
% 2.78/1.04      | ~ v1_funct_1(X3) ),
% 2.78/1.04      inference(cnf_transformation,[],[f82]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1233,plain,
% 2.78/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.78/1.04      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.78/1.04      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.78/1.04      | v1_funct_1(X0) != iProver_top
% 2.78/1.04      | v1_funct_1(X3) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4576,plain,
% 2.78/1.04      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.78/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.78/1.04      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.78/1.04      | v1_funct_1(sK2) != iProver_top
% 2.78/1.04      | v1_funct_1(sK3) != iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_4571,c_1233]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4993,plain,
% 2.78/1.04      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_4574,c_38,c_40,c_41,c_43,c_4576]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4996,plain,
% 2.78/1.04      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.78/1.04      inference(demodulation,[status(thm)],[c_4993,c_4571]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_29,plain,
% 2.78/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.04      | ~ v1_funct_2(X3,X4,X1)
% 2.78/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.78/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.04      | ~ v1_funct_1(X0)
% 2.78/1.04      | ~ v1_funct_1(X3)
% 2.78/1.04      | v2_funct_1(X3)
% 2.78/1.04      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.78/1.04      | k1_xboole_0 = X2 ),
% 2.78/1.04      inference(cnf_transformation,[],[f85]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1229,plain,
% 2.78/1.04      ( k1_xboole_0 = X0
% 2.78/1.04      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.78/1.04      | v1_funct_2(X3,X4,X2) != iProver_top
% 2.78/1.04      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 2.78/1.04      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.78/1.04      | v1_funct_1(X1) != iProver_top
% 2.78/1.04      | v1_funct_1(X3) != iProver_top
% 2.78/1.04      | v2_funct_1(X3) = iProver_top
% 2.78/1.04      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_5003,plain,
% 2.78/1.04      ( sK0 = k1_xboole_0
% 2.78/1.04      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.78/1.04      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.78/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.78/1.04      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.78/1.04      | v1_funct_1(sK2) != iProver_top
% 2.78/1.04      | v1_funct_1(sK3) != iProver_top
% 2.78/1.04      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.78/1.04      | v2_funct_1(sK2) = iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_4996,c_1229]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_14,plain,
% 2.78/1.04      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 2.78/1.04      | ~ v1_relat_1(X0)
% 2.78/1.04      | ~ v1_relat_1(X1) ),
% 2.78/1.04      inference(cnf_transformation,[],[f70]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1237,plain,
% 2.78/1.04      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 2.78/1.04      | v1_relat_1(X0) != iProver_top
% 2.78/1.04      | v1_relat_1(X1) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4997,plain,
% 2.78/1.04      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 2.78/1.04      | v1_relat_1(sK2) != iProver_top
% 2.78/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_4993,c_1237]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_15,plain,
% 2.78/1.04      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 2.78/1.04      inference(cnf_transformation,[],[f95]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4998,plain,
% 2.78/1.04      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 2.78/1.04      | v1_relat_1(sK2) != iProver_top
% 2.78/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.78/1.04      inference(demodulation,[status(thm)],[c_4997,c_15]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_19,plain,
% 2.78/1.04      ( v5_relat_1(X0,X1)
% 2.78/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.78/1.04      inference(cnf_transformation,[],[f75]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_11,plain,
% 2.78/1.04      ( ~ v5_relat_1(X0,X1)
% 2.78/1.04      | r1_tarski(k2_relat_1(X0),X1)
% 2.78/1.04      | ~ v1_relat_1(X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f66]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_436,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.04      | r1_tarski(k2_relat_1(X0),X2)
% 2.78/1.04      | ~ v1_relat_1(X0) ),
% 2.78/1.04      inference(resolution,[status(thm)],[c_19,c_11]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1221,plain,
% 2.78/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.78/1.04      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 2.78/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2669,plain,
% 2.78/1.04      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 2.78/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_1228,c_1221]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1,plain,
% 2.78/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.78/1.04      inference(cnf_transformation,[],[f59]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1247,plain,
% 2.78/1.04      ( X0 = X1
% 2.78/1.04      | r1_tarski(X0,X1) != iProver_top
% 2.78/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2960,plain,
% 2.78/1.04      ( k2_relat_1(sK3) = sK0
% 2.78/1.04      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 2.78/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_2669,c_1247]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_9,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/1.04      | ~ v1_relat_1(X1)
% 2.78/1.04      | v1_relat_1(X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f65]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1240,plain,
% 2.78/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.78/1.04      | v1_relat_1(X1) != iProver_top
% 2.78/1.04      | v1_relat_1(X0) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2870,plain,
% 2.78/1.04      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.78/1.04      | v1_relat_1(sK3) = iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_1228,c_1240]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_12,plain,
% 2.78/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.78/1.04      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1239,plain,
% 2.78/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3020,plain,
% 2.78/1.04      ( v1_relat_1(sK3) = iProver_top ),
% 2.78/1.04      inference(forward_subsumption_resolution,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_2870,c_1239]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3825,plain,
% 2.78/1.04      ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 2.78/1.04      | k2_relat_1(sK3) = sK0 ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_2960,c_3020]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3826,plain,
% 2.78/1.04      ( k2_relat_1(sK3) = sK0
% 2.78/1.04      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_3825]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_7,plain,
% 2.78/1.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 2.78/1.04      inference(cnf_transformation,[],[f63]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1242,plain,
% 2.78/1.04      ( v1_xboole_0(X0) != iProver_top
% 2.78/1.04      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_8,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/1.04      | ~ v1_xboole_0(X1)
% 2.78/1.04      | v1_xboole_0(X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f64]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1241,plain,
% 2.78/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.78/1.04      | v1_xboole_0(X1) != iProver_top
% 2.78/1.04      | v1_xboole_0(X0) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2888,plain,
% 2.78/1.04      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.78/1.04      | v1_xboole_0(sK2) = iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_1225,c_1241]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3095,plain,
% 2.78/1.04      ( v1_xboole_0(sK2) = iProver_top
% 2.78/1.04      | v1_xboole_0(sK0) != iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_1242,c_2888]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3105,plain,
% 2.78/1.04      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 2.78/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_3095]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2871,plain,
% 2.78/1.04      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.78/1.04      | v1_relat_1(sK2) = iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_1225,c_1240]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3025,plain,
% 2.78/1.04      ( v1_relat_1(sK2) = iProver_top ),
% 2.78/1.04      inference(forward_subsumption_resolution,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_2871,c_1239]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3021,plain,
% 2.78/1.04      ( v1_relat_1(sK3) ),
% 2.78/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_3020]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_13,plain,
% 2.78/1.04      ( ~ v1_relat_1(X0)
% 2.78/1.04      | v1_xboole_0(X0)
% 2.78/1.04      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 2.78/1.04      inference(cnf_transformation,[],[f69]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1238,plain,
% 2.78/1.04      ( v1_relat_1(X0) != iProver_top
% 2.78/1.04      | v1_xboole_0(X0) = iProver_top
% 2.78/1.04      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2833,plain,
% 2.78/1.04      ( v1_relat_1(k6_partfun1(X0)) != iProver_top
% 2.78/1.04      | v1_xboole_0(X0) != iProver_top
% 2.78/1.04      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 2.78/1.04      inference(superposition,[status(thm)],[c_15,c_1238]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2834,plain,
% 2.78/1.04      ( ~ v1_relat_1(k6_partfun1(X0))
% 2.78/1.04      | ~ v1_xboole_0(X0)
% 2.78/1.04      | v1_xboole_0(k6_partfun1(X0)) ),
% 2.78/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_2833]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2836,plain,
% 2.78/1.04      ( ~ v1_relat_1(k6_partfun1(sK0))
% 2.78/1.04      | v1_xboole_0(k6_partfun1(sK0))
% 2.78/1.04      | ~ v1_xboole_0(sK0) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_2834]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_5,plain,
% 2.78/1.04      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 2.78/1.04      inference(cnf_transformation,[],[f61]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2734,plain,
% 2.78/1.04      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | sK2 = X0 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2736,plain,
% 2.78/1.04      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) | sK2 = sK0 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_2734]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2604,plain,
% 2.78/1.04      ( ~ v1_xboole_0(X0)
% 2.78/1.04      | ~ v1_xboole_0(k6_partfun1(X1))
% 2.78/1.04      | X0 = k6_partfun1(X1) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2606,plain,
% 2.78/1.04      ( ~ v1_xboole_0(k6_partfun1(sK0))
% 2.78/1.04      | ~ v1_xboole_0(sK0)
% 2.78/1.04      | sK0 = k6_partfun1(sK0) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_2604]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_689,plain,
% 2.78/1.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.78/1.04      theory(equality) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1615,plain,
% 2.78/1.04      ( v1_xboole_0(X0)
% 2.78/1.04      | ~ v1_xboole_0(k1_xboole_0)
% 2.78/1.04      | X0 != k1_xboole_0 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_689]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1617,plain,
% 2.78/1.04      ( v1_xboole_0(sK0)
% 2.78/1.04      | ~ v1_xboole_0(k1_xboole_0)
% 2.78/1.04      | sK0 != k1_xboole_0 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1615]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1486,plain,
% 2.78/1.04      ( v2_funct_1(X0)
% 2.78/1.04      | ~ v2_funct_1(k6_partfun1(X1))
% 2.78/1.04      | X0 != k6_partfun1(X1) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_698]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1488,plain,
% 2.78/1.04      ( ~ v2_funct_1(k6_partfun1(sK0))
% 2.78/1.04      | v2_funct_1(sK0)
% 2.78/1.04      | sK0 != k6_partfun1(sK0) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1486]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_10,plain,
% 2.78/1.04      ( v5_relat_1(X0,X1)
% 2.78/1.04      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.78/1.04      | ~ v1_relat_1(X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_23,plain,
% 2.78/1.04      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.78/1.04      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.78/1.04      | ~ v1_relat_1(X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f103]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_30,negated_conjecture,
% 2.78/1.04      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f94]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_415,plain,
% 2.78/1.04      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.78/1.04      | ~ v2_funct_1(sK2)
% 2.78/1.04      | ~ v1_relat_1(X0)
% 2.78/1.04      | k2_relat_1(X0) != sK0
% 2.78/1.04      | sK3 != X0 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_416,plain,
% 2.78/1.04      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 2.78/1.04      | ~ v2_funct_1(sK2)
% 2.78/1.04      | ~ v1_relat_1(sK3)
% 2.78/1.04      | k2_relat_1(sK3) != sK0 ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_415]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_469,plain,
% 2.78/1.04      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.78/1.04      | ~ v2_funct_1(sK2)
% 2.78/1.04      | ~ v1_relat_1(X0)
% 2.78/1.04      | ~ v1_relat_1(sK3)
% 2.78/1.04      | k2_relat_1(sK3) != X1
% 2.78/1.04      | k2_relat_1(sK3) != sK0
% 2.78/1.04      | sK3 != X0 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_416]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_470,plain,
% 2.78/1.04      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 2.78/1.04      | ~ v2_funct_1(sK2)
% 2.78/1.04      | ~ v1_relat_1(sK3)
% 2.78/1.04      | k2_relat_1(sK3) != sK0 ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_469]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2,plain,
% 2.78/1.04      ( r1_tarski(X0,X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f100]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_480,plain,
% 2.78/1.04      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 2.78/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_470,c_2]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_481,plain,
% 2.78/1.04      ( k2_relat_1(sK3) != sK0
% 2.78/1.04      | v2_funct_1(sK2) != iProver_top
% 2.78/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_0,plain,
% 2.78/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f56]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_17,plain,
% 2.78/1.04      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.78/1.04      inference(cnf_transformation,[],[f97]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_82,plain,
% 2.78/1.04      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_84,plain,
% 2.78/1.04      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_82]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_83,plain,
% 2.78/1.04      ( v2_funct_1(k6_partfun1(sK0)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_17]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_18,plain,
% 2.78/1.04      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.78/1.04      inference(cnf_transformation,[],[f98]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_80,plain,
% 2.78/1.04      ( v1_relat_1(k6_partfun1(sK0)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_18]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_33,negated_conjecture,
% 2.78/1.04      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f91]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_42,plain,
% 2.78/1.04      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_36,negated_conjecture,
% 2.78/1.04      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.78/1.04      inference(cnf_transformation,[],[f88]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_39,plain,
% 2.78/1.04      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.78/1.04      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(contradiction,plain,
% 2.78/1.04      ( $false ),
% 2.78/1.04      inference(minisat,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_7531,c_5003,c_4998,c_3826,c_3105,c_3025,c_3021,c_3020,
% 2.78/1.04                 c_2836,c_2736,c_2606,c_1617,c_1488,c_481,c_480,c_0,c_84,
% 2.78/1.04                 c_83,c_80,c_43,c_42,c_41,c_40,c_39,c_38]) ).
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.04  
% 2.78/1.04  ------                               Statistics
% 2.78/1.04  
% 2.78/1.04  ------ General
% 2.78/1.04  
% 2.78/1.04  abstr_ref_over_cycles:                  0
% 2.78/1.04  abstr_ref_under_cycles:                 0
% 2.78/1.04  gc_basic_clause_elim:                   0
% 2.78/1.04  forced_gc_time:                         0
% 2.78/1.04  parsing_time:                           0.031
% 2.78/1.04  unif_index_cands_time:                  0.
% 2.78/1.04  unif_index_add_time:                    0.
% 2.78/1.04  orderings_time:                         0.
% 2.78/1.04  out_proof_time:                         0.031
% 2.78/1.04  total_time:                             0.422
% 2.78/1.04  num_of_symbols:                         53
% 2.78/1.04  num_of_terms:                           10211
% 2.78/1.04  
% 2.78/1.04  ------ Preprocessing
% 2.78/1.04  
% 2.78/1.04  num_of_splits:                          0
% 2.78/1.04  num_of_split_atoms:                     0
% 2.78/1.04  num_of_reused_defs:                     0
% 2.78/1.04  num_eq_ax_congr_red:                    7
% 2.78/1.04  num_of_sem_filtered_clauses:            1
% 2.78/1.04  num_of_subtypes:                        0
% 2.78/1.04  monotx_restored_types:                  0
% 2.78/1.04  sat_num_of_epr_types:                   0
% 2.78/1.04  sat_num_of_non_cyclic_types:            0
% 2.78/1.04  sat_guarded_non_collapsed_types:        0
% 2.78/1.04  num_pure_diseq_elim:                    0
% 2.78/1.04  simp_replaced_by:                       0
% 2.78/1.04  res_preprocessed:                       161
% 2.78/1.04  prep_upred:                             0
% 2.78/1.04  prep_unflattend:                        15
% 2.78/1.04  smt_new_axioms:                         0
% 2.78/1.04  pred_elim_cands:                        7
% 2.78/1.04  pred_elim:                              3
% 2.78/1.04  pred_elim_cl:                           6
% 2.78/1.04  pred_elim_cycles:                       5
% 2.78/1.04  merged_defs:                            0
% 2.78/1.04  merged_defs_ncl:                        0
% 2.78/1.04  bin_hyper_res:                          0
% 2.78/1.04  prep_cycles:                            4
% 2.78/1.04  pred_elim_time:                         0.004
% 2.78/1.04  splitting_time:                         0.
% 2.78/1.04  sem_filter_time:                        0.
% 2.78/1.04  monotx_time:                            0.
% 2.78/1.04  subtype_inf_time:                       0.
% 2.78/1.04  
% 2.78/1.04  ------ Problem properties
% 2.78/1.04  
% 2.78/1.04  clauses:                                31
% 2.78/1.04  conjectures:                            6
% 2.78/1.04  epr:                                    9
% 2.78/1.04  horn:                                   30
% 2.78/1.04  ground:                                 9
% 2.78/1.04  unary:                                  15
% 2.78/1.04  binary:                                 3
% 2.78/1.04  lits:                                   77
% 2.78/1.04  lits_eq:                                8
% 2.78/1.04  fd_pure:                                0
% 2.78/1.04  fd_pseudo:                              0
% 2.78/1.04  fd_cond:                                1
% 2.78/1.04  fd_pseudo_cond:                         2
% 2.78/1.04  ac_symbols:                             0
% 2.78/1.04  
% 2.78/1.04  ------ Propositional Solver
% 2.78/1.04  
% 2.78/1.04  prop_solver_calls:                      27
% 2.78/1.04  prop_fast_solver_calls:                 1070
% 2.78/1.04  smt_solver_calls:                       0
% 2.78/1.04  smt_fast_solver_calls:                  0
% 2.78/1.04  prop_num_of_clauses:                    3469
% 2.78/1.04  prop_preprocess_simplified:             9886
% 2.78/1.04  prop_fo_subsumed:                       21
% 2.78/1.04  prop_solver_time:                       0.
% 2.78/1.04  smt_solver_time:                        0.
% 2.78/1.04  smt_fast_solver_time:                   0.
% 2.78/1.04  prop_fast_solver_time:                  0.
% 2.78/1.04  prop_unsat_core_time:                   0.
% 2.78/1.04  
% 2.78/1.04  ------ QBF
% 2.78/1.04  
% 2.78/1.04  qbf_q_res:                              0
% 2.78/1.04  qbf_num_tautologies:                    0
% 2.78/1.04  qbf_prep_cycles:                        0
% 2.78/1.04  
% 2.78/1.04  ------ BMC1
% 2.78/1.04  
% 2.78/1.04  bmc1_current_bound:                     -1
% 2.78/1.04  bmc1_last_solved_bound:                 -1
% 2.78/1.04  bmc1_unsat_core_size:                   -1
% 2.78/1.04  bmc1_unsat_core_parents_size:           -1
% 2.78/1.04  bmc1_merge_next_fun:                    0
% 2.78/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.04  
% 2.78/1.04  ------ Instantiation
% 2.78/1.04  
% 2.78/1.04  inst_num_of_clauses:                    909
% 2.78/1.04  inst_num_in_passive:                    493
% 2.78/1.04  inst_num_in_active:                     350
% 2.78/1.04  inst_num_in_unprocessed:                65
% 2.78/1.04  inst_num_of_loops:                      405
% 2.78/1.04  inst_num_of_learning_restarts:          0
% 2.78/1.04  inst_num_moves_active_passive:          53
% 2.78/1.04  inst_lit_activity:                      0
% 2.78/1.04  inst_lit_activity_moves:                0
% 2.78/1.04  inst_num_tautologies:                   0
% 2.78/1.04  inst_num_prop_implied:                  0
% 2.78/1.04  inst_num_existing_simplified:           0
% 2.78/1.04  inst_num_eq_res_simplified:             0
% 2.78/1.04  inst_num_child_elim:                    0
% 2.78/1.04  inst_num_of_dismatching_blockings:      20
% 2.78/1.04  inst_num_of_non_proper_insts:           516
% 2.78/1.04  inst_num_of_duplicates:                 0
% 2.78/1.04  inst_inst_num_from_inst_to_res:         0
% 2.78/1.04  inst_dismatching_checking_time:         0.
% 2.78/1.04  
% 2.78/1.04  ------ Resolution
% 2.78/1.04  
% 2.78/1.04  res_num_of_clauses:                     0
% 2.78/1.04  res_num_in_passive:                     0
% 2.78/1.04  res_num_in_active:                      0
% 2.78/1.04  res_num_of_loops:                       165
% 2.78/1.04  res_forward_subset_subsumed:            28
% 2.78/1.04  res_backward_subset_subsumed:           0
% 2.78/1.04  res_forward_subsumed:                   0
% 2.78/1.04  res_backward_subsumed:                  1
% 2.78/1.04  res_forward_subsumption_resolution:     1
% 2.78/1.04  res_backward_subsumption_resolution:    0
% 2.78/1.04  res_clause_to_clause_subsumption:       311
% 2.78/1.04  res_orphan_elimination:                 0
% 2.78/1.04  res_tautology_del:                      17
% 2.78/1.04  res_num_eq_res_simplified:              0
% 2.78/1.04  res_num_sel_changes:                    0
% 2.78/1.04  res_moves_from_active_to_pass:          0
% 2.78/1.04  
% 2.78/1.04  ------ Superposition
% 2.78/1.04  
% 2.78/1.04  sup_time_total:                         0.
% 2.78/1.04  sup_time_generating:                    0.
% 2.78/1.04  sup_time_sim_full:                      0.
% 2.78/1.04  sup_time_sim_immed:                     0.
% 2.78/1.04  
% 2.78/1.04  sup_num_of_clauses:                     134
% 2.78/1.04  sup_num_in_active:                      74
% 2.78/1.04  sup_num_in_passive:                     60
% 2.78/1.04  sup_num_of_loops:                       80
% 2.78/1.04  sup_fw_superposition:                   59
% 2.78/1.04  sup_bw_superposition:                   71
% 2.78/1.04  sup_immediate_simplified:               16
% 2.78/1.04  sup_given_eliminated:                   1
% 2.78/1.04  comparisons_done:                       0
% 2.78/1.04  comparisons_avoided:                    0
% 2.78/1.04  
% 2.78/1.04  ------ Simplifications
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  sim_fw_subset_subsumed:                 6
% 2.78/1.04  sim_bw_subset_subsumed:                 2
% 2.78/1.04  sim_fw_subsumed:                        4
% 2.78/1.04  sim_bw_subsumed:                        0
% 2.78/1.04  sim_fw_subsumption_res:                 3
% 2.78/1.04  sim_bw_subsumption_res:                 0
% 2.78/1.04  sim_tautology_del:                      4
% 2.78/1.04  sim_eq_tautology_del:                   3
% 2.78/1.04  sim_eq_res_simp:                        0
% 2.78/1.04  sim_fw_demodulated:                     4
% 2.78/1.04  sim_bw_demodulated:                     5
% 2.78/1.04  sim_light_normalised:                   5
% 2.78/1.04  sim_joinable_taut:                      0
% 2.78/1.04  sim_joinable_simp:                      0
% 2.78/1.04  sim_ac_normalised:                      0
% 2.78/1.04  sim_smt_subsumption:                    0
% 2.78/1.04  
%------------------------------------------------------------------------------
