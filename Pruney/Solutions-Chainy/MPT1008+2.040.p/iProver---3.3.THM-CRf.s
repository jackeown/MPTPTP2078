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
% DateTime   : Thu Dec  3 12:05:12 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  165 (2216 expanded)
%              Number of clauses        :   80 ( 437 expanded)
%              Number of leaves         :   25 ( 583 expanded)
%              Depth                    :   21
%              Number of atoms          :  474 (5527 expanded)
%              Number of equality atoms :  245 (3055 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
      & v1_funct_2(sK5,k1_tarski(sK3),sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f54])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f94])).

fof(f103,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f91,f95])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f64,f94,f95,f95,f94])).

fof(f93,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f102,plain,(
    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f93,f95,f95])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f75,f95,f95])).

fof(f89,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f104,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f90,f95])).

fof(f92,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f48])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f51,f50])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1935,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1916,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_13])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_394,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_18])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_1914,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_2199,plain,
    ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1916,c_1914])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1927,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k2_enumset1(X0,X0,X0,X2) = X1
    | k2_enumset1(X2,X2,X2,X2) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3576,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2199,c_1927])).

cnf(c_3850,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3576,c_1916])).

cnf(c_30,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2147,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1467,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2140,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_2212,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_371,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_372,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1915,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_373,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_2129,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2130,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2129])).

cnf(c_2155,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1915,c_37,c_373,c_2130])).

cnf(c_2156,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_2155])).

cnf(c_3842,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3576,c_2156])).

cnf(c_3918,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3850,c_32,c_30,c_2147,c_2212,c_3842])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1923,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3930,plain,
    ( sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3918,c_1923])).

cnf(c_2217,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1466,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2233,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_2408,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_3178,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2408])).

cnf(c_3179,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3178])).

cnf(c_4077,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3930,c_32,c_30,c_2129,c_2147,c_2212,c_2217,c_2233,c_3179,c_3842])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_509,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_511,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_32,c_31])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1919,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3481,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_511,c_1919])).

cnf(c_3740,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3481,c_37])).

cnf(c_4081,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4077,c_3740])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1926,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1925,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3462,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1926,c_1925])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_698,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_699,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_700,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_3583,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3462,c_700])).

cnf(c_4313,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4081,c_3583])).

cnf(c_4317,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1935,c_4313])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1932,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4510,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4317,c_1932])).

cnf(c_3923,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_3918,c_2156])).

cnf(c_4410,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3923,c_4077])).

cnf(c_4538,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4510,c_4410])).

cnf(c_1920,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3189,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1916,c_1920])).

cnf(c_3196,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_3189,c_30])).

cnf(c_4083,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4077,c_3196])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4538,c_4083])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:50:01 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.40/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/0.97  
% 2.40/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.97  
% 2.40/0.97  ------  iProver source info
% 2.40/0.97  
% 2.40/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.97  git: non_committed_changes: false
% 2.40/0.97  git: last_make_outside_of_git: false
% 2.40/0.97  
% 2.40/0.97  ------ 
% 2.40/0.97  
% 2.40/0.97  ------ Input Options
% 2.40/0.97  
% 2.40/0.97  --out_options                           all
% 2.40/0.97  --tptp_safe_out                         true
% 2.40/0.97  --problem_path                          ""
% 2.40/0.97  --include_path                          ""
% 2.40/0.97  --clausifier                            res/vclausify_rel
% 2.40/0.97  --clausifier_options                    --mode clausify
% 2.40/0.97  --stdin                                 false
% 2.40/0.97  --stats_out                             all
% 2.40/0.97  
% 2.40/0.97  ------ General Options
% 2.40/0.97  
% 2.40/0.97  --fof                                   false
% 2.40/0.97  --time_out_real                         305.
% 2.40/0.97  --time_out_virtual                      -1.
% 2.40/0.97  --symbol_type_check                     false
% 2.40/0.97  --clausify_out                          false
% 2.40/0.97  --sig_cnt_out                           false
% 2.40/0.97  --trig_cnt_out                          false
% 2.40/0.97  --trig_cnt_out_tolerance                1.
% 2.40/0.97  --trig_cnt_out_sk_spl                   false
% 2.40/0.97  --abstr_cl_out                          false
% 2.40/0.97  
% 2.40/0.97  ------ Global Options
% 2.40/0.97  
% 2.40/0.97  --schedule                              default
% 2.40/0.97  --add_important_lit                     false
% 2.40/0.97  --prop_solver_per_cl                    1000
% 2.40/0.97  --min_unsat_core                        false
% 2.40/0.97  --soft_assumptions                      false
% 2.40/0.97  --soft_lemma_size                       3
% 2.40/0.97  --prop_impl_unit_size                   0
% 2.40/0.97  --prop_impl_unit                        []
% 2.40/0.97  --share_sel_clauses                     true
% 2.40/0.97  --reset_solvers                         false
% 2.40/0.97  --bc_imp_inh                            [conj_cone]
% 2.40/0.97  --conj_cone_tolerance                   3.
% 2.40/0.97  --extra_neg_conj                        none
% 2.40/0.97  --large_theory_mode                     true
% 2.40/0.97  --prolific_symb_bound                   200
% 2.40/0.97  --lt_threshold                          2000
% 2.40/0.97  --clause_weak_htbl                      true
% 2.40/0.97  --gc_record_bc_elim                     false
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing Options
% 2.40/0.97  
% 2.40/0.97  --preprocessing_flag                    true
% 2.40/0.97  --time_out_prep_mult                    0.1
% 2.40/0.97  --splitting_mode                        input
% 2.40/0.97  --splitting_grd                         true
% 2.40/0.97  --splitting_cvd                         false
% 2.40/0.97  --splitting_cvd_svl                     false
% 2.40/0.97  --splitting_nvd                         32
% 2.40/0.97  --sub_typing                            true
% 2.40/0.97  --prep_gs_sim                           true
% 2.40/0.97  --prep_unflatten                        true
% 2.40/0.97  --prep_res_sim                          true
% 2.40/0.97  --prep_upred                            true
% 2.40/0.97  --prep_sem_filter                       exhaustive
% 2.40/0.97  --prep_sem_filter_out                   false
% 2.40/0.97  --pred_elim                             true
% 2.40/0.97  --res_sim_input                         true
% 2.40/0.97  --eq_ax_congr_red                       true
% 2.40/0.97  --pure_diseq_elim                       true
% 2.40/0.97  --brand_transform                       false
% 2.40/0.97  --non_eq_to_eq                          false
% 2.40/0.97  --prep_def_merge                        true
% 2.40/0.97  --prep_def_merge_prop_impl              false
% 2.40/0.97  --prep_def_merge_mbd                    true
% 2.40/0.97  --prep_def_merge_tr_red                 false
% 2.40/0.97  --prep_def_merge_tr_cl                  false
% 2.40/0.97  --smt_preprocessing                     true
% 2.40/0.97  --smt_ac_axioms                         fast
% 2.40/0.97  --preprocessed_out                      false
% 2.40/0.97  --preprocessed_stats                    false
% 2.40/0.97  
% 2.40/0.97  ------ Abstraction refinement Options
% 2.40/0.97  
% 2.40/0.97  --abstr_ref                             []
% 2.40/0.97  --abstr_ref_prep                        false
% 2.40/0.97  --abstr_ref_until_sat                   false
% 2.40/0.97  --abstr_ref_sig_restrict                funpre
% 2.40/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.97  --abstr_ref_under                       []
% 2.40/0.97  
% 2.40/0.97  ------ SAT Options
% 2.40/0.97  
% 2.40/0.97  --sat_mode                              false
% 2.40/0.97  --sat_fm_restart_options                ""
% 2.40/0.97  --sat_gr_def                            false
% 2.40/0.97  --sat_epr_types                         true
% 2.40/0.97  --sat_non_cyclic_types                  false
% 2.40/0.97  --sat_finite_models                     false
% 2.40/0.97  --sat_fm_lemmas                         false
% 2.40/0.97  --sat_fm_prep                           false
% 2.40/0.97  --sat_fm_uc_incr                        true
% 2.40/0.97  --sat_out_model                         small
% 2.40/0.97  --sat_out_clauses                       false
% 2.40/0.97  
% 2.40/0.97  ------ QBF Options
% 2.40/0.97  
% 2.40/0.97  --qbf_mode                              false
% 2.40/0.97  --qbf_elim_univ                         false
% 2.40/0.97  --qbf_dom_inst                          none
% 2.40/0.97  --qbf_dom_pre_inst                      false
% 2.40/0.97  --qbf_sk_in                             false
% 2.40/0.97  --qbf_pred_elim                         true
% 2.40/0.97  --qbf_split                             512
% 2.40/0.97  
% 2.40/0.97  ------ BMC1 Options
% 2.40/0.97  
% 2.40/0.97  --bmc1_incremental                      false
% 2.40/0.97  --bmc1_axioms                           reachable_all
% 2.40/0.97  --bmc1_min_bound                        0
% 2.40/0.97  --bmc1_max_bound                        -1
% 2.40/0.97  --bmc1_max_bound_default                -1
% 2.40/0.97  --bmc1_symbol_reachability              true
% 2.40/0.97  --bmc1_property_lemmas                  false
% 2.40/0.97  --bmc1_k_induction                      false
% 2.40/0.97  --bmc1_non_equiv_states                 false
% 2.40/0.97  --bmc1_deadlock                         false
% 2.40/0.97  --bmc1_ucm                              false
% 2.40/0.97  --bmc1_add_unsat_core                   none
% 2.40/0.97  --bmc1_unsat_core_children              false
% 2.40/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.97  --bmc1_out_stat                         full
% 2.40/0.97  --bmc1_ground_init                      false
% 2.40/0.97  --bmc1_pre_inst_next_state              false
% 2.40/0.97  --bmc1_pre_inst_state                   false
% 2.40/0.97  --bmc1_pre_inst_reach_state             false
% 2.40/0.97  --bmc1_out_unsat_core                   false
% 2.40/0.97  --bmc1_aig_witness_out                  false
% 2.40/0.97  --bmc1_verbose                          false
% 2.40/0.97  --bmc1_dump_clauses_tptp                false
% 2.40/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.97  --bmc1_dump_file                        -
% 2.40/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.97  --bmc1_ucm_extend_mode                  1
% 2.40/0.97  --bmc1_ucm_init_mode                    2
% 2.40/0.97  --bmc1_ucm_cone_mode                    none
% 2.40/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.97  --bmc1_ucm_relax_model                  4
% 2.40/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.97  --bmc1_ucm_layered_model                none
% 2.40/0.97  --bmc1_ucm_max_lemma_size               10
% 2.40/0.97  
% 2.40/0.97  ------ AIG Options
% 2.40/0.97  
% 2.40/0.97  --aig_mode                              false
% 2.40/0.97  
% 2.40/0.97  ------ Instantiation Options
% 2.40/0.97  
% 2.40/0.97  --instantiation_flag                    true
% 2.40/0.97  --inst_sos_flag                         false
% 2.40/0.97  --inst_sos_phase                        true
% 2.40/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.97  --inst_lit_sel_side                     num_symb
% 2.40/0.97  --inst_solver_per_active                1400
% 2.40/0.97  --inst_solver_calls_frac                1.
% 2.40/0.97  --inst_passive_queue_type               priority_queues
% 2.40/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.97  --inst_passive_queues_freq              [25;2]
% 2.40/0.97  --inst_dismatching                      true
% 2.40/0.97  --inst_eager_unprocessed_to_passive     true
% 2.40/0.97  --inst_prop_sim_given                   true
% 2.40/0.97  --inst_prop_sim_new                     false
% 2.40/0.97  --inst_subs_new                         false
% 2.40/0.97  --inst_eq_res_simp                      false
% 2.40/0.97  --inst_subs_given                       false
% 2.40/0.97  --inst_orphan_elimination               true
% 2.40/0.97  --inst_learning_loop_flag               true
% 2.40/0.97  --inst_learning_start                   3000
% 2.40/0.97  --inst_learning_factor                  2
% 2.40/0.97  --inst_start_prop_sim_after_learn       3
% 2.40/0.97  --inst_sel_renew                        solver
% 2.40/0.97  --inst_lit_activity_flag                true
% 2.40/0.97  --inst_restr_to_given                   false
% 2.40/0.97  --inst_activity_threshold               500
% 2.40/0.97  --inst_out_proof                        true
% 2.40/0.97  
% 2.40/0.97  ------ Resolution Options
% 2.40/0.97  
% 2.40/0.97  --resolution_flag                       true
% 2.40/0.97  --res_lit_sel                           adaptive
% 2.40/0.97  --res_lit_sel_side                      none
% 2.40/0.97  --res_ordering                          kbo
% 2.40/0.97  --res_to_prop_solver                    active
% 2.40/0.97  --res_prop_simpl_new                    false
% 2.40/0.97  --res_prop_simpl_given                  true
% 2.40/0.97  --res_passive_queue_type                priority_queues
% 2.40/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.97  --res_passive_queues_freq               [15;5]
% 2.40/0.97  --res_forward_subs                      full
% 2.40/0.97  --res_backward_subs                     full
% 2.40/0.97  --res_forward_subs_resolution           true
% 2.40/0.97  --res_backward_subs_resolution          true
% 2.40/0.97  --res_orphan_elimination                true
% 2.40/0.97  --res_time_limit                        2.
% 2.40/0.97  --res_out_proof                         true
% 2.40/0.97  
% 2.40/0.97  ------ Superposition Options
% 2.40/0.97  
% 2.40/0.97  --superposition_flag                    true
% 2.40/0.97  --sup_passive_queue_type                priority_queues
% 2.40/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.97  --demod_completeness_check              fast
% 2.40/0.97  --demod_use_ground                      true
% 2.40/0.97  --sup_to_prop_solver                    passive
% 2.40/0.97  --sup_prop_simpl_new                    true
% 2.40/0.97  --sup_prop_simpl_given                  true
% 2.40/0.97  --sup_fun_splitting                     false
% 2.40/0.97  --sup_smt_interval                      50000
% 2.40/0.97  
% 2.40/0.97  ------ Superposition Simplification Setup
% 2.40/0.97  
% 2.40/0.97  --sup_indices_passive                   []
% 2.40/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_full_bw                           [BwDemod]
% 2.40/0.97  --sup_immed_triv                        [TrivRules]
% 2.40/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_immed_bw_main                     []
% 2.40/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.97  
% 2.40/0.97  ------ Combination Options
% 2.40/0.97  
% 2.40/0.97  --comb_res_mult                         3
% 2.40/0.97  --comb_sup_mult                         2
% 2.40/0.97  --comb_inst_mult                        10
% 2.40/0.97  
% 2.40/0.97  ------ Debug Options
% 2.40/0.97  
% 2.40/0.97  --dbg_backtrace                         false
% 2.40/0.97  --dbg_dump_prop_clauses                 false
% 2.40/0.97  --dbg_dump_prop_clauses_file            -
% 2.40/0.97  --dbg_out_stat                          false
% 2.40/0.97  ------ Parsing...
% 2.40/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.97  ------ Proving...
% 2.40/0.97  ------ Problem Properties 
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  clauses                                 28
% 2.40/0.97  conjectures                             3
% 2.40/0.97  EPR                                     5
% 2.40/0.97  Horn                                    24
% 2.40/0.97  unary                                   10
% 2.40/0.97  binary                                  7
% 2.40/0.97  lits                                    61
% 2.40/0.97  lits eq                                 23
% 2.40/0.97  fd_pure                                 0
% 2.40/0.97  fd_pseudo                               0
% 2.40/0.97  fd_cond                                 3
% 2.40/0.97  fd_pseudo_cond                          1
% 2.40/0.97  AC symbols                              0
% 2.40/0.97  
% 2.40/0.97  ------ Schedule dynamic 5 is on 
% 2.40/0.97  
% 2.40/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  ------ 
% 2.40/0.97  Current options:
% 2.40/0.97  ------ 
% 2.40/0.97  
% 2.40/0.97  ------ Input Options
% 2.40/0.97  
% 2.40/0.97  --out_options                           all
% 2.40/0.97  --tptp_safe_out                         true
% 2.40/0.97  --problem_path                          ""
% 2.40/0.97  --include_path                          ""
% 2.40/0.97  --clausifier                            res/vclausify_rel
% 2.40/0.97  --clausifier_options                    --mode clausify
% 2.40/0.97  --stdin                                 false
% 2.40/0.97  --stats_out                             all
% 2.40/0.97  
% 2.40/0.97  ------ General Options
% 2.40/0.97  
% 2.40/0.97  --fof                                   false
% 2.40/0.97  --time_out_real                         305.
% 2.40/0.97  --time_out_virtual                      -1.
% 2.40/0.97  --symbol_type_check                     false
% 2.40/0.97  --clausify_out                          false
% 2.40/0.97  --sig_cnt_out                           false
% 2.40/0.97  --trig_cnt_out                          false
% 2.40/0.97  --trig_cnt_out_tolerance                1.
% 2.40/0.97  --trig_cnt_out_sk_spl                   false
% 2.40/0.97  --abstr_cl_out                          false
% 2.40/0.97  
% 2.40/0.97  ------ Global Options
% 2.40/0.97  
% 2.40/0.97  --schedule                              default
% 2.40/0.97  --add_important_lit                     false
% 2.40/0.97  --prop_solver_per_cl                    1000
% 2.40/0.97  --min_unsat_core                        false
% 2.40/0.97  --soft_assumptions                      false
% 2.40/0.97  --soft_lemma_size                       3
% 2.40/0.97  --prop_impl_unit_size                   0
% 2.40/0.97  --prop_impl_unit                        []
% 2.40/0.97  --share_sel_clauses                     true
% 2.40/0.97  --reset_solvers                         false
% 2.40/0.97  --bc_imp_inh                            [conj_cone]
% 2.40/0.97  --conj_cone_tolerance                   3.
% 2.40/0.97  --extra_neg_conj                        none
% 2.40/0.97  --large_theory_mode                     true
% 2.40/0.97  --prolific_symb_bound                   200
% 2.40/0.97  --lt_threshold                          2000
% 2.40/0.97  --clause_weak_htbl                      true
% 2.40/0.97  --gc_record_bc_elim                     false
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing Options
% 2.40/0.97  
% 2.40/0.97  --preprocessing_flag                    true
% 2.40/0.97  --time_out_prep_mult                    0.1
% 2.40/0.97  --splitting_mode                        input
% 2.40/0.97  --splitting_grd                         true
% 2.40/0.97  --splitting_cvd                         false
% 2.40/0.97  --splitting_cvd_svl                     false
% 2.40/0.97  --splitting_nvd                         32
% 2.40/0.97  --sub_typing                            true
% 2.40/0.97  --prep_gs_sim                           true
% 2.40/0.97  --prep_unflatten                        true
% 2.40/0.97  --prep_res_sim                          true
% 2.40/0.97  --prep_upred                            true
% 2.40/0.97  --prep_sem_filter                       exhaustive
% 2.40/0.97  --prep_sem_filter_out                   false
% 2.40/0.97  --pred_elim                             true
% 2.40/0.97  --res_sim_input                         true
% 2.40/0.97  --eq_ax_congr_red                       true
% 2.40/0.97  --pure_diseq_elim                       true
% 2.40/0.97  --brand_transform                       false
% 2.40/0.97  --non_eq_to_eq                          false
% 2.40/0.97  --prep_def_merge                        true
% 2.40/0.97  --prep_def_merge_prop_impl              false
% 2.40/0.97  --prep_def_merge_mbd                    true
% 2.40/0.97  --prep_def_merge_tr_red                 false
% 2.40/0.97  --prep_def_merge_tr_cl                  false
% 2.40/0.97  --smt_preprocessing                     true
% 2.40/0.97  --smt_ac_axioms                         fast
% 2.40/0.97  --preprocessed_out                      false
% 2.40/0.97  --preprocessed_stats                    false
% 2.40/0.97  
% 2.40/0.97  ------ Abstraction refinement Options
% 2.40/0.97  
% 2.40/0.97  --abstr_ref                             []
% 2.40/0.97  --abstr_ref_prep                        false
% 2.40/0.97  --abstr_ref_until_sat                   false
% 2.40/0.97  --abstr_ref_sig_restrict                funpre
% 2.40/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.97  --abstr_ref_under                       []
% 2.40/0.97  
% 2.40/0.97  ------ SAT Options
% 2.40/0.97  
% 2.40/0.97  --sat_mode                              false
% 2.40/0.97  --sat_fm_restart_options                ""
% 2.40/0.97  --sat_gr_def                            false
% 2.40/0.97  --sat_epr_types                         true
% 2.40/0.97  --sat_non_cyclic_types                  false
% 2.40/0.97  --sat_finite_models                     false
% 2.40/0.97  --sat_fm_lemmas                         false
% 2.40/0.97  --sat_fm_prep                           false
% 2.40/0.97  --sat_fm_uc_incr                        true
% 2.40/0.97  --sat_out_model                         small
% 2.40/0.97  --sat_out_clauses                       false
% 2.40/0.97  
% 2.40/0.97  ------ QBF Options
% 2.40/0.97  
% 2.40/0.97  --qbf_mode                              false
% 2.40/0.97  --qbf_elim_univ                         false
% 2.40/0.97  --qbf_dom_inst                          none
% 2.40/0.97  --qbf_dom_pre_inst                      false
% 2.40/0.97  --qbf_sk_in                             false
% 2.40/0.97  --qbf_pred_elim                         true
% 2.40/0.97  --qbf_split                             512
% 2.40/0.97  
% 2.40/0.97  ------ BMC1 Options
% 2.40/0.97  
% 2.40/0.97  --bmc1_incremental                      false
% 2.40/0.97  --bmc1_axioms                           reachable_all
% 2.40/0.97  --bmc1_min_bound                        0
% 2.40/0.97  --bmc1_max_bound                        -1
% 2.40/0.97  --bmc1_max_bound_default                -1
% 2.40/0.97  --bmc1_symbol_reachability              true
% 2.40/0.97  --bmc1_property_lemmas                  false
% 2.40/0.97  --bmc1_k_induction                      false
% 2.40/0.97  --bmc1_non_equiv_states                 false
% 2.40/0.97  --bmc1_deadlock                         false
% 2.40/0.97  --bmc1_ucm                              false
% 2.40/0.97  --bmc1_add_unsat_core                   none
% 2.40/0.97  --bmc1_unsat_core_children              false
% 2.40/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.97  --bmc1_out_stat                         full
% 2.40/0.97  --bmc1_ground_init                      false
% 2.40/0.97  --bmc1_pre_inst_next_state              false
% 2.40/0.97  --bmc1_pre_inst_state                   false
% 2.40/0.97  --bmc1_pre_inst_reach_state             false
% 2.40/0.97  --bmc1_out_unsat_core                   false
% 2.40/0.97  --bmc1_aig_witness_out                  false
% 2.40/0.97  --bmc1_verbose                          false
% 2.40/0.97  --bmc1_dump_clauses_tptp                false
% 2.40/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.97  --bmc1_dump_file                        -
% 2.40/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.97  --bmc1_ucm_extend_mode                  1
% 2.40/0.97  --bmc1_ucm_init_mode                    2
% 2.40/0.97  --bmc1_ucm_cone_mode                    none
% 2.40/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.97  --bmc1_ucm_relax_model                  4
% 2.40/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.97  --bmc1_ucm_layered_model                none
% 2.40/0.97  --bmc1_ucm_max_lemma_size               10
% 2.40/0.97  
% 2.40/0.97  ------ AIG Options
% 2.40/0.97  
% 2.40/0.97  --aig_mode                              false
% 2.40/0.97  
% 2.40/0.97  ------ Instantiation Options
% 2.40/0.97  
% 2.40/0.97  --instantiation_flag                    true
% 2.40/0.97  --inst_sos_flag                         false
% 2.40/0.97  --inst_sos_phase                        true
% 2.40/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.97  --inst_lit_sel_side                     none
% 2.40/0.97  --inst_solver_per_active                1400
% 2.40/0.97  --inst_solver_calls_frac                1.
% 2.40/0.97  --inst_passive_queue_type               priority_queues
% 2.40/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.97  --inst_passive_queues_freq              [25;2]
% 2.40/0.97  --inst_dismatching                      true
% 2.40/0.97  --inst_eager_unprocessed_to_passive     true
% 2.40/0.97  --inst_prop_sim_given                   true
% 2.40/0.97  --inst_prop_sim_new                     false
% 2.40/0.97  --inst_subs_new                         false
% 2.40/0.97  --inst_eq_res_simp                      false
% 2.40/0.97  --inst_subs_given                       false
% 2.40/0.97  --inst_orphan_elimination               true
% 2.40/0.97  --inst_learning_loop_flag               true
% 2.40/0.97  --inst_learning_start                   3000
% 2.40/0.97  --inst_learning_factor                  2
% 2.40/0.97  --inst_start_prop_sim_after_learn       3
% 2.40/0.97  --inst_sel_renew                        solver
% 2.40/0.97  --inst_lit_activity_flag                true
% 2.40/0.97  --inst_restr_to_given                   false
% 2.40/0.97  --inst_activity_threshold               500
% 2.40/0.97  --inst_out_proof                        true
% 2.40/0.97  
% 2.40/0.97  ------ Resolution Options
% 2.40/0.97  
% 2.40/0.97  --resolution_flag                       false
% 2.40/0.97  --res_lit_sel                           adaptive
% 2.40/0.97  --res_lit_sel_side                      none
% 2.40/0.97  --res_ordering                          kbo
% 2.40/0.97  --res_to_prop_solver                    active
% 2.40/0.97  --res_prop_simpl_new                    false
% 2.40/0.97  --res_prop_simpl_given                  true
% 2.40/0.97  --res_passive_queue_type                priority_queues
% 2.40/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.97  --res_passive_queues_freq               [15;5]
% 2.40/0.97  --res_forward_subs                      full
% 2.40/0.97  --res_backward_subs                     full
% 2.40/0.97  --res_forward_subs_resolution           true
% 2.40/0.97  --res_backward_subs_resolution          true
% 2.40/0.97  --res_orphan_elimination                true
% 2.40/0.97  --res_time_limit                        2.
% 2.40/0.97  --res_out_proof                         true
% 2.40/0.97  
% 2.40/0.97  ------ Superposition Options
% 2.40/0.97  
% 2.40/0.97  --superposition_flag                    true
% 2.40/0.97  --sup_passive_queue_type                priority_queues
% 2.40/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.97  --demod_completeness_check              fast
% 2.40/0.97  --demod_use_ground                      true
% 2.40/0.97  --sup_to_prop_solver                    passive
% 2.40/0.97  --sup_prop_simpl_new                    true
% 2.40/0.97  --sup_prop_simpl_given                  true
% 2.40/0.97  --sup_fun_splitting                     false
% 2.40/0.97  --sup_smt_interval                      50000
% 2.40/0.97  
% 2.40/0.97  ------ Superposition Simplification Setup
% 2.40/0.97  
% 2.40/0.97  --sup_indices_passive                   []
% 2.40/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_full_bw                           [BwDemod]
% 2.40/0.97  --sup_immed_triv                        [TrivRules]
% 2.40/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_immed_bw_main                     []
% 2.40/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.97  
% 2.40/0.97  ------ Combination Options
% 2.40/0.97  
% 2.40/0.97  --comb_res_mult                         3
% 2.40/0.97  --comb_sup_mult                         2
% 2.40/0.97  --comb_inst_mult                        10
% 2.40/0.97  
% 2.40/0.97  ------ Debug Options
% 2.40/0.97  
% 2.40/0.97  --dbg_backtrace                         false
% 2.40/0.97  --dbg_dump_prop_clauses                 false
% 2.40/0.97  --dbg_dump_prop_clauses_file            -
% 2.40/0.97  --dbg_out_stat                          false
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  ------ Proving...
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  % SZS status Theorem for theBenchmark.p
% 2.40/0.97  
% 2.40/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.97  
% 2.40/0.97  fof(f1,axiom,(
% 2.40/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f22,plain,(
% 2.40/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.97    inference(ennf_transformation,[],[f1])).
% 2.40/0.97  
% 2.40/0.97  fof(f41,plain,(
% 2.40/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.97    inference(nnf_transformation,[],[f22])).
% 2.40/0.97  
% 2.40/0.97  fof(f42,plain,(
% 2.40/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.97    inference(rectify,[],[f41])).
% 2.40/0.97  
% 2.40/0.97  fof(f43,plain,(
% 2.40/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f44,plain,(
% 2.40/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.40/0.97  
% 2.40/0.97  fof(f57,plain,(
% 2.40/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f44])).
% 2.40/0.97  
% 2.40/0.97  fof(f19,conjecture,(
% 2.40/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f20,negated_conjecture,(
% 2.40/0.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.40/0.97    inference(negated_conjecture,[],[f19])).
% 2.40/0.97  
% 2.40/0.97  fof(f39,plain,(
% 2.40/0.97    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.40/0.97    inference(ennf_transformation,[],[f20])).
% 2.40/0.97  
% 2.40/0.97  fof(f40,plain,(
% 2.40/0.97    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.40/0.97    inference(flattening,[],[f39])).
% 2.40/0.97  
% 2.40/0.97  fof(f54,plain,(
% 2.40/0.97    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f55,plain,(
% 2.40/0.97    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 2.40/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f54])).
% 2.40/0.97  
% 2.40/0.97  fof(f91,plain,(
% 2.40/0.97    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 2.40/0.97    inference(cnf_transformation,[],[f55])).
% 2.40/0.97  
% 2.40/0.97  fof(f4,axiom,(
% 2.40/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f61,plain,(
% 2.40/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f4])).
% 2.40/0.97  
% 2.40/0.97  fof(f5,axiom,(
% 2.40/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f62,plain,(
% 2.40/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f5])).
% 2.40/0.97  
% 2.40/0.97  fof(f6,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f63,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f6])).
% 2.40/0.97  
% 2.40/0.97  fof(f94,plain,(
% 2.40/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.40/0.97    inference(definition_unfolding,[],[f62,f63])).
% 2.40/0.97  
% 2.40/0.97  fof(f95,plain,(
% 2.40/0.97    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.40/0.97    inference(definition_unfolding,[],[f61,f94])).
% 2.40/0.97  
% 2.40/0.97  fof(f103,plain,(
% 2.40/0.97    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 2.40/0.97    inference(definition_unfolding,[],[f91,f95])).
% 2.40/0.97  
% 2.40/0.97  fof(f15,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f21,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.40/0.97    inference(pure_predicate_removal,[],[f15])).
% 2.40/0.97  
% 2.40/0.97  fof(f34,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.97    inference(ennf_transformation,[],[f21])).
% 2.40/0.97  
% 2.40/0.97  fof(f78,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f10,axiom,(
% 2.40/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f27,plain,(
% 2.40/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.40/0.97    inference(ennf_transformation,[],[f10])).
% 2.40/0.97  
% 2.40/0.97  fof(f47,plain,(
% 2.40/0.97    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.40/0.97    inference(nnf_transformation,[],[f27])).
% 2.40/0.97  
% 2.40/0.97  fof(f71,plain,(
% 2.40/0.97    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f47])).
% 2.40/0.97  
% 2.40/0.97  fof(f14,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f33,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.97    inference(ennf_transformation,[],[f14])).
% 2.40/0.97  
% 2.40/0.97  fof(f77,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.97    inference(cnf_transformation,[],[f33])).
% 2.40/0.97  
% 2.40/0.97  fof(f7,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f24,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.40/0.97    inference(ennf_transformation,[],[f7])).
% 2.40/0.97  
% 2.40/0.97  fof(f45,plain,(
% 2.40/0.97    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.40/0.97    inference(nnf_transformation,[],[f24])).
% 2.40/0.97  
% 2.40/0.97  fof(f46,plain,(
% 2.40/0.97    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.40/0.97    inference(flattening,[],[f45])).
% 2.40/0.97  
% 2.40/0.97  fof(f64,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.40/0.97    inference(cnf_transformation,[],[f46])).
% 2.40/0.97  
% 2.40/0.97  fof(f100,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 2.40/0.97    inference(definition_unfolding,[],[f64,f94,f95,f95,f94])).
% 2.40/0.97  
% 2.40/0.97  fof(f93,plain,(
% 2.40/0.97    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 2.40/0.97    inference(cnf_transformation,[],[f55])).
% 2.40/0.97  
% 2.40/0.97  fof(f102,plain,(
% 2.40/0.97    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)),
% 2.40/0.97    inference(definition_unfolding,[],[f93,f95,f95])).
% 2.40/0.97  
% 2.40/0.97  fof(f16,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f35,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.97    inference(ennf_transformation,[],[f16])).
% 2.40/0.97  
% 2.40/0.97  fof(f79,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.97    inference(cnf_transformation,[],[f35])).
% 2.40/0.97  
% 2.40/0.97  fof(f12,axiom,(
% 2.40/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f30,plain,(
% 2.40/0.97    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.40/0.97    inference(ennf_transformation,[],[f12])).
% 2.40/0.97  
% 2.40/0.97  fof(f31,plain,(
% 2.40/0.97    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.40/0.97    inference(flattening,[],[f30])).
% 2.40/0.97  
% 2.40/0.97  fof(f75,plain,(
% 2.40/0.97    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f31])).
% 2.40/0.97  
% 2.40/0.97  fof(f101,plain,(
% 2.40/0.97    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.40/0.97    inference(definition_unfolding,[],[f75,f95,f95])).
% 2.40/0.97  
% 2.40/0.97  fof(f89,plain,(
% 2.40/0.97    v1_funct_1(sK5)),
% 2.40/0.97    inference(cnf_transformation,[],[f55])).
% 2.40/0.97  
% 2.40/0.97  fof(f11,axiom,(
% 2.40/0.97    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f28,plain,(
% 2.40/0.97    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.40/0.97    inference(ennf_transformation,[],[f11])).
% 2.40/0.97  
% 2.40/0.97  fof(f29,plain,(
% 2.40/0.97    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.40/0.97    inference(flattening,[],[f28])).
% 2.40/0.97  
% 2.40/0.97  fof(f73,plain,(
% 2.40/0.97    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f29])).
% 2.40/0.97  
% 2.40/0.97  fof(f18,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f37,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.97    inference(ennf_transformation,[],[f18])).
% 2.40/0.97  
% 2.40/0.97  fof(f38,plain,(
% 2.40/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.97    inference(flattening,[],[f37])).
% 2.40/0.97  
% 2.40/0.97  fof(f53,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.97    inference(nnf_transformation,[],[f38])).
% 2.40/0.97  
% 2.40/0.97  fof(f83,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.97    inference(cnf_transformation,[],[f53])).
% 2.40/0.97  
% 2.40/0.97  fof(f90,plain,(
% 2.40/0.97    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 2.40/0.97    inference(cnf_transformation,[],[f55])).
% 2.40/0.97  
% 2.40/0.97  fof(f104,plain,(
% 2.40/0.97    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 2.40/0.97    inference(definition_unfolding,[],[f90,f95])).
% 2.40/0.97  
% 2.40/0.97  fof(f92,plain,(
% 2.40/0.97    k1_xboole_0 != sK4),
% 2.40/0.97    inference(cnf_transformation,[],[f55])).
% 2.40/0.97  
% 2.40/0.97  fof(f17,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f36,plain,(
% 2.40/0.97    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.40/0.97    inference(ennf_transformation,[],[f17])).
% 2.40/0.97  
% 2.40/0.97  fof(f48,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.40/0.97    inference(nnf_transformation,[],[f36])).
% 2.40/0.97  
% 2.40/0.97  fof(f49,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.40/0.97    inference(rectify,[],[f48])).
% 2.40/0.97  
% 2.40/0.97  fof(f51,plain,(
% 2.40/0.97    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f50,plain,(
% 2.40/0.97    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f52,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.40/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f51,f50])).
% 2.40/0.97  
% 2.40/0.97  fof(f82,plain,(
% 2.40/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.40/0.97    inference(cnf_transformation,[],[f52])).
% 2.40/0.97  
% 2.40/0.97  fof(f8,axiom,(
% 2.40/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f69,plain,(
% 2.40/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.40/0.97    inference(cnf_transformation,[],[f8])).
% 2.40/0.97  
% 2.40/0.97  fof(f9,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f25,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.40/0.97    inference(ennf_transformation,[],[f9])).
% 2.40/0.97  
% 2.40/0.97  fof(f26,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.40/0.97    inference(flattening,[],[f25])).
% 2.40/0.97  
% 2.40/0.97  fof(f70,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f26])).
% 2.40/0.97  
% 2.40/0.97  fof(f2,axiom,(
% 2.40/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f59,plain,(
% 2.40/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f2])).
% 2.40/0.97  
% 2.40/0.97  fof(f13,axiom,(
% 2.40/0.97    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f32,plain,(
% 2.40/0.97    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.40/0.97    inference(ennf_transformation,[],[f13])).
% 2.40/0.97  
% 2.40/0.97  fof(f76,plain,(
% 2.40/0.97    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f32])).
% 2.40/0.97  
% 2.40/0.97  fof(f3,axiom,(
% 2.40/0.97    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.40/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f23,plain,(
% 2.40/0.97    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.40/0.97    inference(ennf_transformation,[],[f3])).
% 2.40/0.97  
% 2.40/0.97  fof(f60,plain,(
% 2.40/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f23])).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1,plain,
% 2.40/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.40/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1935,plain,
% 2.40/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.40/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_32,negated_conjecture,
% 2.40/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 2.40/0.97      inference(cnf_transformation,[],[f103]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1916,plain,
% 2.40/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_19,plain,
% 2.40/0.97      ( v4_relat_1(X0,X1)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.40/0.97      inference(cnf_transformation,[],[f78]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_13,plain,
% 2.40/0.97      ( ~ v4_relat_1(X0,X1)
% 2.40/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 2.40/0.97      | ~ v1_relat_1(X0) ),
% 2.40/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_390,plain,
% 2.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 2.40/0.97      | ~ v1_relat_1(X0) ),
% 2.40/0.97      inference(resolution,[status(thm)],[c_19,c_13]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_18,plain,
% 2.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.97      | v1_relat_1(X0) ),
% 2.40/0.97      inference(cnf_transformation,[],[f77]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_394,plain,
% 2.40/0.97      ( r1_tarski(k1_relat_1(X0),X1)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_390,c_18]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_395,plain,
% 2.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.97      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.40/0.97      inference(renaming,[status(thm)],[c_394]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1914,plain,
% 2.40/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.40/0.97      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2199,plain,
% 2.40/0.97      ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_1916,c_1914]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_9,plain,
% 2.40/0.97      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 2.40/0.97      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.40/0.97      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.40/0.97      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(cnf_transformation,[],[f100]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1927,plain,
% 2.40/0.97      ( k2_enumset1(X0,X0,X0,X0) = X1
% 2.40/0.97      | k2_enumset1(X0,X0,X0,X2) = X1
% 2.40/0.97      | k2_enumset1(X2,X2,X2,X2) = X1
% 2.40/0.97      | k1_xboole_0 = X1
% 2.40/0.97      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3576,plain,
% 2.40/0.97      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
% 2.40/0.97      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_2199,c_1927]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3850,plain,
% 2.40/0.97      ( k1_relat_1(sK5) = k1_xboole_0
% 2.40/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_3576,c_1916]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_30,negated_conjecture,
% 2.40/0.97      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 2.40/0.97      inference(cnf_transformation,[],[f102]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_20,plain,
% 2.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.40/0.97      inference(cnf_transformation,[],[f79]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2147,plain,
% 2.40/0.97      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.40/0.97      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_20]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1467,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2140,plain,
% 2.40/0.97      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
% 2.40/0.97      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 2.40/0.97      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_1467]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2212,plain,
% 2.40/0.97      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 2.40/0.97      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
% 2.40/0.97      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_2140]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_16,plain,
% 2.40/0.97      ( ~ v1_funct_1(X0)
% 2.40/0.97      | ~ v1_relat_1(X0)
% 2.40/0.97      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.40/0.97      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.40/0.97      inference(cnf_transformation,[],[f101]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_34,negated_conjecture,
% 2.40/0.97      ( v1_funct_1(sK5) ),
% 2.40/0.97      inference(cnf_transformation,[],[f89]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_371,plain,
% 2.40/0.97      ( ~ v1_relat_1(X0)
% 2.40/0.97      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.40/0.97      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.40/0.97      | sK5 != X0 ),
% 2.40/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_34]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_372,plain,
% 2.40/0.97      ( ~ v1_relat_1(sK5)
% 2.40/0.97      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.40/0.97      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.40/0.97      inference(unflattening,[status(thm)],[c_371]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1915,plain,
% 2.40/0.97      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.40/0.97      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.40/0.97      | v1_relat_1(sK5) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_37,plain,
% 2.40/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_373,plain,
% 2.40/0.97      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.40/0.97      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.40/0.97      | v1_relat_1(sK5) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2129,plain,
% 2.40/0.97      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.40/0.97      | v1_relat_1(sK5) ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_18]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2130,plain,
% 2.40/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.40/0.97      | v1_relat_1(sK5) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_2129]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2155,plain,
% 2.40/0.97      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.40/0.97      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_1915,c_37,c_373,c_2130]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2156,plain,
% 2.40/0.97      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.40/0.97      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.40/0.97      inference(renaming,[status(thm)],[c_2155]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3842,plain,
% 2.40/0.97      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
% 2.40/0.97      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_3576,c_2156]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3918,plain,
% 2.40/0.97      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_3850,c_32,c_30,c_2147,c_2212,c_3842]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_15,plain,
% 2.40/0.97      ( ~ v1_relat_1(X0)
% 2.40/0.97      | k1_relat_1(X0) != k1_xboole_0
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1923,plain,
% 2.40/0.97      ( k1_relat_1(X0) != k1_xboole_0
% 2.40/0.97      | k1_xboole_0 = X0
% 2.40/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3930,plain,
% 2.40/0.97      ( sK5 = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_3918,c_1923]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2217,plain,
% 2.40/0.97      ( ~ v1_relat_1(sK5)
% 2.40/0.97      | k1_relat_1(sK5) != k1_xboole_0
% 2.40/0.97      | k1_xboole_0 = sK5 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_15]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1466,plain,( X0 = X0 ),theory(equality) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2233,plain,
% 2.40/0.97      ( sK5 = sK5 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_1466]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2408,plain,
% 2.40/0.97      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_1467]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3178,plain,
% 2.40/0.97      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_2408]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3179,plain,
% 2.40/0.97      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_3178]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4077,plain,
% 2.40/0.97      ( sK5 = k1_xboole_0 ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_3930,c_32,c_30,c_2129,c_2147,c_2212,c_2217,c_2233,
% 2.40/0.97                 c_3179,c_3842]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_29,plain,
% 2.40/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.97      | k1_relset_1(X1,X2,X0) = X1
% 2.40/0.97      | k1_xboole_0 = X2 ),
% 2.40/0.97      inference(cnf_transformation,[],[f83]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_33,negated_conjecture,
% 2.40/0.97      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 2.40/0.97      inference(cnf_transformation,[],[f104]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_508,plain,
% 2.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.97      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 2.40/0.97      | k1_relset_1(X1,X2,X0) = X1
% 2.40/0.97      | sK4 != X2
% 2.40/0.97      | sK5 != X0
% 2.40/0.97      | k1_xboole_0 = X2 ),
% 2.40/0.97      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_509,plain,
% 2.40/0.97      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.40/0.97      | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 2.40/0.97      | k1_xboole_0 = sK4 ),
% 2.40/0.97      inference(unflattening,[status(thm)],[c_508]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_31,negated_conjecture,
% 2.40/0.97      ( k1_xboole_0 != sK4 ),
% 2.40/0.97      inference(cnf_transformation,[],[f92]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_511,plain,
% 2.40/0.97      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_509,c_32,c_31]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_21,plain,
% 2.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.97      | ~ r2_hidden(X3,X1)
% 2.40/0.97      | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
% 2.40/0.97      | k1_relset_1(X1,X2,X0) != X1 ),
% 2.40/0.97      inference(cnf_transformation,[],[f82]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1919,plain,
% 2.40/0.97      ( k1_relset_1(X0,X1,X2) != X0
% 2.40/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.40/0.97      | r2_hidden(X3,X0) != iProver_top
% 2.40/0.97      | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3481,plain,
% 2.40/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.40/0.97      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.40/0.97      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_511,c_1919]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3740,plain,
% 2.40/0.97      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.40/0.97      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_3481,c_37]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4081,plain,
% 2.40/0.97      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.40/0.97      | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 2.40/0.97      inference(demodulation,[status(thm)],[c_4077,c_3740]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_10,plain,
% 2.40/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.40/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1926,plain,
% 2.40/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_11,plain,
% 2.40/0.97      ( m1_subset_1(X0,X1)
% 2.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.40/0.97      | ~ r2_hidden(X0,X2) ),
% 2.40/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1925,plain,
% 2.40/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 2.40/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.40/0.97      | r2_hidden(X0,X2) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3462,plain,
% 2.40/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 2.40/0.97      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_1926,c_1925]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3,plain,
% 2.40/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 2.40/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_17,plain,
% 2.40/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.40/0.97      inference(cnf_transformation,[],[f76]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_698,plain,
% 2.40/0.97      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.40/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_699,plain,
% 2.40/0.97      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.40/0.97      inference(unflattening,[status(thm)],[c_698]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_700,plain,
% 2.40/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3583,plain,
% 2.40/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_3462,c_700]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4313,plain,
% 2.40/0.97      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.40/0.97      inference(forward_subsumption_resolution,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_4081,c_3583]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4317,plain,
% 2.40/0.97      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_1935,c_4313]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4,plain,
% 2.40/0.97      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1932,plain,
% 2.40/0.97      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4510,plain,
% 2.40/0.97      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_4317,c_1932]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3923,plain,
% 2.40/0.97      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 2.40/0.97      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.40/0.97      inference(demodulation,[status(thm)],[c_3918,c_2156]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4410,plain,
% 2.40/0.97      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 2.40/0.97      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
% 2.40/0.97      inference(light_normalisation,[status(thm)],[c_3923,c_4077]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4538,plain,
% 2.40/0.97      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k2_relat_1(k1_xboole_0) ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_4510,c_4410]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1920,plain,
% 2.40/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.40/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3189,plain,
% 2.40/0.97      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_1916,c_1920]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3196,plain,
% 2.40/0.97      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
% 2.40/0.97      inference(demodulation,[status(thm)],[c_3189,c_30]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_4083,plain,
% 2.40/0.97      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
% 2.40/0.97      inference(demodulation,[status(thm)],[c_4077,c_3196]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(contradiction,plain,
% 2.40/0.97      ( $false ),
% 2.40/0.97      inference(minisat,[status(thm)],[c_4538,c_4083]) ).
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/0.97  
% 2.40/0.97  ------                               Statistics
% 2.40/0.97  
% 2.40/0.97  ------ General
% 2.40/0.97  
% 2.40/0.97  abstr_ref_over_cycles:                  0
% 2.40/0.97  abstr_ref_under_cycles:                 0
% 2.40/0.97  gc_basic_clause_elim:                   0
% 2.40/0.97  forced_gc_time:                         0
% 2.40/0.97  parsing_time:                           0.011
% 2.40/0.97  unif_index_cands_time:                  0.
% 2.40/0.97  unif_index_add_time:                    0.
% 2.40/0.97  orderings_time:                         0.
% 2.40/0.97  out_proof_time:                         0.012
% 2.40/0.97  total_time:                             0.154
% 2.40/0.97  num_of_symbols:                         54
% 2.40/0.97  num_of_terms:                           4266
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing
% 2.40/0.97  
% 2.40/0.97  num_of_splits:                          0
% 2.40/0.97  num_of_split_atoms:                     0
% 2.40/0.97  num_of_reused_defs:                     0
% 2.40/0.97  num_eq_ax_congr_red:                    28
% 2.40/0.97  num_of_sem_filtered_clauses:            1
% 2.40/0.97  num_of_subtypes:                        0
% 2.40/0.97  monotx_restored_types:                  0
% 2.40/0.97  sat_num_of_epr_types:                   0
% 2.40/0.97  sat_num_of_non_cyclic_types:            0
% 2.40/0.97  sat_guarded_non_collapsed_types:        0
% 2.40/0.97  num_pure_diseq_elim:                    0
% 2.40/0.97  simp_replaced_by:                       0
% 2.40/0.97  res_preprocessed:                       150
% 2.40/0.97  prep_upred:                             0
% 2.40/0.97  prep_unflattend:                        142
% 2.40/0.97  smt_new_axioms:                         0
% 2.40/0.97  pred_elim_cands:                        4
% 2.40/0.97  pred_elim:                              3
% 2.40/0.97  pred_elim_cl:                           7
% 2.40/0.97  pred_elim_cycles:                       7
% 2.40/0.97  merged_defs:                            0
% 2.40/0.97  merged_defs_ncl:                        0
% 2.40/0.97  bin_hyper_res:                          0
% 2.40/0.97  prep_cycles:                            4
% 2.40/0.97  pred_elim_time:                         0.014
% 2.40/0.97  splitting_time:                         0.
% 2.40/0.97  sem_filter_time:                        0.
% 2.40/0.97  monotx_time:                            0.
% 2.40/0.97  subtype_inf_time:                       0.
% 2.40/0.97  
% 2.40/0.97  ------ Problem properties
% 2.40/0.97  
% 2.40/0.97  clauses:                                28
% 2.40/0.97  conjectures:                            3
% 2.40/0.97  epr:                                    5
% 2.40/0.97  horn:                                   24
% 2.40/0.97  ground:                                 6
% 2.40/0.97  unary:                                  10
% 2.40/0.97  binary:                                 7
% 2.40/0.97  lits:                                   61
% 2.40/0.97  lits_eq:                                23
% 2.40/0.97  fd_pure:                                0
% 2.40/0.97  fd_pseudo:                              0
% 2.40/0.97  fd_cond:                                3
% 2.40/0.97  fd_pseudo_cond:                         1
% 2.40/0.97  ac_symbols:                             0
% 2.40/0.97  
% 2.40/0.97  ------ Propositional Solver
% 2.40/0.97  
% 2.40/0.97  prop_solver_calls:                      28
% 2.40/0.97  prop_fast_solver_calls:                 1012
% 2.40/0.97  smt_solver_calls:                       0
% 2.40/0.97  smt_fast_solver_calls:                  0
% 2.40/0.97  prop_num_of_clauses:                    1482
% 2.40/0.97  prop_preprocess_simplified:             6045
% 2.40/0.97  prop_fo_subsumed:                       20
% 2.40/0.97  prop_solver_time:                       0.
% 2.40/0.97  smt_solver_time:                        0.
% 2.40/0.97  smt_fast_solver_time:                   0.
% 2.40/0.97  prop_fast_solver_time:                  0.
% 2.40/0.97  prop_unsat_core_time:                   0.
% 2.40/0.97  
% 2.40/0.97  ------ QBF
% 2.40/0.97  
% 2.40/0.97  qbf_q_res:                              0
% 2.40/0.97  qbf_num_tautologies:                    0
% 2.40/0.97  qbf_prep_cycles:                        0
% 2.40/0.97  
% 2.40/0.97  ------ BMC1
% 2.40/0.97  
% 2.40/0.97  bmc1_current_bound:                     -1
% 2.40/0.97  bmc1_last_solved_bound:                 -1
% 2.40/0.97  bmc1_unsat_core_size:                   -1
% 2.40/0.97  bmc1_unsat_core_parents_size:           -1
% 2.40/0.97  bmc1_merge_next_fun:                    0
% 2.40/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.40/0.97  
% 2.40/0.97  ------ Instantiation
% 2.40/0.97  
% 2.40/0.97  inst_num_of_clauses:                    461
% 2.40/0.97  inst_num_in_passive:                    174
% 2.40/0.97  inst_num_in_active:                     194
% 2.40/0.97  inst_num_in_unprocessed:                93
% 2.40/0.97  inst_num_of_loops:                      260
% 2.40/0.97  inst_num_of_learning_restarts:          0
% 2.40/0.97  inst_num_moves_active_passive:          63
% 2.40/0.97  inst_lit_activity:                      0
% 2.40/0.97  inst_lit_activity_moves:                0
% 2.40/0.97  inst_num_tautologies:                   0
% 2.40/0.97  inst_num_prop_implied:                  0
% 2.40/0.97  inst_num_existing_simplified:           0
% 2.40/0.97  inst_num_eq_res_simplified:             0
% 2.40/0.97  inst_num_child_elim:                    0
% 2.40/0.97  inst_num_of_dismatching_blockings:      131
% 2.40/0.97  inst_num_of_non_proper_insts:           332
% 2.40/0.97  inst_num_of_duplicates:                 0
% 2.40/0.97  inst_inst_num_from_inst_to_res:         0
% 2.40/0.97  inst_dismatching_checking_time:         0.
% 2.40/0.97  
% 2.40/0.97  ------ Resolution
% 2.40/0.97  
% 2.40/0.97  res_num_of_clauses:                     0
% 2.40/0.97  res_num_in_passive:                     0
% 2.40/0.97  res_num_in_active:                      0
% 2.40/0.97  res_num_of_loops:                       154
% 2.40/0.97  res_forward_subset_subsumed:            39
% 2.40/0.97  res_backward_subset_subsumed:           0
% 2.40/0.97  res_forward_subsumed:                   3
% 2.40/0.97  res_backward_subsumed:                  3
% 2.40/0.97  res_forward_subsumption_resolution:     0
% 2.40/0.97  res_backward_subsumption_resolution:    0
% 2.40/0.97  res_clause_to_clause_subsumption:       194
% 2.40/0.97  res_orphan_elimination:                 0
% 2.40/0.97  res_tautology_del:                      44
% 2.40/0.97  res_num_eq_res_simplified:              0
% 2.40/0.97  res_num_sel_changes:                    0
% 2.40/0.97  res_moves_from_active_to_pass:          0
% 2.40/0.97  
% 2.40/0.97  ------ Superposition
% 2.40/0.97  
% 2.40/0.97  sup_time_total:                         0.
% 2.40/0.97  sup_time_generating:                    0.
% 2.40/0.97  sup_time_sim_full:                      0.
% 2.40/0.97  sup_time_sim_immed:                     0.
% 2.40/0.97  
% 2.40/0.97  sup_num_of_clauses:                     41
% 2.40/0.97  sup_num_in_active:                      34
% 2.40/0.97  sup_num_in_passive:                     7
% 2.40/0.97  sup_num_of_loops:                       51
% 2.40/0.97  sup_fw_superposition:                   26
% 2.40/0.97  sup_bw_superposition:                   36
% 2.40/0.97  sup_immediate_simplified:               10
% 2.40/0.97  sup_given_eliminated:                   1
% 2.40/0.97  comparisons_done:                       0
% 2.40/0.97  comparisons_avoided:                    0
% 2.40/0.97  
% 2.40/0.97  ------ Simplifications
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  sim_fw_subset_subsumed:                 7
% 2.40/0.97  sim_bw_subset_subsumed:                 5
% 2.40/0.97  sim_fw_subsumed:                        8
% 2.40/0.97  sim_bw_subsumed:                        0
% 2.40/0.97  sim_fw_subsumption_res:                 1
% 2.40/0.97  sim_bw_subsumption_res:                 0
% 2.40/0.97  sim_tautology_del:                      1
% 2.40/0.97  sim_eq_tautology_del:                   7
% 2.40/0.97  sim_eq_res_simp:                        1
% 2.40/0.97  sim_fw_demodulated:                     0
% 2.40/0.97  sim_bw_demodulated:                     19
% 2.40/0.97  sim_light_normalised:                   2
% 2.40/0.97  sim_joinable_taut:                      0
% 2.40/0.97  sim_joinable_simp:                      0
% 2.40/0.97  sim_ac_normalised:                      0
% 2.40/0.97  sim_smt_subsumption:                    0
% 2.40/0.97  
%------------------------------------------------------------------------------
