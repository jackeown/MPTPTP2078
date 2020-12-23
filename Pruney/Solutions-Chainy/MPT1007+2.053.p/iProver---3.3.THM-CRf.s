%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:52 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 375 expanded)
%              Number of clauses        :   55 (  89 expanded)
%              Number of leaves         :   19 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  379 (1180 expanded)
%              Number of equality atoms :  134 ( 394 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f44])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
      & k1_xboole_0 != sK6
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
      & v1_funct_2(sK7,k1_tarski(sK5),sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    & k1_xboole_0 != sK6
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
    & v1_funct_2(sK7,k1_tarski(sK5),sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f41,f56])).

fof(f89,plain,(
    v1_funct_2(sK7,k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f93])).

fof(f100,plain,(
    v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
    inference(definition_unfolding,[],[f89,f94])).

fof(f90,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) ),
    inference(cnf_transformation,[],[f57])).

fof(f99,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(definition_unfolding,[],[f90,f94])).

fof(f91,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f53,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK4(X1,X2),X6),X2)
        & r2_hidden(sK4(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK4(X1,X2),X6),X2)
            & r2_hidden(sK4(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f51,f53,f52])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f93])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f42])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f63,f94])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1274,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1271,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2164,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1271])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X2
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_599,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
    | k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5)
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_601,plain,
    ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_29,c_28])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK3(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1267,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3056,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(sK7,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_601,c_1267])).

cnf(c_34,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3161,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(sK7,X0)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3056,c_34])).

cnf(c_3170,plain,
    ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK5,sK5,sK5,sK5)),sK3(sK7,sK0(k2_enumset1(sK5,sK5,sK5,sK5)))),sK7) = iProver_top
    | v1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2164,c_3161])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1278,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3661,plain,
    ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK5,sK5,sK5,sK5)),sK3(sK7,sK0(k2_enumset1(sK5,sK5,sK5,sK5)))),sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3170,c_1278])).

cnf(c_1263,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1273,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2324,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1273])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1275,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2393,plain,
    ( sK5 = X0
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_1275])).

cnf(c_3663,plain,
    ( sK0(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_3661,c_2393])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_406,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_407,plain,
    ( r2_hidden(X0,k1_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1261,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_408,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1464,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1465,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_1499,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1261,c_34,c_408,c_1465])).

cnf(c_1500,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_1499])).

cnf(c_3664,plain,
    ( r2_hidden(sK0(k2_enumset1(sK5,sK5,sK5,sK5)),k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_1500])).

cnf(c_6176,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3663,c_3664])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_382,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_16])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_31])).

cnf(c_437,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X2),X1) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_1259,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X2,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_1790,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1259])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1264,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1797,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1264])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6176,c_1797])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.89/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/0.99  
% 2.89/0.99  ------  iProver source info
% 2.89/0.99  
% 2.89/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.89/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/0.99  git: non_committed_changes: false
% 2.89/0.99  git: last_make_outside_of_git: false
% 2.89/0.99  
% 2.89/0.99  ------ 
% 2.89/0.99  
% 2.89/0.99  ------ Input Options
% 2.89/0.99  
% 2.89/0.99  --out_options                           all
% 2.89/0.99  --tptp_safe_out                         true
% 2.89/0.99  --problem_path                          ""
% 2.89/0.99  --include_path                          ""
% 2.89/0.99  --clausifier                            res/vclausify_rel
% 2.89/0.99  --clausifier_options                    --mode clausify
% 2.89/0.99  --stdin                                 false
% 2.89/0.99  --stats_out                             all
% 2.89/0.99  
% 2.89/0.99  ------ General Options
% 2.89/0.99  
% 2.89/0.99  --fof                                   false
% 2.89/0.99  --time_out_real                         305.
% 2.89/0.99  --time_out_virtual                      -1.
% 2.89/0.99  --symbol_type_check                     false
% 2.89/0.99  --clausify_out                          false
% 2.89/0.99  --sig_cnt_out                           false
% 2.89/0.99  --trig_cnt_out                          false
% 2.89/0.99  --trig_cnt_out_tolerance                1.
% 2.89/0.99  --trig_cnt_out_sk_spl                   false
% 2.89/0.99  --abstr_cl_out                          false
% 2.89/0.99  
% 2.89/0.99  ------ Global Options
% 2.89/0.99  
% 2.89/0.99  --schedule                              default
% 2.89/0.99  --add_important_lit                     false
% 2.89/0.99  --prop_solver_per_cl                    1000
% 2.89/0.99  --min_unsat_core                        false
% 2.89/0.99  --soft_assumptions                      false
% 2.89/0.99  --soft_lemma_size                       3
% 2.89/0.99  --prop_impl_unit_size                   0
% 2.89/0.99  --prop_impl_unit                        []
% 2.89/0.99  --share_sel_clauses                     true
% 2.89/0.99  --reset_solvers                         false
% 2.89/0.99  --bc_imp_inh                            [conj_cone]
% 2.89/0.99  --conj_cone_tolerance                   3.
% 2.89/0.99  --extra_neg_conj                        none
% 2.89/0.99  --large_theory_mode                     true
% 2.89/0.99  --prolific_symb_bound                   200
% 2.89/0.99  --lt_threshold                          2000
% 2.89/0.99  --clause_weak_htbl                      true
% 2.89/0.99  --gc_record_bc_elim                     false
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing Options
% 2.89/0.99  
% 2.89/0.99  --preprocessing_flag                    true
% 2.89/0.99  --time_out_prep_mult                    0.1
% 2.89/0.99  --splitting_mode                        input
% 2.89/0.99  --splitting_grd                         true
% 2.89/0.99  --splitting_cvd                         false
% 2.89/0.99  --splitting_cvd_svl                     false
% 2.89/0.99  --splitting_nvd                         32
% 2.89/0.99  --sub_typing                            true
% 2.89/0.99  --prep_gs_sim                           true
% 2.89/0.99  --prep_unflatten                        true
% 2.89/0.99  --prep_res_sim                          true
% 2.89/0.99  --prep_upred                            true
% 2.89/0.99  --prep_sem_filter                       exhaustive
% 2.89/0.99  --prep_sem_filter_out                   false
% 2.89/0.99  --pred_elim                             true
% 2.89/0.99  --res_sim_input                         true
% 2.89/0.99  --eq_ax_congr_red                       true
% 2.89/0.99  --pure_diseq_elim                       true
% 2.89/0.99  --brand_transform                       false
% 2.89/0.99  --non_eq_to_eq                          false
% 2.89/0.99  --prep_def_merge                        true
% 2.89/0.99  --prep_def_merge_prop_impl              false
% 2.89/0.99  --prep_def_merge_mbd                    true
% 2.89/0.99  --prep_def_merge_tr_red                 false
% 2.89/0.99  --prep_def_merge_tr_cl                  false
% 2.89/0.99  --smt_preprocessing                     true
% 2.89/0.99  --smt_ac_axioms                         fast
% 2.89/0.99  --preprocessed_out                      false
% 2.89/0.99  --preprocessed_stats                    false
% 2.89/0.99  
% 2.89/0.99  ------ Abstraction refinement Options
% 2.89/0.99  
% 2.89/0.99  --abstr_ref                             []
% 2.89/0.99  --abstr_ref_prep                        false
% 2.89/0.99  --abstr_ref_until_sat                   false
% 2.89/0.99  --abstr_ref_sig_restrict                funpre
% 2.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.99  --abstr_ref_under                       []
% 2.89/0.99  
% 2.89/0.99  ------ SAT Options
% 2.89/0.99  
% 2.89/0.99  --sat_mode                              false
% 2.89/0.99  --sat_fm_restart_options                ""
% 2.89/0.99  --sat_gr_def                            false
% 2.89/0.99  --sat_epr_types                         true
% 2.89/0.99  --sat_non_cyclic_types                  false
% 2.89/0.99  --sat_finite_models                     false
% 2.89/0.99  --sat_fm_lemmas                         false
% 2.89/0.99  --sat_fm_prep                           false
% 2.89/0.99  --sat_fm_uc_incr                        true
% 2.89/0.99  --sat_out_model                         small
% 2.89/0.99  --sat_out_clauses                       false
% 2.89/0.99  
% 2.89/0.99  ------ QBF Options
% 2.89/0.99  
% 2.89/0.99  --qbf_mode                              false
% 2.89/0.99  --qbf_elim_univ                         false
% 2.89/0.99  --qbf_dom_inst                          none
% 2.89/0.99  --qbf_dom_pre_inst                      false
% 2.89/0.99  --qbf_sk_in                             false
% 2.89/0.99  --qbf_pred_elim                         true
% 2.89/0.99  --qbf_split                             512
% 2.89/0.99  
% 2.89/0.99  ------ BMC1 Options
% 2.89/0.99  
% 2.89/0.99  --bmc1_incremental                      false
% 2.89/0.99  --bmc1_axioms                           reachable_all
% 2.89/0.99  --bmc1_min_bound                        0
% 2.89/0.99  --bmc1_max_bound                        -1
% 2.89/0.99  --bmc1_max_bound_default                -1
% 2.89/0.99  --bmc1_symbol_reachability              true
% 2.89/0.99  --bmc1_property_lemmas                  false
% 2.89/0.99  --bmc1_k_induction                      false
% 2.89/0.99  --bmc1_non_equiv_states                 false
% 2.89/0.99  --bmc1_deadlock                         false
% 2.89/0.99  --bmc1_ucm                              false
% 2.89/0.99  --bmc1_add_unsat_core                   none
% 2.89/0.99  --bmc1_unsat_core_children              false
% 2.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.99  --bmc1_out_stat                         full
% 2.89/0.99  --bmc1_ground_init                      false
% 2.89/0.99  --bmc1_pre_inst_next_state              false
% 2.89/0.99  --bmc1_pre_inst_state                   false
% 2.89/0.99  --bmc1_pre_inst_reach_state             false
% 2.89/0.99  --bmc1_out_unsat_core                   false
% 2.89/0.99  --bmc1_aig_witness_out                  false
% 2.89/0.99  --bmc1_verbose                          false
% 2.89/0.99  --bmc1_dump_clauses_tptp                false
% 2.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.99  --bmc1_dump_file                        -
% 2.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.99  --bmc1_ucm_extend_mode                  1
% 2.89/0.99  --bmc1_ucm_init_mode                    2
% 2.89/0.99  --bmc1_ucm_cone_mode                    none
% 2.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.99  --bmc1_ucm_relax_model                  4
% 2.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.99  --bmc1_ucm_layered_model                none
% 2.89/0.99  --bmc1_ucm_max_lemma_size               10
% 2.89/0.99  
% 2.89/0.99  ------ AIG Options
% 2.89/0.99  
% 2.89/0.99  --aig_mode                              false
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation Options
% 2.89/0.99  
% 2.89/0.99  --instantiation_flag                    true
% 2.89/0.99  --inst_sos_flag                         false
% 2.89/0.99  --inst_sos_phase                        true
% 2.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel_side                     num_symb
% 2.89/0.99  --inst_solver_per_active                1400
% 2.89/0.99  --inst_solver_calls_frac                1.
% 2.89/0.99  --inst_passive_queue_type               priority_queues
% 2.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.99  --inst_passive_queues_freq              [25;2]
% 2.89/0.99  --inst_dismatching                      true
% 2.89/0.99  --inst_eager_unprocessed_to_passive     true
% 2.89/0.99  --inst_prop_sim_given                   true
% 2.89/0.99  --inst_prop_sim_new                     false
% 2.89/0.99  --inst_subs_new                         false
% 2.89/0.99  --inst_eq_res_simp                      false
% 2.89/0.99  --inst_subs_given                       false
% 2.89/0.99  --inst_orphan_elimination               true
% 2.89/0.99  --inst_learning_loop_flag               true
% 2.89/0.99  --inst_learning_start                   3000
% 2.89/0.99  --inst_learning_factor                  2
% 2.89/0.99  --inst_start_prop_sim_after_learn       3
% 2.89/0.99  --inst_sel_renew                        solver
% 2.89/0.99  --inst_lit_activity_flag                true
% 2.89/0.99  --inst_restr_to_given                   false
% 2.89/0.99  --inst_activity_threshold               500
% 2.89/0.99  --inst_out_proof                        true
% 2.89/0.99  
% 2.89/0.99  ------ Resolution Options
% 2.89/0.99  
% 2.89/0.99  --resolution_flag                       true
% 2.89/0.99  --res_lit_sel                           adaptive
% 2.89/0.99  --res_lit_sel_side                      none
% 2.89/0.99  --res_ordering                          kbo
% 2.89/0.99  --res_to_prop_solver                    active
% 2.89/0.99  --res_prop_simpl_new                    false
% 2.89/0.99  --res_prop_simpl_given                  true
% 2.89/0.99  --res_passive_queue_type                priority_queues
% 2.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.99  --res_passive_queues_freq               [15;5]
% 2.89/0.99  --res_forward_subs                      full
% 2.89/0.99  --res_backward_subs                     full
% 2.89/0.99  --res_forward_subs_resolution           true
% 2.89/0.99  --res_backward_subs_resolution          true
% 2.89/0.99  --res_orphan_elimination                true
% 2.89/0.99  --res_time_limit                        2.
% 2.89/0.99  --res_out_proof                         true
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Options
% 2.89/0.99  
% 2.89/0.99  --superposition_flag                    true
% 2.89/0.99  --sup_passive_queue_type                priority_queues
% 2.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.99  --demod_completeness_check              fast
% 2.89/0.99  --demod_use_ground                      true
% 2.89/0.99  --sup_to_prop_solver                    passive
% 2.89/0.99  --sup_prop_simpl_new                    true
% 2.89/0.99  --sup_prop_simpl_given                  true
% 2.89/0.99  --sup_fun_splitting                     false
% 2.89/0.99  --sup_smt_interval                      50000
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Simplification Setup
% 2.89/0.99  
% 2.89/0.99  --sup_indices_passive                   []
% 2.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_full_bw                           [BwDemod]
% 2.89/0.99  --sup_immed_triv                        [TrivRules]
% 2.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_immed_bw_main                     []
% 2.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  
% 2.89/0.99  ------ Combination Options
% 2.89/0.99  
% 2.89/0.99  --comb_res_mult                         3
% 2.89/0.99  --comb_sup_mult                         2
% 2.89/0.99  --comb_inst_mult                        10
% 2.89/0.99  
% 2.89/0.99  ------ Debug Options
% 2.89/0.99  
% 2.89/0.99  --dbg_backtrace                         false
% 2.89/0.99  --dbg_dump_prop_clauses                 false
% 2.89/0.99  --dbg_dump_prop_clauses_file            -
% 2.89/0.99  --dbg_out_stat                          false
% 2.89/0.99  ------ Parsing...
% 2.89/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/0.99  ------ Proving...
% 2.89/0.99  ------ Problem Properties 
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  clauses                                 25
% 2.89/0.99  conjectures                             3
% 2.89/0.99  EPR                                     3
% 2.89/0.99  Horn                                    21
% 2.89/0.99  unary                                   8
% 2.89/0.99  binary                                  4
% 2.89/0.99  lits                                    57
% 2.89/0.99  lits eq                                 13
% 2.89/0.99  fd_pure                                 0
% 2.89/0.99  fd_pseudo                               0
% 2.89/0.99  fd_cond                                 1
% 2.89/0.99  fd_pseudo_cond                          2
% 2.89/0.99  AC symbols                              0
% 2.89/0.99  
% 2.89/0.99  ------ Schedule dynamic 5 is on 
% 2.89/0.99  
% 2.89/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  ------ 
% 2.89/0.99  Current options:
% 2.89/0.99  ------ 
% 2.89/0.99  
% 2.89/0.99  ------ Input Options
% 2.89/0.99  
% 2.89/0.99  --out_options                           all
% 2.89/0.99  --tptp_safe_out                         true
% 2.89/0.99  --problem_path                          ""
% 2.89/0.99  --include_path                          ""
% 2.89/0.99  --clausifier                            res/vclausify_rel
% 2.89/0.99  --clausifier_options                    --mode clausify
% 2.89/0.99  --stdin                                 false
% 2.89/0.99  --stats_out                             all
% 2.89/0.99  
% 2.89/0.99  ------ General Options
% 2.89/0.99  
% 2.89/0.99  --fof                                   false
% 2.89/0.99  --time_out_real                         305.
% 2.89/0.99  --time_out_virtual                      -1.
% 2.89/0.99  --symbol_type_check                     false
% 2.89/0.99  --clausify_out                          false
% 2.89/0.99  --sig_cnt_out                           false
% 2.89/0.99  --trig_cnt_out                          false
% 2.89/0.99  --trig_cnt_out_tolerance                1.
% 2.89/0.99  --trig_cnt_out_sk_spl                   false
% 2.89/0.99  --abstr_cl_out                          false
% 2.89/0.99  
% 2.89/0.99  ------ Global Options
% 2.89/0.99  
% 2.89/0.99  --schedule                              default
% 2.89/0.99  --add_important_lit                     false
% 2.89/0.99  --prop_solver_per_cl                    1000
% 2.89/0.99  --min_unsat_core                        false
% 2.89/0.99  --soft_assumptions                      false
% 2.89/0.99  --soft_lemma_size                       3
% 2.89/0.99  --prop_impl_unit_size                   0
% 2.89/0.99  --prop_impl_unit                        []
% 2.89/0.99  --share_sel_clauses                     true
% 2.89/0.99  --reset_solvers                         false
% 2.89/0.99  --bc_imp_inh                            [conj_cone]
% 2.89/0.99  --conj_cone_tolerance                   3.
% 2.89/0.99  --extra_neg_conj                        none
% 2.89/0.99  --large_theory_mode                     true
% 2.89/0.99  --prolific_symb_bound                   200
% 2.89/0.99  --lt_threshold                          2000
% 2.89/0.99  --clause_weak_htbl                      true
% 2.89/0.99  --gc_record_bc_elim                     false
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing Options
% 2.89/0.99  
% 2.89/0.99  --preprocessing_flag                    true
% 2.89/0.99  --time_out_prep_mult                    0.1
% 2.89/0.99  --splitting_mode                        input
% 2.89/0.99  --splitting_grd                         true
% 2.89/0.99  --splitting_cvd                         false
% 2.89/0.99  --splitting_cvd_svl                     false
% 2.89/0.99  --splitting_nvd                         32
% 2.89/0.99  --sub_typing                            true
% 2.89/0.99  --prep_gs_sim                           true
% 2.89/0.99  --prep_unflatten                        true
% 2.89/0.99  --prep_res_sim                          true
% 2.89/0.99  --prep_upred                            true
% 2.89/0.99  --prep_sem_filter                       exhaustive
% 2.89/0.99  --prep_sem_filter_out                   false
% 2.89/0.99  --pred_elim                             true
% 2.89/0.99  --res_sim_input                         true
% 2.89/0.99  --eq_ax_congr_red                       true
% 2.89/0.99  --pure_diseq_elim                       true
% 2.89/0.99  --brand_transform                       false
% 2.89/0.99  --non_eq_to_eq                          false
% 2.89/0.99  --prep_def_merge                        true
% 2.89/0.99  --prep_def_merge_prop_impl              false
% 2.89/0.99  --prep_def_merge_mbd                    true
% 2.89/0.99  --prep_def_merge_tr_red                 false
% 2.89/0.99  --prep_def_merge_tr_cl                  false
% 2.89/0.99  --smt_preprocessing                     true
% 2.89/0.99  --smt_ac_axioms                         fast
% 2.89/0.99  --preprocessed_out                      false
% 2.89/0.99  --preprocessed_stats                    false
% 2.89/0.99  
% 2.89/0.99  ------ Abstraction refinement Options
% 2.89/0.99  
% 2.89/0.99  --abstr_ref                             []
% 2.89/0.99  --abstr_ref_prep                        false
% 2.89/0.99  --abstr_ref_until_sat                   false
% 2.89/0.99  --abstr_ref_sig_restrict                funpre
% 2.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.99  --abstr_ref_under                       []
% 2.89/0.99  
% 2.89/0.99  ------ SAT Options
% 2.89/0.99  
% 2.89/0.99  --sat_mode                              false
% 2.89/0.99  --sat_fm_restart_options                ""
% 2.89/0.99  --sat_gr_def                            false
% 2.89/0.99  --sat_epr_types                         true
% 2.89/0.99  --sat_non_cyclic_types                  false
% 2.89/0.99  --sat_finite_models                     false
% 2.89/0.99  --sat_fm_lemmas                         false
% 2.89/0.99  --sat_fm_prep                           false
% 2.89/0.99  --sat_fm_uc_incr                        true
% 2.89/0.99  --sat_out_model                         small
% 2.89/0.99  --sat_out_clauses                       false
% 2.89/0.99  
% 2.89/0.99  ------ QBF Options
% 2.89/0.99  
% 2.89/0.99  --qbf_mode                              false
% 2.89/0.99  --qbf_elim_univ                         false
% 2.89/0.99  --qbf_dom_inst                          none
% 2.89/0.99  --qbf_dom_pre_inst                      false
% 2.89/0.99  --qbf_sk_in                             false
% 2.89/0.99  --qbf_pred_elim                         true
% 2.89/0.99  --qbf_split                             512
% 2.89/0.99  
% 2.89/0.99  ------ BMC1 Options
% 2.89/0.99  
% 2.89/0.99  --bmc1_incremental                      false
% 2.89/0.99  --bmc1_axioms                           reachable_all
% 2.89/0.99  --bmc1_min_bound                        0
% 2.89/0.99  --bmc1_max_bound                        -1
% 2.89/0.99  --bmc1_max_bound_default                -1
% 2.89/0.99  --bmc1_symbol_reachability              true
% 2.89/0.99  --bmc1_property_lemmas                  false
% 2.89/0.99  --bmc1_k_induction                      false
% 2.89/0.99  --bmc1_non_equiv_states                 false
% 2.89/0.99  --bmc1_deadlock                         false
% 2.89/0.99  --bmc1_ucm                              false
% 2.89/0.99  --bmc1_add_unsat_core                   none
% 2.89/0.99  --bmc1_unsat_core_children              false
% 2.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.99  --bmc1_out_stat                         full
% 2.89/0.99  --bmc1_ground_init                      false
% 2.89/0.99  --bmc1_pre_inst_next_state              false
% 2.89/0.99  --bmc1_pre_inst_state                   false
% 2.89/0.99  --bmc1_pre_inst_reach_state             false
% 2.89/0.99  --bmc1_out_unsat_core                   false
% 2.89/0.99  --bmc1_aig_witness_out                  false
% 2.89/0.99  --bmc1_verbose                          false
% 2.89/0.99  --bmc1_dump_clauses_tptp                false
% 2.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.99  --bmc1_dump_file                        -
% 2.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.99  --bmc1_ucm_extend_mode                  1
% 2.89/0.99  --bmc1_ucm_init_mode                    2
% 2.89/0.99  --bmc1_ucm_cone_mode                    none
% 2.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.99  --bmc1_ucm_relax_model                  4
% 2.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.99  --bmc1_ucm_layered_model                none
% 2.89/0.99  --bmc1_ucm_max_lemma_size               10
% 2.89/0.99  
% 2.89/0.99  ------ AIG Options
% 2.89/0.99  
% 2.89/0.99  --aig_mode                              false
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation Options
% 2.89/0.99  
% 2.89/0.99  --instantiation_flag                    true
% 2.89/0.99  --inst_sos_flag                         false
% 2.89/0.99  --inst_sos_phase                        true
% 2.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel_side                     none
% 2.89/0.99  --inst_solver_per_active                1400
% 2.89/0.99  --inst_solver_calls_frac                1.
% 2.89/0.99  --inst_passive_queue_type               priority_queues
% 2.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.99  --inst_passive_queues_freq              [25;2]
% 2.89/0.99  --inst_dismatching                      true
% 2.89/0.99  --inst_eager_unprocessed_to_passive     true
% 2.89/0.99  --inst_prop_sim_given                   true
% 2.89/0.99  --inst_prop_sim_new                     false
% 2.89/0.99  --inst_subs_new                         false
% 2.89/0.99  --inst_eq_res_simp                      false
% 2.89/0.99  --inst_subs_given                       false
% 2.89/0.99  --inst_orphan_elimination               true
% 2.89/0.99  --inst_learning_loop_flag               true
% 2.89/0.99  --inst_learning_start                   3000
% 2.89/0.99  --inst_learning_factor                  2
% 2.89/0.99  --inst_start_prop_sim_after_learn       3
% 2.89/0.99  --inst_sel_renew                        solver
% 2.89/0.99  --inst_lit_activity_flag                true
% 2.89/0.99  --inst_restr_to_given                   false
% 2.89/0.99  --inst_activity_threshold               500
% 2.89/0.99  --inst_out_proof                        true
% 2.89/0.99  
% 2.89/0.99  ------ Resolution Options
% 2.89/0.99  
% 2.89/0.99  --resolution_flag                       false
% 2.89/0.99  --res_lit_sel                           adaptive
% 2.89/0.99  --res_lit_sel_side                      none
% 2.89/0.99  --res_ordering                          kbo
% 2.89/0.99  --res_to_prop_solver                    active
% 2.89/0.99  --res_prop_simpl_new                    false
% 2.89/0.99  --res_prop_simpl_given                  true
% 2.89/0.99  --res_passive_queue_type                priority_queues
% 2.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.99  --res_passive_queues_freq               [15;5]
% 2.89/0.99  --res_forward_subs                      full
% 2.89/0.99  --res_backward_subs                     full
% 2.89/0.99  --res_forward_subs_resolution           true
% 2.89/0.99  --res_backward_subs_resolution          true
% 2.89/0.99  --res_orphan_elimination                true
% 2.89/0.99  --res_time_limit                        2.
% 2.89/0.99  --res_out_proof                         true
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Options
% 2.89/0.99  
% 2.89/0.99  --superposition_flag                    true
% 2.89/0.99  --sup_passive_queue_type                priority_queues
% 2.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.99  --demod_completeness_check              fast
% 2.89/0.99  --demod_use_ground                      true
% 2.89/0.99  --sup_to_prop_solver                    passive
% 2.89/0.99  --sup_prop_simpl_new                    true
% 2.89/0.99  --sup_prop_simpl_given                  true
% 2.89/0.99  --sup_fun_splitting                     false
% 2.89/0.99  --sup_smt_interval                      50000
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Simplification Setup
% 2.89/0.99  
% 2.89/0.99  --sup_indices_passive                   []
% 2.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_full_bw                           [BwDemod]
% 2.89/0.99  --sup_immed_triv                        [TrivRules]
% 2.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_immed_bw_main                     []
% 2.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  
% 2.89/0.99  ------ Combination Options
% 2.89/0.99  
% 2.89/0.99  --comb_res_mult                         3
% 2.89/0.99  --comb_sup_mult                         2
% 2.89/0.99  --comb_inst_mult                        10
% 2.89/0.99  
% 2.89/0.99  ------ Debug Options
% 2.89/0.99  
% 2.89/0.99  --dbg_backtrace                         false
% 2.89/0.99  --dbg_dump_prop_clauses                 false
% 2.89/0.99  --dbg_dump_prop_clauses_file            -
% 2.89/0.99  --dbg_out_stat                          false
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  ------ Proving...
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  % SZS status Theorem for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  fof(f7,axiom,(
% 2.89/0.99    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f44,plain,(
% 2.89/0.99    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.89/0.99    introduced(choice_axiom,[])).
% 2.89/0.99  
% 2.89/0.99  fof(f45,plain,(
% 2.89/0.99    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f44])).
% 2.89/0.99  
% 2.89/0.99  fof(f66,plain,(
% 2.89/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f45])).
% 2.89/0.99  
% 2.89/0.99  fof(f10,axiom,(
% 2.89/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f24,plain,(
% 2.89/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.89/0.99    inference(ennf_transformation,[],[f10])).
% 2.89/0.99  
% 2.89/0.99  fof(f25,plain,(
% 2.89/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.89/0.99    inference(flattening,[],[f24])).
% 2.89/0.99  
% 2.89/0.99  fof(f69,plain,(
% 2.89/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f25])).
% 2.89/0.99  
% 2.89/0.99  fof(f19,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f38,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f19])).
% 2.89/0.99  
% 2.89/0.99  fof(f39,plain,(
% 2.89/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(flattening,[],[f38])).
% 2.89/0.99  
% 2.89/0.99  fof(f55,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(nnf_transformation,[],[f39])).
% 2.89/0.99  
% 2.89/0.99  fof(f82,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f55])).
% 2.89/0.99  
% 2.89/0.99  fof(f20,conjecture,(
% 2.89/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f21,negated_conjecture,(
% 2.89/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.89/0.99    inference(negated_conjecture,[],[f20])).
% 2.89/0.99  
% 2.89/0.99  fof(f40,plain,(
% 2.89/0.99    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.89/0.99    inference(ennf_transformation,[],[f21])).
% 2.89/0.99  
% 2.89/0.99  fof(f41,plain,(
% 2.89/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.89/0.99    inference(flattening,[],[f40])).
% 2.89/0.99  
% 2.89/0.99  fof(f56,plain,(
% 2.89/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7))),
% 2.89/0.99    introduced(choice_axiom,[])).
% 2.89/0.99  
% 2.89/0.99  fof(f57,plain,(
% 2.89/0.99    ~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7)),
% 2.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f41,f56])).
% 2.89/0.99  
% 2.89/0.99  fof(f89,plain,(
% 2.89/0.99    v1_funct_2(sK7,k1_tarski(sK5),sK6)),
% 2.89/0.99    inference(cnf_transformation,[],[f57])).
% 2.89/0.99  
% 2.89/0.99  fof(f2,axiom,(
% 2.89/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f59,plain,(
% 2.89/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f2])).
% 2.89/0.99  
% 2.89/0.99  fof(f3,axiom,(
% 2.89/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f60,plain,(
% 2.89/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f3])).
% 2.89/0.99  
% 2.89/0.99  fof(f4,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f61,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f4])).
% 2.89/0.99  
% 2.89/0.99  fof(f93,plain,(
% 2.89/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.89/0.99    inference(definition_unfolding,[],[f60,f61])).
% 2.89/0.99  
% 2.89/0.99  fof(f94,plain,(
% 2.89/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.89/0.99    inference(definition_unfolding,[],[f59,f93])).
% 2.89/0.99  
% 2.89/0.99  fof(f100,plain,(
% 2.89/0.99    v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6)),
% 2.89/0.99    inference(definition_unfolding,[],[f89,f94])).
% 2.89/0.99  
% 2.89/0.99  fof(f90,plain,(
% 2.89/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))),
% 2.89/0.99    inference(cnf_transformation,[],[f57])).
% 2.89/0.99  
% 2.89/0.99  fof(f99,plain,(
% 2.89/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))),
% 2.89/0.99    inference(definition_unfolding,[],[f90,f94])).
% 2.89/0.99  
% 2.89/0.99  fof(f91,plain,(
% 2.89/0.99    k1_xboole_0 != sK6),
% 2.89/0.99    inference(cnf_transformation,[],[f57])).
% 2.89/0.99  
% 2.89/0.99  fof(f18,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f37,plain,(
% 2.89/0.99    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.89/0.99    inference(ennf_transformation,[],[f18])).
% 2.89/0.99  
% 2.89/0.99  fof(f50,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.89/0.99    inference(nnf_transformation,[],[f37])).
% 2.89/0.99  
% 2.89/0.99  fof(f51,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.89/0.99    inference(rectify,[],[f50])).
% 2.89/0.99  
% 2.89/0.99  fof(f53,plain,(
% 2.89/0.99    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK4(X1,X2),X6),X2) & r2_hidden(sK4(X1,X2),X1)))),
% 2.89/0.99    introduced(choice_axiom,[])).
% 2.89/0.99  
% 2.89/0.99  fof(f52,plain,(
% 2.89/0.99    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2))),
% 2.89/0.99    introduced(choice_axiom,[])).
% 2.89/0.99  
% 2.89/0.99  fof(f54,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK4(X1,X2),X6),X2) & r2_hidden(sK4(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f51,f53,f52])).
% 2.89/0.99  
% 2.89/0.99  fof(f81,plain,(
% 2.89/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f54])).
% 2.89/0.99  
% 2.89/0.99  fof(f5,axiom,(
% 2.89/0.99    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f62,plain,(
% 2.89/0.99    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f5])).
% 2.89/0.99  
% 2.89/0.99  fof(f95,plain,(
% 2.89/0.99    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 2.89/0.99    inference(definition_unfolding,[],[f62,f93])).
% 2.89/0.99  
% 2.89/0.99  fof(f8,axiom,(
% 2.89/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f23,plain,(
% 2.89/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.89/0.99    inference(ennf_transformation,[],[f8])).
% 2.89/0.99  
% 2.89/0.99  fof(f67,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f23])).
% 2.89/0.99  
% 2.89/0.99  fof(f6,axiom,(
% 2.89/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f42,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 2.89/0.99    inference(nnf_transformation,[],[f6])).
% 2.89/0.99  
% 2.89/0.99  fof(f43,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 2.89/0.99    inference(flattening,[],[f42])).
% 2.89/0.99  
% 2.89/0.99  fof(f63,plain,(
% 2.89/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f98,plain,(
% 2.89/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))) )),
% 2.89/0.99    inference(definition_unfolding,[],[f63,f94])).
% 2.89/0.99  
% 2.89/0.99  fof(f14,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f32,plain,(
% 2.89/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.89/0.99    inference(ennf_transformation,[],[f14])).
% 2.89/0.99  
% 2.89/0.99  fof(f33,plain,(
% 2.89/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.89/0.99    inference(flattening,[],[f32])).
% 2.89/0.99  
% 2.89/0.99  fof(f48,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.89/0.99    inference(nnf_transformation,[],[f33])).
% 2.89/0.99  
% 2.89/0.99  fof(f49,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.89/0.99    inference(flattening,[],[f48])).
% 2.89/0.99  
% 2.89/0.99  fof(f73,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f49])).
% 2.89/0.99  
% 2.89/0.99  fof(f88,plain,(
% 2.89/0.99    v1_funct_1(sK7)),
% 2.89/0.99    inference(cnf_transformation,[],[f57])).
% 2.89/0.99  
% 2.89/0.99  fof(f16,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f35,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f16])).
% 2.89/0.99  
% 2.89/0.99  fof(f77,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f35])).
% 2.89/0.99  
% 2.89/0.99  fof(f17,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f22,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.89/0.99    inference(pure_predicate_removal,[],[f17])).
% 2.89/0.99  
% 2.89/0.99  fof(f36,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f22])).
% 2.89/0.99  
% 2.89/0.99  fof(f78,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f36])).
% 2.89/0.99  
% 2.89/0.99  fof(f13,axiom,(
% 2.89/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f30,plain,(
% 2.89/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.89/0.99    inference(ennf_transformation,[],[f13])).
% 2.89/0.99  
% 2.89/0.99  fof(f31,plain,(
% 2.89/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.89/0.99    inference(flattening,[],[f30])).
% 2.89/0.99  
% 2.89/0.99  fof(f72,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f31])).
% 2.89/0.99  
% 2.89/0.99  fof(f92,plain,(
% 2.89/0.99    ~r2_hidden(k1_funct_1(sK7,sK5),sK6)),
% 2.89/0.99    inference(cnf_transformation,[],[f57])).
% 2.89/0.99  
% 2.89/0.99  cnf(c_5,plain,
% 2.89/0.99      ( m1_subset_1(sK0(X0),X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1274,plain,
% 2.89/0.99      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_8,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1271,plain,
% 2.89/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.89/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.89/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2164,plain,
% 2.89/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.89/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1274,c_1271]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_26,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.89/0.99      | k1_xboole_0 = X2 ),
% 2.89/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_30,negated_conjecture,
% 2.89/0.99      ( v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
% 2.89/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_598,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | k2_enumset1(sK5,sK5,sK5,sK5) != X1
% 2.89/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.89/0.99      | sK6 != X2
% 2.89/0.99      | sK7 != X0
% 2.89/0.99      | k1_xboole_0 = X2 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_599,plain,
% 2.89/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
% 2.89/0.99      | k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5)
% 2.89/0.99      | k1_xboole_0 = sK6 ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_598]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_29,negated_conjecture,
% 2.89/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_28,negated_conjecture,
% 2.89/0.99      ( k1_xboole_0 != sK6 ),
% 2.89/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_601,plain,
% 2.89/0.99      ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_599,c_29,c_28]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_18,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ r2_hidden(X3,X1)
% 2.89/0.99      | r2_hidden(k4_tarski(X3,sK3(X0,X3)),X0)
% 2.89/0.99      | k1_relset_1(X1,X2,X0) != X1 ),
% 2.89/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1267,plain,
% 2.89/0.99      ( k1_relset_1(X0,X1,X2) != X0
% 2.89/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.89/0.99      | r2_hidden(X3,X0) != iProver_top
% 2.89/0.99      | r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3056,plain,
% 2.89/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
% 2.89/0.99      | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 2.89/0.99      | r2_hidden(k4_tarski(X0,sK3(sK7,X0)),sK7) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_601,c_1267]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_34,plain,
% 2.89/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3161,plain,
% 2.89/0.99      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 2.89/0.99      | r2_hidden(k4_tarski(X0,sK3(sK7,X0)),sK7) = iProver_top ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_3056,c_34]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3170,plain,
% 2.89/0.99      ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK5,sK5,sK5,sK5)),sK3(sK7,sK0(k2_enumset1(sK5,sK5,sK5,sK5)))),sK7) = iProver_top
% 2.89/0.99      | v1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_2164,c_3161]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1,plain,
% 2.89/0.99      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1278,plain,
% 2.89/0.99      ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3661,plain,
% 2.89/0.99      ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK5,sK5,sK5,sK5)),sK3(sK7,sK0(k2_enumset1(sK5,sK5,sK5,sK5)))),sK7) = iProver_top ),
% 2.89/0.99      inference(forward_subsumption_resolution,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_3170,c_1278]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1263,plain,
% 2.89/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_6,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.89/0.99      | ~ r2_hidden(X2,X0)
% 2.89/0.99      | r2_hidden(X2,X1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1273,plain,
% 2.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.89/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.89/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2324,plain,
% 2.89/0.99      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) = iProver_top
% 2.89/0.99      | r2_hidden(X0,sK7) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1263,c_1273]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4,plain,
% 2.89/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
% 2.89/0.99      | X2 = X0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1275,plain,
% 2.89/0.99      ( X0 = X1
% 2.89/0.99      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2393,plain,
% 2.89/0.99      ( sK5 = X0 | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_2324,c_1275]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3663,plain,
% 2.89/0.99      ( sK0(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_3661,c_2393]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_14,plain,
% 2.89/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.89/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.89/0.99      | ~ v1_funct_1(X1)
% 2.89/0.99      | ~ v1_relat_1(X1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_31,negated_conjecture,
% 2.89/0.99      ( v1_funct_1(sK7) ),
% 2.89/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_406,plain,
% 2.89/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.89/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.89/0.99      | ~ v1_relat_1(X1)
% 2.89/0.99      | sK7 != X1 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_407,plain,
% 2.89/0.99      ( r2_hidden(X0,k1_relat_1(sK7))
% 2.89/0.99      | ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 2.89/0.99      | ~ v1_relat_1(sK7) ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1261,plain,
% 2.89/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 2.89/0.99      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.89/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_408,plain,
% 2.89/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 2.89/0.99      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.89/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_16,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | v1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1464,plain,
% 2.89/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
% 2.89/0.99      | v1_relat_1(sK7) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1465,plain,
% 2.89/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
% 2.89/0.99      | v1_relat_1(sK7) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1499,plain,
% 2.89/0.99      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.89/0.99      | r2_hidden(X0,k1_relat_1(sK7)) = iProver_top ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_1261,c_34,c_408,c_1465]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1500,plain,
% 2.89/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 2.89/0.99      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 2.89/0.99      inference(renaming,[status(thm)],[c_1499]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3664,plain,
% 2.89/0.99      ( r2_hidden(sK0(k2_enumset1(sK5,sK5,sK5,sK5)),k1_relat_1(sK7)) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_3661,c_1500]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_6176,plain,
% 2.89/0.99      ( r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_3663,c_3664]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_17,plain,
% 2.89/0.99      ( v5_relat_1(X0,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_11,plain,
% 2.89/0.99      ( ~ v5_relat_1(X0,X1)
% 2.89/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.89/0.99      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_378,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.89/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_relat_1(X0) ),
% 2.89/0.99      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_382,plain,
% 2.89/0.99      ( ~ v1_funct_1(X0)
% 2.89/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.89/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_378,c_16]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_383,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.89/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.89/0.99      | ~ v1_funct_1(X0) ),
% 2.89/0.99      inference(renaming,[status(thm)],[c_382]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_436,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.89/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.89/0.99      | sK7 != X0 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_383,c_31]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_437,plain,
% 2.89/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.89/0.99      | ~ r2_hidden(X2,k1_relat_1(sK7))
% 2.89/0.99      | r2_hidden(k1_funct_1(sK7,X2),X1) ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_436]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1259,plain,
% 2.89/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.89/0.99      | r2_hidden(X2,k1_relat_1(sK7)) != iProver_top
% 2.89/0.99      | r2_hidden(k1_funct_1(sK7,X2),X1) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1790,plain,
% 2.89/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.89/0.99      | r2_hidden(k1_funct_1(sK7,X0),sK6) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1263,c_1259]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_27,negated_conjecture,
% 2.89/0.99      ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
% 2.89/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1264,plain,
% 2.89/0.99      ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1797,plain,
% 2.89/0.99      ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1790,c_1264]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(contradiction,plain,
% 2.89/0.99      ( $false ),
% 2.89/0.99      inference(minisat,[status(thm)],[c_6176,c_1797]) ).
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  ------                               Statistics
% 2.89/0.99  
% 2.89/0.99  ------ General
% 2.89/0.99  
% 2.89/0.99  abstr_ref_over_cycles:                  0
% 2.89/0.99  abstr_ref_under_cycles:                 0
% 2.89/0.99  gc_basic_clause_elim:                   0
% 2.89/0.99  forced_gc_time:                         0
% 2.89/0.99  parsing_time:                           0.009
% 2.89/0.99  unif_index_cands_time:                  0.
% 2.89/0.99  unif_index_add_time:                    0.
% 2.89/0.99  orderings_time:                         0.
% 2.89/0.99  out_proof_time:                         0.009
% 2.89/0.99  total_time:                             0.225
% 2.89/0.99  num_of_symbols:                         55
% 2.89/0.99  num_of_terms:                           6744
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing
% 2.89/0.99  
% 2.89/0.99  num_of_splits:                          0
% 2.89/0.99  num_of_split_atoms:                     0
% 2.89/0.99  num_of_reused_defs:                     0
% 2.89/0.99  num_eq_ax_congr_red:                    28
% 2.89/0.99  num_of_sem_filtered_clauses:            1
% 2.89/0.99  num_of_subtypes:                        0
% 2.89/0.99  monotx_restored_types:                  0
% 2.89/0.99  sat_num_of_epr_types:                   0
% 2.89/0.99  sat_num_of_non_cyclic_types:            0
% 2.89/0.99  sat_guarded_non_collapsed_types:        0
% 2.89/0.99  num_pure_diseq_elim:                    0
% 2.89/0.99  simp_replaced_by:                       0
% 2.89/0.99  res_preprocessed:                       134
% 2.89/0.99  prep_upred:                             0
% 2.89/0.99  prep_unflattend:                        41
% 2.89/0.99  smt_new_axioms:                         0
% 2.89/0.99  pred_elim_cands:                        4
% 2.89/0.99  pred_elim:                              4
% 2.89/0.99  pred_elim_cl:                           7
% 2.89/0.99  pred_elim_cycles:                       9
% 2.89/0.99  merged_defs:                            0
% 2.89/0.99  merged_defs_ncl:                        0
% 2.89/0.99  bin_hyper_res:                          0
% 2.89/0.99  prep_cycles:                            4
% 2.89/0.99  pred_elim_time:                         0.007
% 2.89/0.99  splitting_time:                         0.
% 2.89/0.99  sem_filter_time:                        0.
% 2.89/0.99  monotx_time:                            0.
% 2.89/0.99  subtype_inf_time:                       0.
% 2.89/0.99  
% 2.89/0.99  ------ Problem properties
% 2.89/0.99  
% 2.89/0.99  clauses:                                25
% 2.89/0.99  conjectures:                            3
% 2.89/0.99  epr:                                    3
% 2.89/0.99  horn:                                   21
% 2.89/0.99  ground:                                 6
% 2.89/0.99  unary:                                  8
% 2.89/0.99  binary:                                 4
% 2.89/0.99  lits:                                   57
% 2.89/0.99  lits_eq:                                13
% 2.89/0.99  fd_pure:                                0
% 2.89/0.99  fd_pseudo:                              0
% 2.89/0.99  fd_cond:                                1
% 2.89/0.99  fd_pseudo_cond:                         2
% 2.89/0.99  ac_symbols:                             0
% 2.89/0.99  
% 2.89/0.99  ------ Propositional Solver
% 2.89/0.99  
% 2.89/0.99  prop_solver_calls:                      29
% 2.89/0.99  prop_fast_solver_calls:                 935
% 2.89/0.99  smt_solver_calls:                       0
% 2.89/0.99  smt_fast_solver_calls:                  0
% 2.89/0.99  prop_num_of_clauses:                    2145
% 2.89/0.99  prop_preprocess_simplified:             6286
% 2.89/0.99  prop_fo_subsumed:                       14
% 2.89/0.99  prop_solver_time:                       0.
% 2.89/0.99  smt_solver_time:                        0.
% 2.89/0.99  smt_fast_solver_time:                   0.
% 2.89/0.99  prop_fast_solver_time:                  0.
% 2.89/0.99  prop_unsat_core_time:                   0.
% 2.89/0.99  
% 2.89/0.99  ------ QBF
% 2.89/0.99  
% 2.89/0.99  qbf_q_res:                              0
% 2.89/0.99  qbf_num_tautologies:                    0
% 2.89/0.99  qbf_prep_cycles:                        0
% 2.89/0.99  
% 2.89/0.99  ------ BMC1
% 2.89/0.99  
% 2.89/0.99  bmc1_current_bound:                     -1
% 2.89/0.99  bmc1_last_solved_bound:                 -1
% 2.89/0.99  bmc1_unsat_core_size:                   -1
% 2.89/0.99  bmc1_unsat_core_parents_size:           -1
% 2.89/0.99  bmc1_merge_next_fun:                    0
% 2.89/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation
% 2.89/0.99  
% 2.89/0.99  inst_num_of_clauses:                    564
% 2.89/0.99  inst_num_in_passive:                    163
% 2.89/0.99  inst_num_in_active:                     358
% 2.89/0.99  inst_num_in_unprocessed:                43
% 2.89/0.99  inst_num_of_loops:                      410
% 2.89/0.99  inst_num_of_learning_restarts:          0
% 2.89/0.99  inst_num_moves_active_passive:          48
% 2.89/0.99  inst_lit_activity:                      0
% 2.89/0.99  inst_lit_activity_moves:                0
% 2.89/0.99  inst_num_tautologies:                   0
% 2.89/0.99  inst_num_prop_implied:                  0
% 2.89/0.99  inst_num_existing_simplified:           0
% 2.89/0.99  inst_num_eq_res_simplified:             0
% 2.89/0.99  inst_num_child_elim:                    0
% 2.89/0.99  inst_num_of_dismatching_blockings:      405
% 2.89/0.99  inst_num_of_non_proper_insts:           656
% 2.89/0.99  inst_num_of_duplicates:                 0
% 2.89/0.99  inst_inst_num_from_inst_to_res:         0
% 2.89/0.99  inst_dismatching_checking_time:         0.
% 2.89/0.99  
% 2.89/0.99  ------ Resolution
% 2.89/0.99  
% 2.89/0.99  res_num_of_clauses:                     0
% 2.89/0.99  res_num_in_passive:                     0
% 2.89/0.99  res_num_in_active:                      0
% 2.89/0.99  res_num_of_loops:                       138
% 2.89/0.99  res_forward_subset_subsumed:            47
% 2.89/0.99  res_backward_subset_subsumed:           0
% 2.89/0.99  res_forward_subsumed:                   0
% 2.89/0.99  res_backward_subsumed:                  0
% 2.89/0.99  res_forward_subsumption_resolution:     0
% 2.89/0.99  res_backward_subsumption_resolution:    0
% 2.89/0.99  res_clause_to_clause_subsumption:       258
% 2.89/0.99  res_orphan_elimination:                 0
% 2.89/0.99  res_tautology_del:                      63
% 2.89/0.99  res_num_eq_res_simplified:              0
% 2.89/0.99  res_num_sel_changes:                    0
% 2.89/0.99  res_moves_from_active_to_pass:          0
% 2.89/0.99  
% 2.89/0.99  ------ Superposition
% 2.89/0.99  
% 2.89/0.99  sup_time_total:                         0.
% 2.89/0.99  sup_time_generating:                    0.
% 2.89/0.99  sup_time_sim_full:                      0.
% 2.89/0.99  sup_time_sim_immed:                     0.
% 2.89/0.99  
% 2.89/0.99  sup_num_of_clauses:                     135
% 2.89/0.99  sup_num_in_active:                      77
% 2.89/0.99  sup_num_in_passive:                     58
% 2.89/0.99  sup_num_of_loops:                       80
% 2.89/0.99  sup_fw_superposition:                   50
% 2.89/0.99  sup_bw_superposition:                   86
% 2.89/0.99  sup_immediate_simplified:               8
% 2.89/0.99  sup_given_eliminated:                   2
% 2.89/0.99  comparisons_done:                       0
% 2.89/0.99  comparisons_avoided:                    30
% 2.89/0.99  
% 2.89/0.99  ------ Simplifications
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  sim_fw_subset_subsumed:                 8
% 2.89/0.99  sim_bw_subset_subsumed:                 1
% 2.89/0.99  sim_fw_subsumed:                        0
% 2.89/0.99  sim_bw_subsumed:                        0
% 2.89/0.99  sim_fw_subsumption_res:                 1
% 2.89/0.99  sim_bw_subsumption_res:                 0
% 2.89/0.99  sim_tautology_del:                      2
% 2.89/0.99  sim_eq_tautology_del:                   3
% 2.89/0.99  sim_eq_res_simp:                        0
% 2.89/0.99  sim_fw_demodulated:                     0
% 2.89/0.99  sim_bw_demodulated:                     6
% 2.89/0.99  sim_light_normalised:                   1
% 2.89/0.99  sim_joinable_taut:                      0
% 2.89/0.99  sim_joinable_simp:                      0
% 2.89/0.99  sim_ac_normalised:                      0
% 2.89/0.99  sim_smt_subsumption:                    0
% 2.89/0.99  
%------------------------------------------------------------------------------
