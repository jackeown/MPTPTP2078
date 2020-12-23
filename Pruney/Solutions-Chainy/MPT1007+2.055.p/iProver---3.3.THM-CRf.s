%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:53 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 363 expanded)
%              Number of clauses        :   68 (  94 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  429 (1166 expanded)
%              Number of equality atoms :  164 ( 364 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f53])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f54])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f93])).

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

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
        & r2_hidden(sK3(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
            & r2_hidden(sK3(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f49,f51,f50])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f66,f94])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f63,f94])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_20,plain,
    ( r2_hidden(sK4(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1172,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK4(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X2
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_568,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
    | k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5)
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_570,plain,
    ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_29,c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK2(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1175,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3418,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_570,c_1175])).

cnf(c_34,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3558,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_34])).

cnf(c_3567,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(k2_enumset1(sK5,sK5,sK5,sK5)),sK2(sK7,sK4(k2_enumset1(sK5,sK5,sK5,sK5)))),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_3558])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1587,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_3802,plain,
    ( r2_hidden(k4_tarski(sK4(k2_enumset1(sK5,sK5,sK5,sK5)),sK2(sK7,sK4(k2_enumset1(sK5,sK5,sK5,sK5)))),sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3567,c_1587])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_405,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_406,plain,
    ( r2_hidden(X0,k1_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_1166,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_407,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1355,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1356,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1355])).

cnf(c_1388,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1166,c_34,c_407,c_1356])).

cnf(c_1389,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_1388])).

cnf(c_3805,plain,
    ( r2_hidden(sK4(k2_enumset1(sK5,sK5,sK5,sK5)),k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3802,c_1389])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_421,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1165,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_422,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1441,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_34,c_422,c_1356])).

cnf(c_1442,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_1441])).

cnf(c_1170,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2340,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1180])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1181,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2437,plain,
    ( sK5 = X0
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2340,c_1181])).

cnf(c_2553,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_2437])).

cnf(c_2572,plain,
    ( sK4(k1_relat_1(sK7)) = sK5
    | k1_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1172,c_2553])).

cnf(c_4092,plain,
    ( k1_relat_1(sK7) = k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_1172])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

cnf(c_351,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_15])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_31])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X2),X1) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_1167,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X2,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_1663,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1167])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1171,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1794,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1171])).

cnf(c_4107,plain,
    ( k1_relat_1(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4092,c_1794])).

cnf(c_4254,plain,
    ( r2_hidden(sK4(k2_enumset1(sK5,sK5,sK5,sK5)),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3805,c_4107])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1169,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_4256,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4254,c_1169])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:57:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.45/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.01  
% 2.45/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.01  
% 2.45/1.01  ------  iProver source info
% 2.45/1.01  
% 2.45/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.01  git: non_committed_changes: false
% 2.45/1.01  git: last_make_outside_of_git: false
% 2.45/1.01  
% 2.45/1.01  ------ 
% 2.45/1.01  
% 2.45/1.01  ------ Input Options
% 2.45/1.01  
% 2.45/1.01  --out_options                           all
% 2.45/1.01  --tptp_safe_out                         true
% 2.45/1.01  --problem_path                          ""
% 2.45/1.01  --include_path                          ""
% 2.45/1.01  --clausifier                            res/vclausify_rel
% 2.45/1.01  --clausifier_options                    --mode clausify
% 2.45/1.01  --stdin                                 false
% 2.45/1.01  --stats_out                             all
% 2.45/1.01  
% 2.45/1.01  ------ General Options
% 2.45/1.01  
% 2.45/1.01  --fof                                   false
% 2.45/1.01  --time_out_real                         305.
% 2.45/1.01  --time_out_virtual                      -1.
% 2.45/1.01  --symbol_type_check                     false
% 2.45/1.01  --clausify_out                          false
% 2.45/1.01  --sig_cnt_out                           false
% 2.45/1.01  --trig_cnt_out                          false
% 2.45/1.01  --trig_cnt_out_tolerance                1.
% 2.45/1.01  --trig_cnt_out_sk_spl                   false
% 2.45/1.01  --abstr_cl_out                          false
% 2.45/1.01  
% 2.45/1.01  ------ Global Options
% 2.45/1.01  
% 2.45/1.01  --schedule                              default
% 2.45/1.01  --add_important_lit                     false
% 2.45/1.01  --prop_solver_per_cl                    1000
% 2.45/1.01  --min_unsat_core                        false
% 2.45/1.01  --soft_assumptions                      false
% 2.45/1.01  --soft_lemma_size                       3
% 2.45/1.01  --prop_impl_unit_size                   0
% 2.45/1.01  --prop_impl_unit                        []
% 2.45/1.01  --share_sel_clauses                     true
% 2.45/1.01  --reset_solvers                         false
% 2.45/1.01  --bc_imp_inh                            [conj_cone]
% 2.45/1.01  --conj_cone_tolerance                   3.
% 2.45/1.01  --extra_neg_conj                        none
% 2.45/1.01  --large_theory_mode                     true
% 2.45/1.01  --prolific_symb_bound                   200
% 2.45/1.01  --lt_threshold                          2000
% 2.45/1.01  --clause_weak_htbl                      true
% 2.45/1.01  --gc_record_bc_elim                     false
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing Options
% 2.45/1.01  
% 2.45/1.01  --preprocessing_flag                    true
% 2.45/1.01  --time_out_prep_mult                    0.1
% 2.45/1.01  --splitting_mode                        input
% 2.45/1.01  --splitting_grd                         true
% 2.45/1.01  --splitting_cvd                         false
% 2.45/1.01  --splitting_cvd_svl                     false
% 2.45/1.01  --splitting_nvd                         32
% 2.45/1.01  --sub_typing                            true
% 2.45/1.01  --prep_gs_sim                           true
% 2.45/1.01  --prep_unflatten                        true
% 2.45/1.01  --prep_res_sim                          true
% 2.45/1.01  --prep_upred                            true
% 2.45/1.01  --prep_sem_filter                       exhaustive
% 2.45/1.01  --prep_sem_filter_out                   false
% 2.45/1.01  --pred_elim                             true
% 2.45/1.01  --res_sim_input                         true
% 2.45/1.01  --eq_ax_congr_red                       true
% 2.45/1.01  --pure_diseq_elim                       true
% 2.45/1.01  --brand_transform                       false
% 2.45/1.01  --non_eq_to_eq                          false
% 2.45/1.01  --prep_def_merge                        true
% 2.45/1.01  --prep_def_merge_prop_impl              false
% 2.45/1.01  --prep_def_merge_mbd                    true
% 2.45/1.01  --prep_def_merge_tr_red                 false
% 2.45/1.01  --prep_def_merge_tr_cl                  false
% 2.45/1.01  --smt_preprocessing                     true
% 2.45/1.01  --smt_ac_axioms                         fast
% 2.45/1.01  --preprocessed_out                      false
% 2.45/1.01  --preprocessed_stats                    false
% 2.45/1.01  
% 2.45/1.01  ------ Abstraction refinement Options
% 2.45/1.01  
% 2.45/1.01  --abstr_ref                             []
% 2.45/1.01  --abstr_ref_prep                        false
% 2.45/1.01  --abstr_ref_until_sat                   false
% 2.45/1.01  --abstr_ref_sig_restrict                funpre
% 2.45/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.01  --abstr_ref_under                       []
% 2.45/1.01  
% 2.45/1.01  ------ SAT Options
% 2.45/1.01  
% 2.45/1.01  --sat_mode                              false
% 2.45/1.01  --sat_fm_restart_options                ""
% 2.45/1.01  --sat_gr_def                            false
% 2.45/1.01  --sat_epr_types                         true
% 2.45/1.01  --sat_non_cyclic_types                  false
% 2.45/1.01  --sat_finite_models                     false
% 2.45/1.01  --sat_fm_lemmas                         false
% 2.45/1.01  --sat_fm_prep                           false
% 2.45/1.01  --sat_fm_uc_incr                        true
% 2.45/1.01  --sat_out_model                         small
% 2.45/1.01  --sat_out_clauses                       false
% 2.45/1.01  
% 2.45/1.01  ------ QBF Options
% 2.45/1.01  
% 2.45/1.01  --qbf_mode                              false
% 2.45/1.01  --qbf_elim_univ                         false
% 2.45/1.01  --qbf_dom_inst                          none
% 2.45/1.01  --qbf_dom_pre_inst                      false
% 2.45/1.01  --qbf_sk_in                             false
% 2.45/1.01  --qbf_pred_elim                         true
% 2.45/1.01  --qbf_split                             512
% 2.45/1.01  
% 2.45/1.01  ------ BMC1 Options
% 2.45/1.01  
% 2.45/1.01  --bmc1_incremental                      false
% 2.45/1.01  --bmc1_axioms                           reachable_all
% 2.45/1.01  --bmc1_min_bound                        0
% 2.45/1.01  --bmc1_max_bound                        -1
% 2.45/1.01  --bmc1_max_bound_default                -1
% 2.45/1.01  --bmc1_symbol_reachability              true
% 2.45/1.01  --bmc1_property_lemmas                  false
% 2.45/1.01  --bmc1_k_induction                      false
% 2.45/1.01  --bmc1_non_equiv_states                 false
% 2.45/1.01  --bmc1_deadlock                         false
% 2.45/1.01  --bmc1_ucm                              false
% 2.45/1.01  --bmc1_add_unsat_core                   none
% 2.45/1.01  --bmc1_unsat_core_children              false
% 2.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.01  --bmc1_out_stat                         full
% 2.45/1.01  --bmc1_ground_init                      false
% 2.45/1.01  --bmc1_pre_inst_next_state              false
% 2.45/1.01  --bmc1_pre_inst_state                   false
% 2.45/1.01  --bmc1_pre_inst_reach_state             false
% 2.45/1.01  --bmc1_out_unsat_core                   false
% 2.45/1.01  --bmc1_aig_witness_out                  false
% 2.45/1.01  --bmc1_verbose                          false
% 2.45/1.01  --bmc1_dump_clauses_tptp                false
% 2.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.01  --bmc1_dump_file                        -
% 2.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.01  --bmc1_ucm_extend_mode                  1
% 2.45/1.01  --bmc1_ucm_init_mode                    2
% 2.45/1.01  --bmc1_ucm_cone_mode                    none
% 2.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.01  --bmc1_ucm_relax_model                  4
% 2.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.01  --bmc1_ucm_layered_model                none
% 2.45/1.01  --bmc1_ucm_max_lemma_size               10
% 2.45/1.01  
% 2.45/1.01  ------ AIG Options
% 2.45/1.01  
% 2.45/1.01  --aig_mode                              false
% 2.45/1.01  
% 2.45/1.01  ------ Instantiation Options
% 2.45/1.01  
% 2.45/1.01  --instantiation_flag                    true
% 2.45/1.01  --inst_sos_flag                         false
% 2.45/1.01  --inst_sos_phase                        true
% 2.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel_side                     num_symb
% 2.45/1.01  --inst_solver_per_active                1400
% 2.45/1.01  --inst_solver_calls_frac                1.
% 2.45/1.01  --inst_passive_queue_type               priority_queues
% 2.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.01  --inst_passive_queues_freq              [25;2]
% 2.45/1.01  --inst_dismatching                      true
% 2.45/1.01  --inst_eager_unprocessed_to_passive     true
% 2.45/1.01  --inst_prop_sim_given                   true
% 2.45/1.01  --inst_prop_sim_new                     false
% 2.45/1.01  --inst_subs_new                         false
% 2.45/1.01  --inst_eq_res_simp                      false
% 2.45/1.01  --inst_subs_given                       false
% 2.45/1.01  --inst_orphan_elimination               true
% 2.45/1.01  --inst_learning_loop_flag               true
% 2.45/1.01  --inst_learning_start                   3000
% 2.45/1.01  --inst_learning_factor                  2
% 2.45/1.01  --inst_start_prop_sim_after_learn       3
% 2.45/1.01  --inst_sel_renew                        solver
% 2.45/1.01  --inst_lit_activity_flag                true
% 2.45/1.01  --inst_restr_to_given                   false
% 2.45/1.01  --inst_activity_threshold               500
% 2.45/1.01  --inst_out_proof                        true
% 2.45/1.01  
% 2.45/1.01  ------ Resolution Options
% 2.45/1.01  
% 2.45/1.01  --resolution_flag                       true
% 2.45/1.01  --res_lit_sel                           adaptive
% 2.45/1.01  --res_lit_sel_side                      none
% 2.45/1.01  --res_ordering                          kbo
% 2.45/1.01  --res_to_prop_solver                    active
% 2.45/1.01  --res_prop_simpl_new                    false
% 2.45/1.01  --res_prop_simpl_given                  true
% 2.45/1.01  --res_passive_queue_type                priority_queues
% 2.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.01  --res_passive_queues_freq               [15;5]
% 2.45/1.01  --res_forward_subs                      full
% 2.45/1.01  --res_backward_subs                     full
% 2.45/1.01  --res_forward_subs_resolution           true
% 2.45/1.01  --res_backward_subs_resolution          true
% 2.45/1.01  --res_orphan_elimination                true
% 2.45/1.01  --res_time_limit                        2.
% 2.45/1.01  --res_out_proof                         true
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Options
% 2.45/1.01  
% 2.45/1.01  --superposition_flag                    true
% 2.45/1.01  --sup_passive_queue_type                priority_queues
% 2.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.01  --demod_completeness_check              fast
% 2.45/1.01  --demod_use_ground                      true
% 2.45/1.01  --sup_to_prop_solver                    passive
% 2.45/1.01  --sup_prop_simpl_new                    true
% 2.45/1.01  --sup_prop_simpl_given                  true
% 2.45/1.01  --sup_fun_splitting                     false
% 2.45/1.01  --sup_smt_interval                      50000
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Simplification Setup
% 2.45/1.01  
% 2.45/1.01  --sup_indices_passive                   []
% 2.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_full_bw                           [BwDemod]
% 2.45/1.01  --sup_immed_triv                        [TrivRules]
% 2.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_immed_bw_main                     []
% 2.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  
% 2.45/1.01  ------ Combination Options
% 2.45/1.01  
% 2.45/1.01  --comb_res_mult                         3
% 2.45/1.01  --comb_sup_mult                         2
% 2.45/1.01  --comb_inst_mult                        10
% 2.45/1.01  
% 2.45/1.01  ------ Debug Options
% 2.45/1.01  
% 2.45/1.01  --dbg_backtrace                         false
% 2.45/1.01  --dbg_dump_prop_clauses                 false
% 2.45/1.01  --dbg_dump_prop_clauses_file            -
% 2.45/1.01  --dbg_out_stat                          false
% 2.45/1.01  ------ Parsing...
% 2.45/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.01  ------ Proving...
% 2.45/1.01  ------ Problem Properties 
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  clauses                                 25
% 2.45/1.01  conjectures                             3
% 2.45/1.01  EPR                                     2
% 2.45/1.01  Horn                                    21
% 2.45/1.01  unary                                   8
% 2.45/1.01  binary                                  5
% 2.45/1.01  lits                                    56
% 2.45/1.01  lits eq                                 16
% 2.45/1.01  fd_pure                                 0
% 2.45/1.01  fd_pseudo                               0
% 2.45/1.01  fd_cond                                 2
% 2.45/1.01  fd_pseudo_cond                          2
% 2.45/1.01  AC symbols                              0
% 2.45/1.01  
% 2.45/1.01  ------ Schedule dynamic 5 is on 
% 2.45/1.01  
% 2.45/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  ------ 
% 2.45/1.01  Current options:
% 2.45/1.01  ------ 
% 2.45/1.01  
% 2.45/1.01  ------ Input Options
% 2.45/1.01  
% 2.45/1.01  --out_options                           all
% 2.45/1.01  --tptp_safe_out                         true
% 2.45/1.01  --problem_path                          ""
% 2.45/1.01  --include_path                          ""
% 2.45/1.01  --clausifier                            res/vclausify_rel
% 2.45/1.01  --clausifier_options                    --mode clausify
% 2.45/1.01  --stdin                                 false
% 2.45/1.01  --stats_out                             all
% 2.45/1.01  
% 2.45/1.01  ------ General Options
% 2.45/1.01  
% 2.45/1.01  --fof                                   false
% 2.45/1.01  --time_out_real                         305.
% 2.45/1.01  --time_out_virtual                      -1.
% 2.45/1.01  --symbol_type_check                     false
% 2.45/1.01  --clausify_out                          false
% 2.45/1.01  --sig_cnt_out                           false
% 2.45/1.01  --trig_cnt_out                          false
% 2.45/1.01  --trig_cnt_out_tolerance                1.
% 2.45/1.01  --trig_cnt_out_sk_spl                   false
% 2.45/1.01  --abstr_cl_out                          false
% 2.45/1.01  
% 2.45/1.01  ------ Global Options
% 2.45/1.01  
% 2.45/1.01  --schedule                              default
% 2.45/1.01  --add_important_lit                     false
% 2.45/1.01  --prop_solver_per_cl                    1000
% 2.45/1.01  --min_unsat_core                        false
% 2.45/1.01  --soft_assumptions                      false
% 2.45/1.01  --soft_lemma_size                       3
% 2.45/1.01  --prop_impl_unit_size                   0
% 2.45/1.01  --prop_impl_unit                        []
% 2.45/1.01  --share_sel_clauses                     true
% 2.45/1.01  --reset_solvers                         false
% 2.45/1.01  --bc_imp_inh                            [conj_cone]
% 2.45/1.01  --conj_cone_tolerance                   3.
% 2.45/1.01  --extra_neg_conj                        none
% 2.45/1.01  --large_theory_mode                     true
% 2.45/1.01  --prolific_symb_bound                   200
% 2.45/1.01  --lt_threshold                          2000
% 2.45/1.01  --clause_weak_htbl                      true
% 2.45/1.01  --gc_record_bc_elim                     false
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing Options
% 2.45/1.01  
% 2.45/1.01  --preprocessing_flag                    true
% 2.45/1.01  --time_out_prep_mult                    0.1
% 2.45/1.01  --splitting_mode                        input
% 2.45/1.01  --splitting_grd                         true
% 2.45/1.01  --splitting_cvd                         false
% 2.45/1.01  --splitting_cvd_svl                     false
% 2.45/1.01  --splitting_nvd                         32
% 2.45/1.01  --sub_typing                            true
% 2.45/1.01  --prep_gs_sim                           true
% 2.45/1.01  --prep_unflatten                        true
% 2.45/1.01  --prep_res_sim                          true
% 2.45/1.01  --prep_upred                            true
% 2.45/1.01  --prep_sem_filter                       exhaustive
% 2.45/1.01  --prep_sem_filter_out                   false
% 2.45/1.01  --pred_elim                             true
% 2.45/1.01  --res_sim_input                         true
% 2.45/1.01  --eq_ax_congr_red                       true
% 2.45/1.01  --pure_diseq_elim                       true
% 2.45/1.01  --brand_transform                       false
% 2.45/1.01  --non_eq_to_eq                          false
% 2.45/1.01  --prep_def_merge                        true
% 2.45/1.01  --prep_def_merge_prop_impl              false
% 2.45/1.01  --prep_def_merge_mbd                    true
% 2.45/1.01  --prep_def_merge_tr_red                 false
% 2.45/1.01  --prep_def_merge_tr_cl                  false
% 2.45/1.01  --smt_preprocessing                     true
% 2.45/1.01  --smt_ac_axioms                         fast
% 2.45/1.01  --preprocessed_out                      false
% 2.45/1.01  --preprocessed_stats                    false
% 2.45/1.01  
% 2.45/1.01  ------ Abstraction refinement Options
% 2.45/1.01  
% 2.45/1.01  --abstr_ref                             []
% 2.45/1.01  --abstr_ref_prep                        false
% 2.45/1.01  --abstr_ref_until_sat                   false
% 2.45/1.01  --abstr_ref_sig_restrict                funpre
% 2.45/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.01  --abstr_ref_under                       []
% 2.45/1.01  
% 2.45/1.01  ------ SAT Options
% 2.45/1.01  
% 2.45/1.01  --sat_mode                              false
% 2.45/1.01  --sat_fm_restart_options                ""
% 2.45/1.01  --sat_gr_def                            false
% 2.45/1.01  --sat_epr_types                         true
% 2.45/1.01  --sat_non_cyclic_types                  false
% 2.45/1.01  --sat_finite_models                     false
% 2.45/1.01  --sat_fm_lemmas                         false
% 2.45/1.01  --sat_fm_prep                           false
% 2.45/1.01  --sat_fm_uc_incr                        true
% 2.45/1.01  --sat_out_model                         small
% 2.45/1.01  --sat_out_clauses                       false
% 2.45/1.01  
% 2.45/1.01  ------ QBF Options
% 2.45/1.01  
% 2.45/1.01  --qbf_mode                              false
% 2.45/1.01  --qbf_elim_univ                         false
% 2.45/1.01  --qbf_dom_inst                          none
% 2.45/1.01  --qbf_dom_pre_inst                      false
% 2.45/1.01  --qbf_sk_in                             false
% 2.45/1.01  --qbf_pred_elim                         true
% 2.45/1.01  --qbf_split                             512
% 2.45/1.01  
% 2.45/1.01  ------ BMC1 Options
% 2.45/1.01  
% 2.45/1.01  --bmc1_incremental                      false
% 2.45/1.01  --bmc1_axioms                           reachable_all
% 2.45/1.01  --bmc1_min_bound                        0
% 2.45/1.01  --bmc1_max_bound                        -1
% 2.45/1.01  --bmc1_max_bound_default                -1
% 2.45/1.01  --bmc1_symbol_reachability              true
% 2.45/1.01  --bmc1_property_lemmas                  false
% 2.45/1.01  --bmc1_k_induction                      false
% 2.45/1.01  --bmc1_non_equiv_states                 false
% 2.45/1.01  --bmc1_deadlock                         false
% 2.45/1.01  --bmc1_ucm                              false
% 2.45/1.01  --bmc1_add_unsat_core                   none
% 2.45/1.01  --bmc1_unsat_core_children              false
% 2.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.01  --bmc1_out_stat                         full
% 2.45/1.01  --bmc1_ground_init                      false
% 2.45/1.01  --bmc1_pre_inst_next_state              false
% 2.45/1.01  --bmc1_pre_inst_state                   false
% 2.45/1.01  --bmc1_pre_inst_reach_state             false
% 2.45/1.01  --bmc1_out_unsat_core                   false
% 2.45/1.01  --bmc1_aig_witness_out                  false
% 2.45/1.01  --bmc1_verbose                          false
% 2.45/1.01  --bmc1_dump_clauses_tptp                false
% 2.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.01  --bmc1_dump_file                        -
% 2.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.01  --bmc1_ucm_extend_mode                  1
% 2.45/1.01  --bmc1_ucm_init_mode                    2
% 2.45/1.01  --bmc1_ucm_cone_mode                    none
% 2.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.01  --bmc1_ucm_relax_model                  4
% 2.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.01  --bmc1_ucm_layered_model                none
% 2.45/1.01  --bmc1_ucm_max_lemma_size               10
% 2.45/1.01  
% 2.45/1.01  ------ AIG Options
% 2.45/1.01  
% 2.45/1.01  --aig_mode                              false
% 2.45/1.01  
% 2.45/1.01  ------ Instantiation Options
% 2.45/1.01  
% 2.45/1.01  --instantiation_flag                    true
% 2.45/1.01  --inst_sos_flag                         false
% 2.45/1.01  --inst_sos_phase                        true
% 2.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel_side                     none
% 2.45/1.01  --inst_solver_per_active                1400
% 2.45/1.01  --inst_solver_calls_frac                1.
% 2.45/1.01  --inst_passive_queue_type               priority_queues
% 2.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.01  --inst_passive_queues_freq              [25;2]
% 2.45/1.01  --inst_dismatching                      true
% 2.45/1.01  --inst_eager_unprocessed_to_passive     true
% 2.45/1.01  --inst_prop_sim_given                   true
% 2.45/1.01  --inst_prop_sim_new                     false
% 2.45/1.01  --inst_subs_new                         false
% 2.45/1.01  --inst_eq_res_simp                      false
% 2.45/1.01  --inst_subs_given                       false
% 2.45/1.01  --inst_orphan_elimination               true
% 2.45/1.01  --inst_learning_loop_flag               true
% 2.45/1.01  --inst_learning_start                   3000
% 2.45/1.01  --inst_learning_factor                  2
% 2.45/1.01  --inst_start_prop_sim_after_learn       3
% 2.45/1.01  --inst_sel_renew                        solver
% 2.45/1.01  --inst_lit_activity_flag                true
% 2.45/1.01  --inst_restr_to_given                   false
% 2.45/1.01  --inst_activity_threshold               500
% 2.45/1.01  --inst_out_proof                        true
% 2.45/1.01  
% 2.45/1.01  ------ Resolution Options
% 2.45/1.01  
% 2.45/1.01  --resolution_flag                       false
% 2.45/1.01  --res_lit_sel                           adaptive
% 2.45/1.01  --res_lit_sel_side                      none
% 2.45/1.01  --res_ordering                          kbo
% 2.45/1.01  --res_to_prop_solver                    active
% 2.45/1.01  --res_prop_simpl_new                    false
% 2.45/1.01  --res_prop_simpl_given                  true
% 2.45/1.01  --res_passive_queue_type                priority_queues
% 2.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.01  --res_passive_queues_freq               [15;5]
% 2.45/1.01  --res_forward_subs                      full
% 2.45/1.01  --res_backward_subs                     full
% 2.45/1.01  --res_forward_subs_resolution           true
% 2.45/1.01  --res_backward_subs_resolution          true
% 2.45/1.01  --res_orphan_elimination                true
% 2.45/1.01  --res_time_limit                        2.
% 2.45/1.01  --res_out_proof                         true
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Options
% 2.45/1.01  
% 2.45/1.01  --superposition_flag                    true
% 2.45/1.01  --sup_passive_queue_type                priority_queues
% 2.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.01  --demod_completeness_check              fast
% 2.45/1.01  --demod_use_ground                      true
% 2.45/1.01  --sup_to_prop_solver                    passive
% 2.45/1.01  --sup_prop_simpl_new                    true
% 2.45/1.01  --sup_prop_simpl_given                  true
% 2.45/1.01  --sup_fun_splitting                     false
% 2.45/1.01  --sup_smt_interval                      50000
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Simplification Setup
% 2.45/1.01  
% 2.45/1.01  --sup_indices_passive                   []
% 2.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_full_bw                           [BwDemod]
% 2.45/1.01  --sup_immed_triv                        [TrivRules]
% 2.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_immed_bw_main                     []
% 2.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  
% 2.45/1.01  ------ Combination Options
% 2.45/1.01  
% 2.45/1.01  --comb_res_mult                         3
% 2.45/1.01  --comb_sup_mult                         2
% 2.45/1.01  --comb_inst_mult                        10
% 2.45/1.01  
% 2.45/1.01  ------ Debug Options
% 2.45/1.01  
% 2.45/1.01  --dbg_backtrace                         false
% 2.45/1.01  --dbg_dump_prop_clauses                 false
% 2.45/1.01  --dbg_dump_prop_clauses_file            -
% 2.45/1.01  --dbg_out_stat                          false
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  ------ Proving...
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  % SZS status Theorem for theBenchmark.p
% 2.45/1.01  
% 2.45/1.01   Resolution empty clause
% 2.45/1.01  
% 2.45/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/1.01  
% 2.45/1.01  fof(f18,axiom,(
% 2.45/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f22,plain,(
% 2.45/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.45/1.01    inference(pure_predicate_removal,[],[f18])).
% 2.45/1.01  
% 2.45/1.01  fof(f37,plain,(
% 2.45/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.45/1.01    inference(ennf_transformation,[],[f22])).
% 2.45/1.01  
% 2.45/1.01  fof(f53,plain,(
% 2.45/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.45/1.01    introduced(choice_axiom,[])).
% 2.45/1.01  
% 2.45/1.01  fof(f54,plain,(
% 2.45/1.01    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 2.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f53])).
% 2.45/1.01  
% 2.45/1.01  fof(f81,plain,(
% 2.45/1.01    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.45/1.01    inference(cnf_transformation,[],[f54])).
% 2.45/1.01  
% 2.45/1.01  fof(f19,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f38,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(ennf_transformation,[],[f19])).
% 2.45/1.01  
% 2.45/1.01  fof(f39,plain,(
% 2.45/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(flattening,[],[f38])).
% 2.45/1.01  
% 2.45/1.01  fof(f55,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(nnf_transformation,[],[f39])).
% 2.45/1.01  
% 2.45/1.01  fof(f82,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f55])).
% 2.45/1.01  
% 2.45/1.01  fof(f20,conjecture,(
% 2.45/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f21,negated_conjecture,(
% 2.45/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.45/1.01    inference(negated_conjecture,[],[f20])).
% 2.45/1.01  
% 2.45/1.01  fof(f40,plain,(
% 2.45/1.01    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.45/1.01    inference(ennf_transformation,[],[f21])).
% 2.45/1.01  
% 2.45/1.01  fof(f41,plain,(
% 2.45/1.01    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.45/1.01    inference(flattening,[],[f40])).
% 2.45/1.01  
% 2.45/1.01  fof(f56,plain,(
% 2.45/1.01    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7))),
% 2.45/1.01    introduced(choice_axiom,[])).
% 2.45/1.01  
% 2.45/1.01  fof(f57,plain,(
% 2.45/1.01    ~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7)),
% 2.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f41,f56])).
% 2.45/1.01  
% 2.45/1.01  fof(f89,plain,(
% 2.45/1.01    v1_funct_2(sK7,k1_tarski(sK5),sK6)),
% 2.45/1.01    inference(cnf_transformation,[],[f57])).
% 2.45/1.01  
% 2.45/1.01  fof(f3,axiom,(
% 2.45/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f60,plain,(
% 2.45/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f3])).
% 2.45/1.01  
% 2.45/1.01  fof(f4,axiom,(
% 2.45/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f61,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f4])).
% 2.45/1.01  
% 2.45/1.01  fof(f5,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f62,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f5])).
% 2.45/1.01  
% 2.45/1.01  fof(f93,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.45/1.01    inference(definition_unfolding,[],[f61,f62])).
% 2.45/1.01  
% 2.45/1.01  fof(f94,plain,(
% 2.45/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.45/1.01    inference(definition_unfolding,[],[f60,f93])).
% 2.45/1.01  
% 2.45/1.01  fof(f100,plain,(
% 2.45/1.01    v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6)),
% 2.45/1.01    inference(definition_unfolding,[],[f89,f94])).
% 2.45/1.01  
% 2.45/1.01  fof(f90,plain,(
% 2.45/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))),
% 2.45/1.01    inference(cnf_transformation,[],[f57])).
% 2.45/1.01  
% 2.45/1.01  fof(f99,plain,(
% 2.45/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))),
% 2.45/1.01    inference(definition_unfolding,[],[f90,f94])).
% 2.45/1.01  
% 2.45/1.01  fof(f91,plain,(
% 2.45/1.01    k1_xboole_0 != sK6),
% 2.45/1.01    inference(cnf_transformation,[],[f57])).
% 2.45/1.01  
% 2.45/1.01  fof(f17,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f36,plain,(
% 2.45/1.01    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.45/1.01    inference(ennf_transformation,[],[f17])).
% 2.45/1.01  
% 2.45/1.01  fof(f48,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.45/1.01    inference(nnf_transformation,[],[f36])).
% 2.45/1.01  
% 2.45/1.01  fof(f49,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.45/1.01    inference(rectify,[],[f48])).
% 2.45/1.01  
% 2.45/1.01  fof(f51,plain,(
% 2.45/1.01    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 2.45/1.01    introduced(choice_axiom,[])).
% 2.45/1.01  
% 2.45/1.01  fof(f50,plain,(
% 2.45/1.01    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 2.45/1.01    introduced(choice_axiom,[])).
% 2.45/1.01  
% 2.45/1.01  fof(f52,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f49,f51,f50])).
% 2.45/1.01  
% 2.45/1.01  fof(f80,plain,(
% 2.45/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f52])).
% 2.45/1.01  
% 2.45/1.01  fof(f1,axiom,(
% 2.45/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f58,plain,(
% 2.45/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.45/1.01    inference(cnf_transformation,[],[f1])).
% 2.45/1.01  
% 2.45/1.01  fof(f7,axiom,(
% 2.45/1.01    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f66,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f7])).
% 2.45/1.01  
% 2.45/1.01  fof(f98,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 2.45/1.01    inference(definition_unfolding,[],[f66,f94])).
% 2.45/1.01  
% 2.45/1.01  fof(f13,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f31,plain,(
% 2.45/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.45/1.01    inference(ennf_transformation,[],[f13])).
% 2.45/1.01  
% 2.45/1.01  fof(f32,plain,(
% 2.45/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.45/1.01    inference(flattening,[],[f31])).
% 2.45/1.01  
% 2.45/1.01  fof(f46,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.45/1.01    inference(nnf_transformation,[],[f32])).
% 2.45/1.01  
% 2.45/1.01  fof(f47,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.45/1.01    inference(flattening,[],[f46])).
% 2.45/1.01  
% 2.45/1.01  fof(f72,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f47])).
% 2.45/1.01  
% 2.45/1.01  fof(f88,plain,(
% 2.45/1.01    v1_funct_1(sK7)),
% 2.45/1.01    inference(cnf_transformation,[],[f57])).
% 2.45/1.01  
% 2.45/1.01  fof(f15,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f34,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(ennf_transformation,[],[f15])).
% 2.45/1.01  
% 2.45/1.01  fof(f76,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f34])).
% 2.45/1.01  
% 2.45/1.01  fof(f74,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f47])).
% 2.45/1.01  
% 2.45/1.01  fof(f102,plain,(
% 2.45/1.01    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.45/1.01    inference(equality_resolution,[],[f74])).
% 2.45/1.01  
% 2.45/1.01  fof(f8,axiom,(
% 2.45/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f24,plain,(
% 2.45/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/1.01    inference(ennf_transformation,[],[f8])).
% 2.45/1.01  
% 2.45/1.01  fof(f67,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f24])).
% 2.45/1.01  
% 2.45/1.01  fof(f6,axiom,(
% 2.45/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f42,plain,(
% 2.45/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 2.45/1.01    inference(nnf_transformation,[],[f6])).
% 2.45/1.01  
% 2.45/1.01  fof(f43,plain,(
% 2.45/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 2.45/1.01    inference(flattening,[],[f42])).
% 2.45/1.01  
% 2.45/1.01  fof(f63,plain,(
% 2.45/1.01    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f43])).
% 2.45/1.01  
% 2.45/1.01  fof(f97,plain,(
% 2.45/1.01    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))) )),
% 2.45/1.01    inference(definition_unfolding,[],[f63,f94])).
% 2.45/1.01  
% 2.45/1.01  fof(f16,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f23,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.45/1.01    inference(pure_predicate_removal,[],[f16])).
% 2.45/1.01  
% 2.45/1.01  fof(f35,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(ennf_transformation,[],[f23])).
% 2.45/1.01  
% 2.45/1.01  fof(f77,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f35])).
% 2.45/1.01  
% 2.45/1.01  fof(f12,axiom,(
% 2.45/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f29,plain,(
% 2.45/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.45/1.01    inference(ennf_transformation,[],[f12])).
% 2.45/1.01  
% 2.45/1.01  fof(f30,plain,(
% 2.45/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(flattening,[],[f29])).
% 2.45/1.01  
% 2.45/1.01  fof(f71,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f30])).
% 2.45/1.01  
% 2.45/1.01  fof(f92,plain,(
% 2.45/1.01    ~r2_hidden(k1_funct_1(sK7,sK5),sK6)),
% 2.45/1.01    inference(cnf_transformation,[],[f57])).
% 2.45/1.01  
% 2.45/1.01  fof(f2,axiom,(
% 2.45/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f59,plain,(
% 2.45/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f2])).
% 2.45/1.01  
% 2.45/1.01  fof(f14,axiom,(
% 2.45/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f33,plain,(
% 2.45/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.45/1.01    inference(ennf_transformation,[],[f14])).
% 2.45/1.01  
% 2.45/1.01  fof(f75,plain,(
% 2.45/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f33])).
% 2.45/1.01  
% 2.45/1.01  cnf(c_20,plain,
% 2.45/1.01      ( r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1172,plain,
% 2.45/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0) = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_26,plain,
% 2.45/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.45/1.01      | k1_xboole_0 = X2 ),
% 2.45/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_30,negated_conjecture,
% 2.45/1.01      ( v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
% 2.45/1.01      inference(cnf_transformation,[],[f100]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_567,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | k2_enumset1(sK5,sK5,sK5,sK5) != X1
% 2.45/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.45/1.01      | sK6 != X2
% 2.45/1.01      | sK7 != X0
% 2.45/1.01      | k1_xboole_0 = X2 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_568,plain,
% 2.45/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
% 2.45/1.01      | k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5)
% 2.45/1.01      | k1_xboole_0 = sK6 ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_567]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_29,negated_conjecture,
% 2.45/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
% 2.45/1.01      inference(cnf_transformation,[],[f99]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_28,negated_conjecture,
% 2.45/1.01      ( k1_xboole_0 != sK6 ),
% 2.45/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_570,plain,
% 2.45/1.01      ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_568,c_29,c_28]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_17,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | ~ r2_hidden(X3,X1)
% 2.45/1.01      | r2_hidden(k4_tarski(X3,sK2(X0,X3)),X0)
% 2.45/1.01      | k1_relset_1(X1,X2,X0) != X1 ),
% 2.45/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1175,plain,
% 2.45/1.01      ( k1_relset_1(X0,X1,X2) != X0
% 2.45/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.45/1.01      | r2_hidden(X3,X0) != iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_3418,plain,
% 2.45/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
% 2.45/1.01      | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_570,c_1175]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_34,plain,
% 2.45/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_3558,plain,
% 2.45/1.01      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
% 2.45/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3418,c_34]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_3567,plain,
% 2.45/1.01      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
% 2.45/1.01      | r2_hidden(k4_tarski(sK4(k2_enumset1(sK5,sK5,sK5,sK5)),sK2(sK7,sK4(k2_enumset1(sK5,sK5,sK5,sK5)))),sK7) = iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1172,c_3558]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_0,plain,
% 2.45/1.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_5,plain,
% 2.45/1.01      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f98]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1587,plain,
% 2.45/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_3802,plain,
% 2.45/1.01      ( r2_hidden(k4_tarski(sK4(k2_enumset1(sK5,sK5,sK5,sK5)),sK2(sK7,sK4(k2_enumset1(sK5,sK5,sK5,sK5)))),sK7) = iProver_top ),
% 2.45/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3567,c_1587]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_13,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(X1))
% 2.45/1.01      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.45/1.01      | ~ v1_funct_1(X1)
% 2.45/1.01      | ~ v1_relat_1(X1) ),
% 2.45/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_31,negated_conjecture,
% 2.45/1.01      ( v1_funct_1(sK7) ),
% 2.45/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_405,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(X1))
% 2.45/1.01      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.45/1.01      | ~ v1_relat_1(X1)
% 2.45/1.01      | sK7 != X1 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_406,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(sK7))
% 2.45/1.01      | ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 2.45/1.01      | ~ v1_relat_1(sK7) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_405]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1166,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.45/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_407,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.45/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_15,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.45/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1355,plain,
% 2.45/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
% 2.45/1.01      | v1_relat_1(sK7) ),
% 2.45/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1356,plain,
% 2.45/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
% 2.45/1.01      | v1_relat_1(sK7) = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_1355]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1388,plain,
% 2.45/1.01      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.45/1.01      | r2_hidden(X0,k1_relat_1(sK7)) = iProver_top ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_1166,c_34,c_407,c_1356]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1389,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 2.45/1.01      inference(renaming,[status(thm)],[c_1388]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_3805,plain,
% 2.45/1.01      ( r2_hidden(sK4(k2_enumset1(sK5,sK5,sK5,sK5)),k1_relat_1(sK7)) = iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_3802,c_1389]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_11,plain,
% 2.45/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.45/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.45/1.01      | ~ v1_funct_1(X1)
% 2.45/1.01      | ~ v1_relat_1(X1) ),
% 2.45/1.01      inference(cnf_transformation,[],[f102]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_420,plain,
% 2.45/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.45/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.45/1.01      | ~ v1_relat_1(X1)
% 2.45/1.01      | sK7 != X1 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_421,plain,
% 2.45/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 2.45/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
% 2.45/1.01      | ~ v1_relat_1(sK7) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_420]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1165,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 2.45/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_422,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 2.45/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1441,plain,
% 2.45/1.01      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 2.45/1.01      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_1165,c_34,c_422,c_1356]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1442,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.45/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top ),
% 2.45/1.01      inference(renaming,[status(thm)],[c_1441]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1170,plain,
% 2.45/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_6,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/1.01      | ~ r2_hidden(X2,X0)
% 2.45/1.01      | r2_hidden(X2,X1) ),
% 2.45/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1180,plain,
% 2.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.45/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.45/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2340,plain,
% 2.45/1.01      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) = iProver_top
% 2.45/1.01      | r2_hidden(X0,sK7) != iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1170,c_1180]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_4,plain,
% 2.45/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
% 2.45/1.01      | X2 = X0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f97]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1181,plain,
% 2.45/1.01      ( X0 = X1
% 2.45/1.01      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2437,plain,
% 2.45/1.01      ( sK5 = X0 | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_2340,c_1181]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2553,plain,
% 2.45/1.01      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1442,c_2437]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2572,plain,
% 2.45/1.01      ( sK4(k1_relat_1(sK7)) = sK5 | k1_relat_1(sK7) = k1_xboole_0 ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1172,c_2553]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_4092,plain,
% 2.45/1.01      ( k1_relat_1(sK7) = k1_xboole_0
% 2.45/1.01      | r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_2572,c_1172]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_16,plain,
% 2.45/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.45/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_10,plain,
% 2.45/1.01      ( ~ v5_relat_1(X0,X1)
% 2.45/1.01      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.45/1.01      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.45/1.01      | ~ v1_funct_1(X0)
% 2.45/1.01      | ~ v1_relat_1(X0) ),
% 2.45/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_347,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.45/1.01      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.45/1.01      | ~ v1_funct_1(X0)
% 2.45/1.01      | ~ v1_relat_1(X0) ),
% 2.45/1.01      inference(resolution,[status(thm)],[c_16,c_10]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_351,plain,
% 2.45/1.01      ( ~ v1_funct_1(X0)
% 2.45/1.01      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.45/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.45/1.01      inference(global_propositional_subsumption,[status(thm)],[c_347,c_15]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_352,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.45/1.01      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.45/1.01      | ~ v1_funct_1(X0) ),
% 2.45/1.01      inference(renaming,[status(thm)],[c_351]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_390,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.45/1.01      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.45/1.01      | sK7 != X0 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_352,c_31]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_391,plain,
% 2.45/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.45/1.01      | ~ r2_hidden(X2,k1_relat_1(sK7))
% 2.45/1.01      | r2_hidden(k1_funct_1(sK7,X2),X1) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_390]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1167,plain,
% 2.45/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.45/1.01      | r2_hidden(X2,k1_relat_1(sK7)) != iProver_top
% 2.45/1.01      | r2_hidden(k1_funct_1(sK7,X2),X1) = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1663,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.45/1.01      | r2_hidden(k1_funct_1(sK7,X0),sK6) = iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1170,c_1167]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_27,negated_conjecture,
% 2.45/1.01      ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
% 2.45/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1171,plain,
% 2.45/1.01      ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1794,plain,
% 2.45/1.01      ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1663,c_1171]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_4107,plain,
% 2.45/1.01      ( k1_relat_1(sK7) = k1_xboole_0 ),
% 2.45/1.01      inference(global_propositional_subsumption,[status(thm)],[c_4092,c_1794]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_4254,plain,
% 2.45/1.01      ( r2_hidden(sK4(k2_enumset1(sK5,sK5,sK5,sK5)),k1_xboole_0) = iProver_top ),
% 2.45/1.01      inference(light_normalisation,[status(thm)],[c_3805,c_4107]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1,plain,
% 2.45/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.45/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_14,plain,
% 2.45/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.45/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_336,plain,
% 2.45/1.01      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_337,plain,
% 2.45/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_336]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1169,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_4256,plain,
% 2.45/1.01      ( $false ),
% 2.45/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4254,c_1169]) ).
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/1.01  
% 2.45/1.01  ------                               Statistics
% 2.45/1.01  
% 2.45/1.01  ------ General
% 2.45/1.01  
% 2.45/1.01  abstr_ref_over_cycles:                  0
% 2.45/1.01  abstr_ref_under_cycles:                 0
% 2.45/1.01  gc_basic_clause_elim:                   0
% 2.45/1.01  forced_gc_time:                         0
% 2.45/1.01  parsing_time:                           0.012
% 2.45/1.01  unif_index_cands_time:                  0.
% 2.45/1.01  unif_index_add_time:                    0.
% 2.45/1.01  orderings_time:                         0.
% 2.45/1.01  out_proof_time:                         0.009
% 2.45/1.01  total_time:                             0.152
% 2.45/1.01  num_of_symbols:                         55
% 2.45/1.01  num_of_terms:                           4484
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing
% 2.45/1.01  
% 2.45/1.01  num_of_splits:                          0
% 2.45/1.01  num_of_split_atoms:                     0
% 2.45/1.01  num_of_reused_defs:                     0
% 2.45/1.01  num_eq_ax_congr_red:                    28
% 2.45/1.01  num_of_sem_filtered_clauses:            1
% 2.45/1.01  num_of_subtypes:                        0
% 2.45/1.01  monotx_restored_types:                  0
% 2.45/1.01  sat_num_of_epr_types:                   0
% 2.45/1.01  sat_num_of_non_cyclic_types:            0
% 2.45/1.01  sat_guarded_non_collapsed_types:        0
% 2.45/1.01  num_pure_diseq_elim:                    0
% 2.45/1.01  simp_replaced_by:                       0
% 2.45/1.01  res_preprocessed:                       134
% 2.45/1.01  prep_upred:                             0
% 2.45/1.01  prep_unflattend:                        39
% 2.45/1.01  smt_new_axioms:                         0
% 2.45/1.01  pred_elim_cands:                        3
% 2.45/1.01  pred_elim:                              4
% 2.45/1.01  pred_elim_cl:                           7
% 2.45/1.01  pred_elim_cycles:                       7
% 2.45/1.01  merged_defs:                            0
% 2.45/1.01  merged_defs_ncl:                        0
% 2.45/1.01  bin_hyper_res:                          0
% 2.45/1.01  prep_cycles:                            4
% 2.45/1.01  pred_elim_time:                         0.015
% 2.45/1.01  splitting_time:                         0.
% 2.45/1.01  sem_filter_time:                        0.
% 2.45/1.01  monotx_time:                            0.
% 2.45/1.01  subtype_inf_time:                       0.
% 2.45/1.01  
% 2.45/1.01  ------ Problem properties
% 2.45/1.01  
% 2.45/1.01  clauses:                                25
% 2.45/1.01  conjectures:                            3
% 2.45/1.01  epr:                                    2
% 2.45/1.01  horn:                                   21
% 2.45/1.01  ground:                                 6
% 2.45/1.01  unary:                                  8
% 2.45/1.01  binary:                                 5
% 2.45/1.01  lits:                                   56
% 2.45/1.01  lits_eq:                                16
% 2.45/1.01  fd_pure:                                0
% 2.45/1.01  fd_pseudo:                              0
% 2.45/1.01  fd_cond:                                2
% 2.45/1.01  fd_pseudo_cond:                         2
% 2.45/1.01  ac_symbols:                             0
% 2.45/1.01  
% 2.45/1.01  ------ Propositional Solver
% 2.45/1.01  
% 2.45/1.01  prop_solver_calls:                      27
% 2.45/1.01  prop_fast_solver_calls:                 848
% 2.45/1.01  smt_solver_calls:                       0
% 2.45/1.01  smt_fast_solver_calls:                  0
% 2.45/1.01  prop_num_of_clauses:                    1461
% 2.45/1.01  prop_preprocess_simplified:             5563
% 2.45/1.01  prop_fo_subsumed:                       15
% 2.45/1.01  prop_solver_time:                       0.
% 2.45/1.01  smt_solver_time:                        0.
% 2.45/1.01  smt_fast_solver_time:                   0.
% 2.45/1.01  prop_fast_solver_time:                  0.
% 2.45/1.01  prop_unsat_core_time:                   0.
% 2.45/1.01  
% 2.45/1.01  ------ QBF
% 2.45/1.01  
% 2.45/1.01  qbf_q_res:                              0
% 2.45/1.01  qbf_num_tautologies:                    0
% 2.45/1.01  qbf_prep_cycles:                        0
% 2.45/1.01  
% 2.45/1.01  ------ BMC1
% 2.45/1.01  
% 2.45/1.01  bmc1_current_bound:                     -1
% 2.45/1.01  bmc1_last_solved_bound:                 -1
% 2.45/1.01  bmc1_unsat_core_size:                   -1
% 2.45/1.01  bmc1_unsat_core_parents_size:           -1
% 2.45/1.01  bmc1_merge_next_fun:                    0
% 2.45/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.01  
% 2.45/1.01  ------ Instantiation
% 2.45/1.01  
% 2.45/1.01  inst_num_of_clauses:                    425
% 2.45/1.01  inst_num_in_passive:                    118
% 2.45/1.01  inst_num_in_active:                     223
% 2.45/1.01  inst_num_in_unprocessed:                84
% 2.45/1.01  inst_num_of_loops:                      260
% 2.45/1.01  inst_num_of_learning_restarts:          0
% 2.45/1.01  inst_num_moves_active_passive:          35
% 2.45/1.01  inst_lit_activity:                      0
% 2.45/1.01  inst_lit_activity_moves:                0
% 2.45/1.01  inst_num_tautologies:                   0
% 2.45/1.01  inst_num_prop_implied:                  0
% 2.45/1.01  inst_num_existing_simplified:           0
% 2.45/1.01  inst_num_eq_res_simplified:             0
% 2.45/1.01  inst_num_child_elim:                    0
% 2.45/1.01  inst_num_of_dismatching_blockings:      204
% 2.45/1.01  inst_num_of_non_proper_insts:           401
% 2.45/1.01  inst_num_of_duplicates:                 0
% 2.45/1.01  inst_inst_num_from_inst_to_res:         0
% 2.45/1.01  inst_dismatching_checking_time:         0.
% 2.45/1.01  
% 2.45/1.01  ------ Resolution
% 2.45/1.01  
% 2.45/1.01  res_num_of_clauses:                     0
% 2.45/1.01  res_num_in_passive:                     0
% 2.45/1.01  res_num_in_active:                      0
% 2.45/1.01  res_num_of_loops:                       138
% 2.45/1.01  res_forward_subset_subsumed:            24
% 2.45/1.01  res_backward_subset_subsumed:           0
% 2.45/1.01  res_forward_subsumed:                   0
% 2.45/1.01  res_backward_subsumed:                  0
% 2.45/1.01  res_forward_subsumption_resolution:     0
% 2.45/1.01  res_backward_subsumption_resolution:    0
% 2.45/1.01  res_clause_to_clause_subsumption:       110
% 2.45/1.01  res_orphan_elimination:                 0
% 2.45/1.01  res_tautology_del:                      31
% 2.45/1.01  res_num_eq_res_simplified:              0
% 2.45/1.01  res_num_sel_changes:                    0
% 2.45/1.01  res_moves_from_active_to_pass:          0
% 2.45/1.01  
% 2.45/1.01  ------ Superposition
% 2.45/1.01  
% 2.45/1.01  sup_time_total:                         0.
% 2.45/1.01  sup_time_generating:                    0.
% 2.45/1.01  sup_time_sim_full:                      0.
% 2.45/1.01  sup_time_sim_immed:                     0.
% 2.45/1.01  
% 2.45/1.01  sup_num_of_clauses:                     55
% 2.45/1.01  sup_num_in_active:                      38
% 2.45/1.01  sup_num_in_passive:                     17
% 2.45/1.01  sup_num_of_loops:                       50
% 2.45/1.01  sup_fw_superposition:                   24
% 2.45/1.01  sup_bw_superposition:                   30
% 2.45/1.01  sup_immediate_simplified:               11
% 2.45/1.01  sup_given_eliminated:                   2
% 2.45/1.01  comparisons_done:                       0
% 2.45/1.01  comparisons_avoided:                    9
% 2.45/1.01  
% 2.45/1.01  ------ Simplifications
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  sim_fw_subset_subsumed:                 7
% 2.45/1.01  sim_bw_subset_subsumed:                 2
% 2.45/1.01  sim_fw_subsumed:                        4
% 2.45/1.01  sim_bw_subsumed:                        0
% 2.45/1.01  sim_fw_subsumption_res:                 3
% 2.45/1.01  sim_bw_subsumption_res:                 0
% 2.45/1.01  sim_tautology_del:                      2
% 2.45/1.01  sim_eq_tautology_del:                   5
% 2.45/1.01  sim_eq_res_simp:                        0
% 2.45/1.01  sim_fw_demodulated:                     0
% 2.45/1.01  sim_bw_demodulated:                     15
% 2.45/1.01  sim_light_normalised:                   2
% 2.45/1.01  sim_joinable_taut:                      0
% 2.45/1.01  sim_joinable_simp:                      0
% 2.45/1.01  sim_ac_normalised:                      0
% 2.45/1.01  sim_smt_subsumption:                    0
% 2.45/1.01  
%------------------------------------------------------------------------------
