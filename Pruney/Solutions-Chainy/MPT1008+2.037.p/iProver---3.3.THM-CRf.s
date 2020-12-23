%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:11 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 712 expanded)
%              Number of clauses        :   77 ( 153 expanded)
%              Number of leaves         :   23 ( 185 expanded)
%              Depth                    :   20
%              Number of atoms          :  449 (1804 expanded)
%              Number of equality atoms :  252 (1019 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,
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

fof(f49,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f48])).

fof(f81,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f84])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f81,f85])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f56,f84,f85,f85,f84])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f83,f85,f85])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f85,f85])).

fof(f79,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f37])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f45,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f45,f44])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f80,f85])).

fof(f16,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f86,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f84])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_9])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_365,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_14])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_434,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_366,c_28])).

cnf(c_435,plain,
    ( r1_tarski(k1_relat_1(sK5),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_1527,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_1911,plain,
    ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1527])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1532,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2544,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1911,c_1532])).

cnf(c_2551,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = X0
    | k1_relat_1(sK5) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2544,c_1532])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_530,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_531,plain,
    ( k2_relset_1(X0,X1,sK5) = k2_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_1694,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_531])).

cnf(c_26,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1722,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_1694,c_26])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_342,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_343,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_1528,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_344,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_1191,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1677,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_539,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_540,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_1681,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_1682,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1681])).

cnf(c_1963,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1528,c_344,c_1677,c_1682])).

cnf(c_1964,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_1963])).

cnf(c_2563,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2544,c_1964])).

cnf(c_2815,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2551,c_1722,c_2563])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1530,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2830,plain,
    ( sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2815,c_1530])).

cnf(c_1879,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2069,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_1192,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2070,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_2403,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2070])).

cnf(c_2404,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2403])).

cnf(c_2833,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2830,c_1677,c_1681,c_1722,c_1879,c_2069,c_2404,c_2563])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1539,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_512,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK1(X2,X0)),X2)
    | k1_relset_1(X1,X3,X2) != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X3))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_513,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5)
    | k1_relset_1(X1,X2,sK5) != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_1524,plain,
    ( k1_relset_1(X0,X1,sK5) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k4_tarski(X2,sK1(sK5,X2)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_1993,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_enumset1(sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1524])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_446,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_28])).

cnf(c_447,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_845,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X1
    | sK5 != sK5
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_447])).

cnf(c_846,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_847,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_27])).

cnf(c_848,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_847])).

cnf(c_914,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_848])).

cnf(c_1994,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k2_enumset1(sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1993,c_914])).

cnf(c_1995,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1994])).

cnf(c_2147,plain,
    ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),sK1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3)))),sK5) = iProver_top
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1995])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1537,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2311,plain,
    ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),sK1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3)))),sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2147,c_1537])).

cnf(c_2837,plain,
    ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),sK1(k1_xboole_0,sK0(k2_enumset1(sK3,sK3,sK3,sK3)))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2833,c_2311])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1538,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1529,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1906,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_1529])).

cnf(c_3456,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2837,c_1906])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n019.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 19:54:22 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 1.96/0.89  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/0.89  
% 1.96/0.89  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/0.89  
% 1.96/0.89  ------  iProver source info
% 1.96/0.89  
% 1.96/0.89  git: date: 2020-06-30 10:37:57 +0100
% 1.96/0.89  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/0.89  git: non_committed_changes: false
% 1.96/0.89  git: last_make_outside_of_git: false
% 1.96/0.89  
% 1.96/0.89  ------ 
% 1.96/0.89  
% 1.96/0.89  ------ Input Options
% 1.96/0.89  
% 1.96/0.89  --out_options                           all
% 1.96/0.89  --tptp_safe_out                         true
% 1.96/0.89  --problem_path                          ""
% 1.96/0.89  --include_path                          ""
% 1.96/0.89  --clausifier                            res/vclausify_rel
% 1.96/0.89  --clausifier_options                    --mode clausify
% 1.96/0.89  --stdin                                 false
% 1.96/0.89  --stats_out                             all
% 1.96/0.89  
% 1.96/0.89  ------ General Options
% 1.96/0.89  
% 1.96/0.89  --fof                                   false
% 1.96/0.89  --time_out_real                         305.
% 1.96/0.89  --time_out_virtual                      -1.
% 1.96/0.89  --symbol_type_check                     false
% 1.96/0.89  --clausify_out                          false
% 1.96/0.89  --sig_cnt_out                           false
% 1.96/0.89  --trig_cnt_out                          false
% 1.96/0.89  --trig_cnt_out_tolerance                1.
% 1.96/0.89  --trig_cnt_out_sk_spl                   false
% 1.96/0.89  --abstr_cl_out                          false
% 1.96/0.89  
% 1.96/0.89  ------ Global Options
% 1.96/0.89  
% 1.96/0.89  --schedule                              default
% 1.96/0.89  --add_important_lit                     false
% 1.96/0.89  --prop_solver_per_cl                    1000
% 1.96/0.89  --min_unsat_core                        false
% 1.96/0.89  --soft_assumptions                      false
% 1.96/0.89  --soft_lemma_size                       3
% 1.96/0.89  --prop_impl_unit_size                   0
% 1.96/0.89  --prop_impl_unit                        []
% 1.96/0.89  --share_sel_clauses                     true
% 1.96/0.89  --reset_solvers                         false
% 1.96/0.89  --bc_imp_inh                            [conj_cone]
% 1.96/0.89  --conj_cone_tolerance                   3.
% 1.96/0.89  --extra_neg_conj                        none
% 1.96/0.89  --large_theory_mode                     true
% 1.96/0.89  --prolific_symb_bound                   200
% 1.96/0.89  --lt_threshold                          2000
% 1.96/0.89  --clause_weak_htbl                      true
% 1.96/0.89  --gc_record_bc_elim                     false
% 1.96/0.89  
% 1.96/0.89  ------ Preprocessing Options
% 1.96/0.89  
% 1.96/0.89  --preprocessing_flag                    true
% 1.96/0.89  --time_out_prep_mult                    0.1
% 1.96/0.89  --splitting_mode                        input
% 1.96/0.89  --splitting_grd                         true
% 1.96/0.89  --splitting_cvd                         false
% 1.96/0.89  --splitting_cvd_svl                     false
% 1.96/0.89  --splitting_nvd                         32
% 1.96/0.89  --sub_typing                            true
% 1.96/0.89  --prep_gs_sim                           true
% 1.96/0.89  --prep_unflatten                        true
% 1.96/0.89  --prep_res_sim                          true
% 1.96/0.89  --prep_upred                            true
% 1.96/0.89  --prep_sem_filter                       exhaustive
% 1.96/0.89  --prep_sem_filter_out                   false
% 1.96/0.89  --pred_elim                             true
% 1.96/0.89  --res_sim_input                         true
% 1.96/0.89  --eq_ax_congr_red                       true
% 1.96/0.89  --pure_diseq_elim                       true
% 1.96/0.89  --brand_transform                       false
% 1.96/0.89  --non_eq_to_eq                          false
% 1.96/0.89  --prep_def_merge                        true
% 1.96/0.89  --prep_def_merge_prop_impl              false
% 1.96/0.89  --prep_def_merge_mbd                    true
% 1.96/0.89  --prep_def_merge_tr_red                 false
% 1.96/0.89  --prep_def_merge_tr_cl                  false
% 1.96/0.89  --smt_preprocessing                     true
% 1.96/0.89  --smt_ac_axioms                         fast
% 1.96/0.89  --preprocessed_out                      false
% 1.96/0.89  --preprocessed_stats                    false
% 1.96/0.89  
% 1.96/0.89  ------ Abstraction refinement Options
% 1.96/0.89  
% 1.96/0.89  --abstr_ref                             []
% 1.96/0.89  --abstr_ref_prep                        false
% 1.96/0.89  --abstr_ref_until_sat                   false
% 1.96/0.89  --abstr_ref_sig_restrict                funpre
% 1.96/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/0.89  --abstr_ref_under                       []
% 1.96/0.89  
% 1.96/0.89  ------ SAT Options
% 1.96/0.89  
% 1.96/0.89  --sat_mode                              false
% 1.96/0.89  --sat_fm_restart_options                ""
% 1.96/0.89  --sat_gr_def                            false
% 1.96/0.89  --sat_epr_types                         true
% 1.96/0.89  --sat_non_cyclic_types                  false
% 1.96/0.89  --sat_finite_models                     false
% 1.96/0.89  --sat_fm_lemmas                         false
% 1.96/0.89  --sat_fm_prep                           false
% 1.96/0.89  --sat_fm_uc_incr                        true
% 1.96/0.89  --sat_out_model                         small
% 1.96/0.89  --sat_out_clauses                       false
% 1.96/0.89  
% 1.96/0.89  ------ QBF Options
% 1.96/0.89  
% 1.96/0.89  --qbf_mode                              false
% 1.96/0.89  --qbf_elim_univ                         false
% 1.96/0.89  --qbf_dom_inst                          none
% 1.96/0.89  --qbf_dom_pre_inst                      false
% 1.96/0.89  --qbf_sk_in                             false
% 1.96/0.89  --qbf_pred_elim                         true
% 1.96/0.89  --qbf_split                             512
% 1.96/0.89  
% 1.96/0.89  ------ BMC1 Options
% 1.96/0.89  
% 1.96/0.89  --bmc1_incremental                      false
% 1.96/0.89  --bmc1_axioms                           reachable_all
% 1.96/0.89  --bmc1_min_bound                        0
% 1.96/0.89  --bmc1_max_bound                        -1
% 1.96/0.89  --bmc1_max_bound_default                -1
% 1.96/0.89  --bmc1_symbol_reachability              true
% 1.96/0.89  --bmc1_property_lemmas                  false
% 1.96/0.89  --bmc1_k_induction                      false
% 1.96/0.89  --bmc1_non_equiv_states                 false
% 1.96/0.89  --bmc1_deadlock                         false
% 1.96/0.89  --bmc1_ucm                              false
% 1.96/0.89  --bmc1_add_unsat_core                   none
% 1.96/0.89  --bmc1_unsat_core_children              false
% 1.96/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/0.89  --bmc1_out_stat                         full
% 1.96/0.89  --bmc1_ground_init                      false
% 1.96/0.89  --bmc1_pre_inst_next_state              false
% 1.96/0.89  --bmc1_pre_inst_state                   false
% 1.96/0.89  --bmc1_pre_inst_reach_state             false
% 1.96/0.89  --bmc1_out_unsat_core                   false
% 1.96/0.89  --bmc1_aig_witness_out                  false
% 1.96/0.89  --bmc1_verbose                          false
% 1.96/0.89  --bmc1_dump_clauses_tptp                false
% 1.96/0.89  --bmc1_dump_unsat_core_tptp             false
% 1.96/0.89  --bmc1_dump_file                        -
% 1.96/0.89  --bmc1_ucm_expand_uc_limit              128
% 1.96/0.89  --bmc1_ucm_n_expand_iterations          6
% 1.96/0.89  --bmc1_ucm_extend_mode                  1
% 1.96/0.89  --bmc1_ucm_init_mode                    2
% 1.96/0.89  --bmc1_ucm_cone_mode                    none
% 1.96/0.89  --bmc1_ucm_reduced_relation_type        0
% 1.96/0.89  --bmc1_ucm_relax_model                  4
% 1.96/0.89  --bmc1_ucm_full_tr_after_sat            true
% 1.96/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/0.89  --bmc1_ucm_layered_model                none
% 1.96/0.89  --bmc1_ucm_max_lemma_size               10
% 1.96/0.89  
% 1.96/0.89  ------ AIG Options
% 1.96/0.89  
% 1.96/0.89  --aig_mode                              false
% 1.96/0.89  
% 1.96/0.89  ------ Instantiation Options
% 1.96/0.89  
% 1.96/0.89  --instantiation_flag                    true
% 1.96/0.89  --inst_sos_flag                         false
% 1.96/0.89  --inst_sos_phase                        true
% 1.96/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/0.89  --inst_lit_sel_side                     num_symb
% 1.96/0.89  --inst_solver_per_active                1400
% 1.96/0.89  --inst_solver_calls_frac                1.
% 1.96/0.89  --inst_passive_queue_type               priority_queues
% 1.96/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/0.89  --inst_passive_queues_freq              [25;2]
% 1.96/0.89  --inst_dismatching                      true
% 1.96/0.89  --inst_eager_unprocessed_to_passive     true
% 1.96/0.89  --inst_prop_sim_given                   true
% 1.96/0.89  --inst_prop_sim_new                     false
% 1.96/0.89  --inst_subs_new                         false
% 1.96/0.89  --inst_eq_res_simp                      false
% 1.96/0.89  --inst_subs_given                       false
% 1.96/0.89  --inst_orphan_elimination               true
% 1.96/0.89  --inst_learning_loop_flag               true
% 1.96/0.89  --inst_learning_start                   3000
% 1.96/0.89  --inst_learning_factor                  2
% 1.96/0.89  --inst_start_prop_sim_after_learn       3
% 1.96/0.89  --inst_sel_renew                        solver
% 1.96/0.89  --inst_lit_activity_flag                true
% 1.96/0.89  --inst_restr_to_given                   false
% 1.96/0.89  --inst_activity_threshold               500
% 1.96/0.89  --inst_out_proof                        true
% 1.96/0.89  
% 1.96/0.89  ------ Resolution Options
% 1.96/0.89  
% 1.96/0.89  --resolution_flag                       true
% 1.96/0.89  --res_lit_sel                           adaptive
% 1.96/0.89  --res_lit_sel_side                      none
% 1.96/0.89  --res_ordering                          kbo
% 1.96/0.89  --res_to_prop_solver                    active
% 1.96/0.89  --res_prop_simpl_new                    false
% 1.96/0.89  --res_prop_simpl_given                  true
% 1.96/0.89  --res_passive_queue_type                priority_queues
% 1.96/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/0.89  --res_passive_queues_freq               [15;5]
% 1.96/0.89  --res_forward_subs                      full
% 1.96/0.89  --res_backward_subs                     full
% 1.96/0.89  --res_forward_subs_resolution           true
% 1.96/0.89  --res_backward_subs_resolution          true
% 1.96/0.89  --res_orphan_elimination                true
% 1.96/0.89  --res_time_limit                        2.
% 1.96/0.89  --res_out_proof                         true
% 1.96/0.89  
% 1.96/0.89  ------ Superposition Options
% 1.96/0.89  
% 1.96/0.89  --superposition_flag                    true
% 1.96/0.89  --sup_passive_queue_type                priority_queues
% 1.96/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/0.89  --sup_passive_queues_freq               [8;1;4]
% 1.96/0.89  --demod_completeness_check              fast
% 1.96/0.89  --demod_use_ground                      true
% 1.96/0.89  --sup_to_prop_solver                    passive
% 1.96/0.89  --sup_prop_simpl_new                    true
% 1.96/0.89  --sup_prop_simpl_given                  true
% 1.96/0.89  --sup_fun_splitting                     false
% 1.96/0.89  --sup_smt_interval                      50000
% 1.96/0.89  
% 1.96/0.89  ------ Superposition Simplification Setup
% 1.96/0.89  
% 1.96/0.89  --sup_indices_passive                   []
% 1.96/0.89  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.89  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.89  --sup_full_bw                           [BwDemod]
% 1.96/0.89  --sup_immed_triv                        [TrivRules]
% 1.96/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.89  --sup_immed_bw_main                     []
% 1.96/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.89  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.89  
% 1.96/0.89  ------ Combination Options
% 1.96/0.89  
% 1.96/0.89  --comb_res_mult                         3
% 1.96/0.89  --comb_sup_mult                         2
% 1.96/0.89  --comb_inst_mult                        10
% 1.96/0.89  
% 1.96/0.89  ------ Debug Options
% 1.96/0.89  
% 1.96/0.89  --dbg_backtrace                         false
% 1.96/0.89  --dbg_dump_prop_clauses                 false
% 1.96/0.89  --dbg_dump_prop_clauses_file            -
% 1.96/0.89  --dbg_out_stat                          false
% 1.96/0.89  ------ Parsing...
% 1.96/0.89  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/0.89  
% 1.96/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.96/0.89  
% 1.96/0.89  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/0.89  
% 1.96/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/0.89  ------ Proving...
% 1.96/0.89  ------ Problem Properties 
% 1.96/0.89  
% 1.96/0.89  
% 1.96/0.89  clauses                                 23
% 1.96/0.89  conjectures                             2
% 1.96/0.89  EPR                                     3
% 1.96/0.89  Horn                                    19
% 1.96/0.89  unary                                   9
% 1.96/0.89  binary                                  5
% 1.96/0.89  lits                                    50
% 1.96/0.89  lits eq                                 30
% 1.96/0.89  fd_pure                                 0
% 1.96/0.89  fd_pseudo                               0
% 1.96/0.89  fd_cond                                 2
% 1.96/0.89  fd_pseudo_cond                          1
% 1.96/0.89  AC symbols                              0
% 1.96/0.89  
% 1.96/0.89  ------ Schedule dynamic 5 is on 
% 1.96/0.89  
% 1.96/0.89  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/0.89  
% 1.96/0.89  
% 1.96/0.89  ------ 
% 1.96/0.89  Current options:
% 1.96/0.89  ------ 
% 1.96/0.89  
% 1.96/0.89  ------ Input Options
% 1.96/0.89  
% 1.96/0.89  --out_options                           all
% 1.96/0.89  --tptp_safe_out                         true
% 1.96/0.89  --problem_path                          ""
% 1.96/0.89  --include_path                          ""
% 1.96/0.89  --clausifier                            res/vclausify_rel
% 1.96/0.89  --clausifier_options                    --mode clausify
% 1.96/0.89  --stdin                                 false
% 1.96/0.89  --stats_out                             all
% 1.96/0.89  
% 1.96/0.89  ------ General Options
% 1.96/0.89  
% 1.96/0.89  --fof                                   false
% 1.96/0.89  --time_out_real                         305.
% 1.96/0.89  --time_out_virtual                      -1.
% 1.96/0.89  --symbol_type_check                     false
% 1.96/0.89  --clausify_out                          false
% 1.96/0.89  --sig_cnt_out                           false
% 1.96/0.89  --trig_cnt_out                          false
% 1.96/0.89  --trig_cnt_out_tolerance                1.
% 1.96/0.89  --trig_cnt_out_sk_spl                   false
% 1.96/0.89  --abstr_cl_out                          false
% 1.96/0.89  
% 1.96/0.89  ------ Global Options
% 1.96/0.89  
% 1.96/0.89  --schedule                              default
% 1.96/0.89  --add_important_lit                     false
% 1.96/0.89  --prop_solver_per_cl                    1000
% 1.96/0.89  --min_unsat_core                        false
% 1.96/0.89  --soft_assumptions                      false
% 1.96/0.89  --soft_lemma_size                       3
% 1.96/0.89  --prop_impl_unit_size                   0
% 1.96/0.89  --prop_impl_unit                        []
% 1.96/0.89  --share_sel_clauses                     true
% 1.96/0.89  --reset_solvers                         false
% 1.96/0.89  --bc_imp_inh                            [conj_cone]
% 1.96/0.89  --conj_cone_tolerance                   3.
% 1.96/0.89  --extra_neg_conj                        none
% 1.96/0.89  --large_theory_mode                     true
% 1.96/0.89  --prolific_symb_bound                   200
% 1.96/0.89  --lt_threshold                          2000
% 1.96/0.89  --clause_weak_htbl                      true
% 1.96/0.89  --gc_record_bc_elim                     false
% 1.96/0.89  
% 1.96/0.89  ------ Preprocessing Options
% 1.96/0.89  
% 1.96/0.89  --preprocessing_flag                    true
% 1.96/0.89  --time_out_prep_mult                    0.1
% 1.96/0.89  --splitting_mode                        input
% 1.96/0.89  --splitting_grd                         true
% 1.96/0.89  --splitting_cvd                         false
% 1.96/0.89  --splitting_cvd_svl                     false
% 1.96/0.89  --splitting_nvd                         32
% 1.96/0.89  --sub_typing                            true
% 1.96/0.89  --prep_gs_sim                           true
% 1.96/0.89  --prep_unflatten                        true
% 1.96/0.89  --prep_res_sim                          true
% 1.96/0.89  --prep_upred                            true
% 1.96/0.89  --prep_sem_filter                       exhaustive
% 1.96/0.89  --prep_sem_filter_out                   false
% 1.96/0.89  --pred_elim                             true
% 1.96/0.89  --res_sim_input                         true
% 1.96/0.89  --eq_ax_congr_red                       true
% 1.96/0.89  --pure_diseq_elim                       true
% 1.96/0.89  --brand_transform                       false
% 1.96/0.89  --non_eq_to_eq                          false
% 1.96/0.89  --prep_def_merge                        true
% 1.96/0.89  --prep_def_merge_prop_impl              false
% 1.96/0.89  --prep_def_merge_mbd                    true
% 1.96/0.89  --prep_def_merge_tr_red                 false
% 1.96/0.89  --prep_def_merge_tr_cl                  false
% 1.96/0.89  --smt_preprocessing                     true
% 1.96/0.89  --smt_ac_axioms                         fast
% 1.96/0.89  --preprocessed_out                      false
% 1.96/0.89  --preprocessed_stats                    false
% 1.96/0.89  
% 1.96/0.89  ------ Abstraction refinement Options
% 1.96/0.89  
% 1.96/0.89  --abstr_ref                             []
% 1.96/0.89  --abstr_ref_prep                        false
% 1.96/0.89  --abstr_ref_until_sat                   false
% 1.96/0.89  --abstr_ref_sig_restrict                funpre
% 1.96/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/0.89  --abstr_ref_under                       []
% 1.96/0.89  
% 1.96/0.89  ------ SAT Options
% 1.96/0.89  
% 1.96/0.89  --sat_mode                              false
% 1.96/0.89  --sat_fm_restart_options                ""
% 1.96/0.89  --sat_gr_def                            false
% 1.96/0.89  --sat_epr_types                         true
% 1.96/0.89  --sat_non_cyclic_types                  false
% 1.96/0.89  --sat_finite_models                     false
% 1.96/0.89  --sat_fm_lemmas                         false
% 1.96/0.89  --sat_fm_prep                           false
% 1.96/0.89  --sat_fm_uc_incr                        true
% 1.96/0.89  --sat_out_model                         small
% 1.96/0.89  --sat_out_clauses                       false
% 1.96/0.89  
% 1.96/0.89  ------ QBF Options
% 1.96/0.89  
% 1.96/0.89  --qbf_mode                              false
% 1.96/0.89  --qbf_elim_univ                         false
% 1.96/0.89  --qbf_dom_inst                          none
% 1.96/0.89  --qbf_dom_pre_inst                      false
% 1.96/0.89  --qbf_sk_in                             false
% 1.96/0.89  --qbf_pred_elim                         true
% 1.96/0.89  --qbf_split                             512
% 1.96/0.89  
% 1.96/0.89  ------ BMC1 Options
% 1.96/0.89  
% 1.96/0.89  --bmc1_incremental                      false
% 1.96/0.89  --bmc1_axioms                           reachable_all
% 1.96/0.89  --bmc1_min_bound                        0
% 1.96/0.89  --bmc1_max_bound                        -1
% 1.96/0.89  --bmc1_max_bound_default                -1
% 1.96/0.89  --bmc1_symbol_reachability              true
% 1.96/0.89  --bmc1_property_lemmas                  false
% 1.96/0.89  --bmc1_k_induction                      false
% 1.96/0.89  --bmc1_non_equiv_states                 false
% 1.96/0.89  --bmc1_deadlock                         false
% 1.96/0.89  --bmc1_ucm                              false
% 1.96/0.89  --bmc1_add_unsat_core                   none
% 1.96/0.89  --bmc1_unsat_core_children              false
% 1.96/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/0.89  --bmc1_out_stat                         full
% 1.96/0.89  --bmc1_ground_init                      false
% 1.96/0.89  --bmc1_pre_inst_next_state              false
% 1.96/0.89  --bmc1_pre_inst_state                   false
% 1.96/0.89  --bmc1_pre_inst_reach_state             false
% 1.96/0.89  --bmc1_out_unsat_core                   false
% 1.96/0.89  --bmc1_aig_witness_out                  false
% 1.96/0.89  --bmc1_verbose                          false
% 1.96/0.89  --bmc1_dump_clauses_tptp                false
% 1.96/0.89  --bmc1_dump_unsat_core_tptp             false
% 1.96/0.89  --bmc1_dump_file                        -
% 1.96/0.89  --bmc1_ucm_expand_uc_limit              128
% 1.96/0.89  --bmc1_ucm_n_expand_iterations          6
% 1.96/0.89  --bmc1_ucm_extend_mode                  1
% 1.96/0.89  --bmc1_ucm_init_mode                    2
% 1.96/0.89  --bmc1_ucm_cone_mode                    none
% 1.96/0.89  --bmc1_ucm_reduced_relation_type        0
% 1.96/0.89  --bmc1_ucm_relax_model                  4
% 1.96/0.89  --bmc1_ucm_full_tr_after_sat            true
% 1.96/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/0.89  --bmc1_ucm_layered_model                none
% 1.96/0.89  --bmc1_ucm_max_lemma_size               10
% 1.96/0.89  
% 1.96/0.89  ------ AIG Options
% 1.96/0.89  
% 1.96/0.89  --aig_mode                              false
% 1.96/0.89  
% 1.96/0.89  ------ Instantiation Options
% 1.96/0.89  
% 1.96/0.89  --instantiation_flag                    true
% 1.96/0.89  --inst_sos_flag                         false
% 1.96/0.89  --inst_sos_phase                        true
% 1.96/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/0.89  --inst_lit_sel_side                     none
% 1.96/0.89  --inst_solver_per_active                1400
% 1.96/0.89  --inst_solver_calls_frac                1.
% 1.96/0.89  --inst_passive_queue_type               priority_queues
% 1.96/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/0.89  --inst_passive_queues_freq              [25;2]
% 1.96/0.89  --inst_dismatching                      true
% 1.96/0.89  --inst_eager_unprocessed_to_passive     true
% 1.96/0.89  --inst_prop_sim_given                   true
% 1.96/0.89  --inst_prop_sim_new                     false
% 1.96/0.89  --inst_subs_new                         false
% 1.96/0.89  --inst_eq_res_simp                      false
% 1.96/0.89  --inst_subs_given                       false
% 1.96/0.89  --inst_orphan_elimination               true
% 1.96/0.89  --inst_learning_loop_flag               true
% 1.96/0.89  --inst_learning_start                   3000
% 1.96/0.89  --inst_learning_factor                  2
% 1.96/0.89  --inst_start_prop_sim_after_learn       3
% 1.96/0.89  --inst_sel_renew                        solver
% 1.96/0.89  --inst_lit_activity_flag                true
% 1.96/0.89  --inst_restr_to_given                   false
% 1.96/0.89  --inst_activity_threshold               500
% 1.96/0.89  --inst_out_proof                        true
% 1.96/0.89  
% 1.96/0.89  ------ Resolution Options
% 1.96/0.89  
% 1.96/0.89  --resolution_flag                       false
% 1.96/0.89  --res_lit_sel                           adaptive
% 1.96/0.89  --res_lit_sel_side                      none
% 1.96/0.89  --res_ordering                          kbo
% 1.96/0.89  --res_to_prop_solver                    active
% 1.96/0.89  --res_prop_simpl_new                    false
% 1.96/0.89  --res_prop_simpl_given                  true
% 1.96/0.89  --res_passive_queue_type                priority_queues
% 1.96/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/0.89  --res_passive_queues_freq               [15;5]
% 1.96/0.89  --res_forward_subs                      full
% 1.96/0.89  --res_backward_subs                     full
% 1.96/0.89  --res_forward_subs_resolution           true
% 1.96/0.89  --res_backward_subs_resolution          true
% 1.96/0.89  --res_orphan_elimination                true
% 1.96/0.89  --res_time_limit                        2.
% 1.96/0.89  --res_out_proof                         true
% 1.96/0.89  
% 1.96/0.89  ------ Superposition Options
% 1.96/0.89  
% 1.96/0.89  --superposition_flag                    true
% 1.96/0.89  --sup_passive_queue_type                priority_queues
% 1.96/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/0.89  --sup_passive_queues_freq               [8;1;4]
% 1.96/0.89  --demod_completeness_check              fast
% 1.96/0.89  --demod_use_ground                      true
% 1.96/0.89  --sup_to_prop_solver                    passive
% 1.96/0.89  --sup_prop_simpl_new                    true
% 1.96/0.89  --sup_prop_simpl_given                  true
% 1.96/0.89  --sup_fun_splitting                     false
% 1.96/0.89  --sup_smt_interval                      50000
% 1.96/0.89  
% 1.96/0.89  ------ Superposition Simplification Setup
% 1.96/0.89  
% 1.96/0.89  --sup_indices_passive                   []
% 1.96/0.89  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.89  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.89  --sup_full_bw                           [BwDemod]
% 1.96/0.89  --sup_immed_triv                        [TrivRules]
% 1.96/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.89  --sup_immed_bw_main                     []
% 1.96/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.89  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.89  
% 1.96/0.89  ------ Combination Options
% 1.96/0.89  
% 1.96/0.89  --comb_res_mult                         3
% 1.96/0.89  --comb_sup_mult                         2
% 1.96/0.89  --comb_inst_mult                        10
% 1.96/0.89  
% 1.96/0.89  ------ Debug Options
% 1.96/0.89  
% 1.96/0.89  --dbg_backtrace                         false
% 1.96/0.89  --dbg_dump_prop_clauses                 false
% 1.96/0.89  --dbg_dump_prop_clauses_file            -
% 1.96/0.89  --dbg_out_stat                          false
% 1.96/0.89  
% 1.96/0.89  
% 1.96/0.89  
% 1.96/0.89  
% 1.96/0.89  ------ Proving...
% 1.96/0.89  
% 1.96/0.89  
% 1.96/0.89  % SZS status Theorem for theBenchmark.p
% 1.96/0.89  
% 1.96/0.89   Resolution empty clause
% 1.96/0.89  
% 1.96/0.89  % SZS output start CNFRefutation for theBenchmark.p
% 1.96/0.89  
% 1.96/0.89  fof(f13,axiom,(
% 1.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f20,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.96/0.89    inference(pure_predicate_removal,[],[f13])).
% 1.96/0.89  
% 1.96/0.89  fof(f30,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.89    inference(ennf_transformation,[],[f20])).
% 1.96/0.89  
% 1.96/0.89  fof(f68,plain,(
% 1.96/0.89    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.89    inference(cnf_transformation,[],[f30])).
% 1.96/0.89  
% 1.96/0.89  fof(f8,axiom,(
% 1.96/0.89    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f23,plain,(
% 1.96/0.89    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.96/0.89    inference(ennf_transformation,[],[f8])).
% 1.96/0.89  
% 1.96/0.89  fof(f41,plain,(
% 1.96/0.89    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.96/0.89    inference(nnf_transformation,[],[f23])).
% 1.96/0.89  
% 1.96/0.89  fof(f61,plain,(
% 1.96/0.89    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f41])).
% 1.96/0.89  
% 1.96/0.89  fof(f12,axiom,(
% 1.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f29,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.89    inference(ennf_transformation,[],[f12])).
% 1.96/0.89  
% 1.96/0.89  fof(f67,plain,(
% 1.96/0.89    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.89    inference(cnf_transformation,[],[f29])).
% 1.96/0.89  
% 1.96/0.89  fof(f17,conjecture,(
% 1.96/0.89    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f18,negated_conjecture,(
% 1.96/0.89    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.96/0.89    inference(negated_conjecture,[],[f17])).
% 1.96/0.89  
% 1.96/0.89  fof(f35,plain,(
% 1.96/0.89    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.96/0.89    inference(ennf_transformation,[],[f18])).
% 1.96/0.89  
% 1.96/0.89  fof(f36,plain,(
% 1.96/0.89    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.96/0.89    inference(flattening,[],[f35])).
% 1.96/0.89  
% 1.96/0.89  fof(f48,plain,(
% 1.96/0.89    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 1.96/0.89    introduced(choice_axiom,[])).
% 1.96/0.89  
% 1.96/0.89  fof(f49,plain,(
% 1.96/0.89    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 1.96/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f48])).
% 1.96/0.89  
% 1.96/0.89  fof(f81,plain,(
% 1.96/0.89    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 1.96/0.89    inference(cnf_transformation,[],[f49])).
% 1.96/0.89  
% 1.96/0.89  fof(f3,axiom,(
% 1.96/0.89    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f52,plain,(
% 1.96/0.89    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f3])).
% 1.96/0.89  
% 1.96/0.89  fof(f4,axiom,(
% 1.96/0.89    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f53,plain,(
% 1.96/0.89    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f4])).
% 1.96/0.89  
% 1.96/0.89  fof(f5,axiom,(
% 1.96/0.89    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f54,plain,(
% 1.96/0.89    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f5])).
% 1.96/0.89  
% 1.96/0.89  fof(f84,plain,(
% 1.96/0.89    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.96/0.89    inference(definition_unfolding,[],[f53,f54])).
% 1.96/0.89  
% 1.96/0.89  fof(f85,plain,(
% 1.96/0.89    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.96/0.89    inference(definition_unfolding,[],[f52,f84])).
% 1.96/0.89  
% 1.96/0.89  fof(f94,plain,(
% 1.96/0.89    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 1.96/0.89    inference(definition_unfolding,[],[f81,f85])).
% 1.96/0.89  
% 1.96/0.89  fof(f7,axiom,(
% 1.96/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f22,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.96/0.89    inference(ennf_transformation,[],[f7])).
% 1.96/0.89  
% 1.96/0.89  fof(f39,plain,(
% 1.96/0.89    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.96/0.89    inference(nnf_transformation,[],[f22])).
% 1.96/0.89  
% 1.96/0.89  fof(f40,plain,(
% 1.96/0.89    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.96/0.89    inference(flattening,[],[f39])).
% 1.96/0.89  
% 1.96/0.89  fof(f56,plain,(
% 1.96/0.89    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.96/0.89    inference(cnf_transformation,[],[f40])).
% 1.96/0.89  
% 1.96/0.89  fof(f91,plain,(
% 1.96/0.89    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 1.96/0.89    inference(definition_unfolding,[],[f56,f84,f85,f85,f84])).
% 1.96/0.89  
% 1.96/0.89  fof(f14,axiom,(
% 1.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f31,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.89    inference(ennf_transformation,[],[f14])).
% 1.96/0.89  
% 1.96/0.89  fof(f69,plain,(
% 1.96/0.89    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.89    inference(cnf_transformation,[],[f31])).
% 1.96/0.89  
% 1.96/0.89  fof(f83,plain,(
% 1.96/0.89    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 1.96/0.89    inference(cnf_transformation,[],[f49])).
% 1.96/0.89  
% 1.96/0.89  fof(f93,plain,(
% 1.96/0.89    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)),
% 1.96/0.89    inference(definition_unfolding,[],[f83,f85,f85])).
% 1.96/0.89  
% 1.96/0.89  fof(f10,axiom,(
% 1.96/0.89    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f26,plain,(
% 1.96/0.89    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.96/0.89    inference(ennf_transformation,[],[f10])).
% 1.96/0.89  
% 1.96/0.89  fof(f27,plain,(
% 1.96/0.89    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.96/0.89    inference(flattening,[],[f26])).
% 1.96/0.89  
% 1.96/0.89  fof(f65,plain,(
% 1.96/0.89    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f27])).
% 1.96/0.89  
% 1.96/0.89  fof(f92,plain,(
% 1.96/0.89    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.96/0.89    inference(definition_unfolding,[],[f65,f85,f85])).
% 1.96/0.89  
% 1.96/0.89  fof(f79,plain,(
% 1.96/0.89    v1_funct_1(sK5)),
% 1.96/0.89    inference(cnf_transformation,[],[f49])).
% 1.96/0.89  
% 1.96/0.89  fof(f9,axiom,(
% 1.96/0.89    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f24,plain,(
% 1.96/0.89    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.96/0.89    inference(ennf_transformation,[],[f9])).
% 1.96/0.89  
% 1.96/0.89  fof(f25,plain,(
% 1.96/0.89    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.96/0.89    inference(flattening,[],[f24])).
% 1.96/0.89  
% 1.96/0.89  fof(f63,plain,(
% 1.96/0.89    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f25])).
% 1.96/0.89  
% 1.96/0.89  fof(f1,axiom,(
% 1.96/0.89    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f19,plain,(
% 1.96/0.89    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.96/0.89    inference(unused_predicate_definition_removal,[],[f1])).
% 1.96/0.89  
% 1.96/0.89  fof(f21,plain,(
% 1.96/0.89    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.96/0.89    inference(ennf_transformation,[],[f19])).
% 1.96/0.89  
% 1.96/0.89  fof(f37,plain,(
% 1.96/0.89    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.96/0.89    introduced(choice_axiom,[])).
% 1.96/0.89  
% 1.96/0.89  fof(f38,plain,(
% 1.96/0.89    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 1.96/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f37])).
% 1.96/0.89  
% 1.96/0.89  fof(f50,plain,(
% 1.96/0.89    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f38])).
% 1.96/0.89  
% 1.96/0.89  fof(f15,axiom,(
% 1.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f32,plain,(
% 1.96/0.89    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.96/0.89    inference(ennf_transformation,[],[f15])).
% 1.96/0.89  
% 1.96/0.89  fof(f42,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.96/0.89    inference(nnf_transformation,[],[f32])).
% 1.96/0.89  
% 1.96/0.89  fof(f43,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.96/0.89    inference(rectify,[],[f42])).
% 1.96/0.89  
% 1.96/0.89  fof(f45,plain,(
% 1.96/0.89    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 1.96/0.89    introduced(choice_axiom,[])).
% 1.96/0.89  
% 1.96/0.89  fof(f44,plain,(
% 1.96/0.89    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 1.96/0.89    introduced(choice_axiom,[])).
% 1.96/0.89  
% 1.96/0.89  fof(f46,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.96/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f45,f44])).
% 1.96/0.89  
% 1.96/0.89  fof(f72,plain,(
% 1.96/0.89    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.96/0.89    inference(cnf_transformation,[],[f46])).
% 1.96/0.89  
% 1.96/0.89  fof(f80,plain,(
% 1.96/0.89    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 1.96/0.89    inference(cnf_transformation,[],[f49])).
% 1.96/0.89  
% 1.96/0.89  fof(f95,plain,(
% 1.96/0.89    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 1.96/0.89    inference(definition_unfolding,[],[f80,f85])).
% 1.96/0.89  
% 1.96/0.89  fof(f16,axiom,(
% 1.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f33,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.89    inference(ennf_transformation,[],[f16])).
% 1.96/0.89  
% 1.96/0.89  fof(f34,plain,(
% 1.96/0.89    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.89    inference(flattening,[],[f33])).
% 1.96/0.89  
% 1.96/0.89  fof(f47,plain,(
% 1.96/0.89    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.89    inference(nnf_transformation,[],[f34])).
% 1.96/0.89  
% 1.96/0.89  fof(f73,plain,(
% 1.96/0.89    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.89    inference(cnf_transformation,[],[f47])).
% 1.96/0.89  
% 1.96/0.89  fof(f82,plain,(
% 1.96/0.89    k1_xboole_0 != sK4),
% 1.96/0.89    inference(cnf_transformation,[],[f49])).
% 1.96/0.89  
% 1.96/0.89  fof(f6,axiom,(
% 1.96/0.89    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f55,plain,(
% 1.96/0.89    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 1.96/0.89    inference(cnf_transformation,[],[f6])).
% 1.96/0.89  
% 1.96/0.89  fof(f86,plain,(
% 1.96/0.89    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 1.96/0.89    inference(definition_unfolding,[],[f55,f84])).
% 1.96/0.89  
% 1.96/0.89  fof(f2,axiom,(
% 1.96/0.89    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f51,plain,(
% 1.96/0.89    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f2])).
% 1.96/0.89  
% 1.96/0.89  fof(f11,axiom,(
% 1.96/0.89    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.96/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.89  
% 1.96/0.89  fof(f28,plain,(
% 1.96/0.89    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.96/0.89    inference(ennf_transformation,[],[f11])).
% 1.96/0.89  
% 1.96/0.89  fof(f66,plain,(
% 1.96/0.89    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.96/0.89    inference(cnf_transformation,[],[f28])).
% 1.96/0.89  
% 1.96/0.89  cnf(c_15,plain,
% 1.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 1.96/0.89      inference(cnf_transformation,[],[f68]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_9,plain,
% 1.96/0.89      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 1.96/0.89      inference(cnf_transformation,[],[f61]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_361,plain,
% 1.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/0.89      | r1_tarski(k1_relat_1(X0),X1)
% 1.96/0.89      | ~ v1_relat_1(X0) ),
% 1.96/0.89      inference(resolution,[status(thm)],[c_15,c_9]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_14,plain,
% 1.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.96/0.89      inference(cnf_transformation,[],[f67]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_365,plain,
% 1.96/0.89      ( r1_tarski(k1_relat_1(X0),X1)
% 1.96/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.96/0.89      inference(global_propositional_subsumption,[status(thm)],[c_361,c_14]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_366,plain,
% 1.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/0.89      | r1_tarski(k1_relat_1(X0),X1) ),
% 1.96/0.89      inference(renaming,[status(thm)],[c_365]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_28,negated_conjecture,
% 1.96/0.89      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 1.96/0.89      inference(cnf_transformation,[],[f94]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_434,plain,
% 1.96/0.89      ( r1_tarski(k1_relat_1(X0),X1)
% 1.96/0.89      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.96/0.89      | sK5 != X0 ),
% 1.96/0.89      inference(resolution_lifted,[status(thm)],[c_366,c_28]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_435,plain,
% 1.96/0.89      ( r1_tarski(k1_relat_1(sK5),X0)
% 1.96/0.89      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.96/0.89      inference(unflattening,[status(thm)],[c_434]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_1527,plain,
% 1.96/0.89      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.96/0.89      | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
% 1.96/0.89      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_1911,plain,
% 1.96/0.89      ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 1.96/0.89      inference(equality_resolution,[status(thm)],[c_1527]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_7,plain,
% 1.96/0.89      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 1.96/0.89      | k2_enumset1(X1,X1,X1,X2) = X0
% 1.96/0.89      | k2_enumset1(X2,X2,X2,X2) = X0
% 1.96/0.89      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.96/0.89      | k1_xboole_0 = X0 ),
% 1.96/0.89      inference(cnf_transformation,[],[f91]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_1532,plain,
% 1.96/0.89      ( k2_enumset1(X0,X0,X0,X1) = X2
% 1.96/0.89      | k2_enumset1(X1,X1,X1,X1) = X2
% 1.96/0.89      | k2_enumset1(X0,X0,X0,X0) = X2
% 1.96/0.89      | k1_xboole_0 = X2
% 1.96/0.89      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 1.96/0.89      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_2544,plain,
% 1.96/0.89      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
% 1.96/0.89      | k1_relat_1(sK5) = k1_xboole_0 ),
% 1.96/0.89      inference(superposition,[status(thm)],[c_1911,c_1532]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_2551,plain,
% 1.96/0.89      ( k2_enumset1(sK3,sK3,sK3,sK3) = X0
% 1.96/0.89      | k1_relat_1(sK5) = k1_xboole_0
% 1.96/0.89      | k1_xboole_0 = X0
% 1.96/0.89      | r1_tarski(X0,k1_relat_1(sK5)) != iProver_top ),
% 1.96/0.89      inference(superposition,[status(thm)],[c_2544,c_1532]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_16,plain,
% 1.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/0.89      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.96/0.89      inference(cnf_transformation,[],[f69]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_530,plain,
% 1.96/0.89      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.96/0.89      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.96/0.89      | sK5 != X2 ),
% 1.96/0.89      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_531,plain,
% 1.96/0.89      ( k2_relset_1(X0,X1,sK5) = k2_relat_1(sK5)
% 1.96/0.89      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.96/0.89      inference(unflattening,[status(thm)],[c_530]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_1694,plain,
% 1.96/0.89      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 1.96/0.89      inference(equality_resolution,[status(thm)],[c_531]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_26,negated_conjecture,
% 1.96/0.89      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 1.96/0.89      inference(cnf_transformation,[],[f93]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_1722,plain,
% 1.96/0.89      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
% 1.96/0.89      inference(demodulation,[status(thm)],[c_1694,c_26]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_12,plain,
% 1.96/0.89      ( ~ v1_funct_1(X0)
% 1.96/0.89      | ~ v1_relat_1(X0)
% 1.96/0.89      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 1.96/0.89      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 1.96/0.89      inference(cnf_transformation,[],[f92]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_30,negated_conjecture,
% 1.96/0.89      ( v1_funct_1(sK5) ),
% 1.96/0.89      inference(cnf_transformation,[],[f79]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_342,plain,
% 1.96/0.89      ( ~ v1_relat_1(X0)
% 1.96/0.89      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 1.96/0.89      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 1.96/0.89      | sK5 != X0 ),
% 1.96/0.89      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_343,plain,
% 1.96/0.89      ( ~ v1_relat_1(sK5)
% 1.96/0.89      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 1.96/0.89      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 1.96/0.89      inference(unflattening,[status(thm)],[c_342]) ).
% 1.96/0.89  
% 1.96/0.89  cnf(c_1528,plain,
% 1.96/0.89      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 1.96/0.89      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 1.96/0.89      | v1_relat_1(sK5) != iProver_top ),
% 1.96/0.89      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_344,plain,
% 1.96/0.90      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 1.96/0.90      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 1.96/0.90      | v1_relat_1(sK5) != iProver_top ),
% 1.96/0.90      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1191,plain,( X0 = X0 ),theory(equality) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1677,plain,
% 1.96/0.90      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 1.96/0.90      inference(instantiation,[status(thm)],[c_1191]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_539,plain,
% 1.96/0.90      ( v1_relat_1(X0)
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.96/0.90      | sK5 != X0 ),
% 1.96/0.90      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_540,plain,
% 1.96/0.90      ( v1_relat_1(sK5)
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.96/0.90      inference(unflattening,[status(thm)],[c_539]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1681,plain,
% 1.96/0.90      ( v1_relat_1(sK5)
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 1.96/0.90      inference(instantiation,[status(thm)],[c_540]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1682,plain,
% 1.96/0.90      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 1.96/0.90      | v1_relat_1(sK5) = iProver_top ),
% 1.96/0.90      inference(predicate_to_equality,[status(thm)],[c_1681]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1963,plain,
% 1.96/0.90      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 1.96/0.90      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
% 1.96/0.90      inference(global_propositional_subsumption,
% 1.96/0.90                [status(thm)],
% 1.96/0.90                [c_1528,c_344,c_1677,c_1682]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1964,plain,
% 1.96/0.90      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 1.96/0.90      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 1.96/0.90      inference(renaming,[status(thm)],[c_1963]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2563,plain,
% 1.96/0.90      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
% 1.96/0.90      | k1_relat_1(sK5) = k1_xboole_0 ),
% 1.96/0.90      inference(superposition,[status(thm)],[c_2544,c_1964]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2815,plain,
% 1.96/0.90      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 1.96/0.90      inference(global_propositional_subsumption,
% 1.96/0.90                [status(thm)],
% 1.96/0.90                [c_2551,c_1722,c_2563]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_11,plain,
% 1.96/0.90      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 1.96/0.90      inference(cnf_transformation,[],[f63]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1530,plain,
% 1.96/0.90      ( k1_relat_1(X0) != k1_xboole_0
% 1.96/0.90      | k1_xboole_0 = X0
% 1.96/0.90      | v1_relat_1(X0) != iProver_top ),
% 1.96/0.90      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2830,plain,
% 1.96/0.90      ( sK5 = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 1.96/0.90      inference(superposition,[status(thm)],[c_2815,c_1530]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1879,plain,
% 1.96/0.90      ( ~ v1_relat_1(sK5)
% 1.96/0.90      | k1_relat_1(sK5) != k1_xboole_0
% 1.96/0.90      | k1_xboole_0 = sK5 ),
% 1.96/0.90      inference(instantiation,[status(thm)],[c_11]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2069,plain,
% 1.96/0.90      ( sK5 = sK5 ),
% 1.96/0.90      inference(instantiation,[status(thm)],[c_1191]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1192,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2070,plain,
% 1.96/0.90      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 1.96/0.90      inference(instantiation,[status(thm)],[c_1192]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2403,plain,
% 1.96/0.90      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 1.96/0.90      inference(instantiation,[status(thm)],[c_2070]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2404,plain,
% 1.96/0.90      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 1.96/0.90      inference(instantiation,[status(thm)],[c_2403]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2833,plain,
% 1.96/0.90      ( sK5 = k1_xboole_0 ),
% 1.96/0.90      inference(global_propositional_subsumption,
% 1.96/0.90                [status(thm)],
% 1.96/0.90                [c_2830,c_1677,c_1681,c_1722,c_1879,c_2069,c_2404,c_2563]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_0,plain,
% 1.96/0.90      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.96/0.90      inference(cnf_transformation,[],[f50]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1539,plain,
% 1.96/0.90      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 1.96/0.90      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_17,plain,
% 1.96/0.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/0.90      | ~ r2_hidden(X3,X1)
% 1.96/0.90      | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
% 1.96/0.90      | k1_relset_1(X1,X2,X0) != X1 ),
% 1.96/0.90      inference(cnf_transformation,[],[f72]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_512,plain,
% 1.96/0.90      ( ~ r2_hidden(X0,X1)
% 1.96/0.90      | r2_hidden(k4_tarski(X0,sK1(X2,X0)),X2)
% 1.96/0.90      | k1_relset_1(X1,X3,X2) != X1
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X3))
% 1.96/0.90      | sK5 != X2 ),
% 1.96/0.90      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_513,plain,
% 1.96/0.90      ( ~ r2_hidden(X0,X1)
% 1.96/0.90      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5)
% 1.96/0.90      | k1_relset_1(X1,X2,sK5) != X1
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 1.96/0.90      inference(unflattening,[status(thm)],[c_512]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1524,plain,
% 1.96/0.90      ( k1_relset_1(X0,X1,sK5) != X0
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.96/0.90      | r2_hidden(X2,X0) != iProver_top
% 1.96/0.90      | r2_hidden(k4_tarski(X2,sK1(sK5,X2)),sK5) = iProver_top ),
% 1.96/0.90      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1993,plain,
% 1.96/0.90      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_enumset1(sK3,sK3,sK3,sK3)
% 1.96/0.90      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 1.96/0.90      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 1.96/0.90      inference(equality_resolution,[status(thm)],[c_1524]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_29,negated_conjecture,
% 1.96/0.90      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 1.96/0.90      inference(cnf_transformation,[],[f95]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_25,plain,
% 1.96/0.90      ( ~ v1_funct_2(X0,X1,X2)
% 1.96/0.90      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/0.90      | k1_relset_1(X1,X2,X0) = X1
% 1.96/0.90      | k1_xboole_0 = X2 ),
% 1.96/0.90      inference(cnf_transformation,[],[f73]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_446,plain,
% 1.96/0.90      ( ~ v1_funct_2(X0,X1,X2)
% 1.96/0.90      | k1_relset_1(X1,X2,X0) = X1
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.96/0.90      | sK5 != X0
% 1.96/0.90      | k1_xboole_0 = X2 ),
% 1.96/0.90      inference(resolution_lifted,[status(thm)],[c_25,c_28]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_447,plain,
% 1.96/0.90      ( ~ v1_funct_2(sK5,X0,X1)
% 1.96/0.90      | k1_relset_1(X0,X1,sK5) = X0
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.96/0.90      | k1_xboole_0 = X1 ),
% 1.96/0.90      inference(unflattening,[status(thm)],[c_446]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_845,plain,
% 1.96/0.90      ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
% 1.96/0.90      | k1_relset_1(X0,X1,sK5) = X0
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.96/0.90      | sK4 != X1
% 1.96/0.90      | sK5 != sK5
% 1.96/0.90      | k1_xboole_0 = X1 ),
% 1.96/0.90      inference(resolution_lifted,[status(thm)],[c_29,c_447]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_846,plain,
% 1.96/0.90      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 1.96/0.90      | k1_xboole_0 = sK4 ),
% 1.96/0.90      inference(unflattening,[status(thm)],[c_845]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_27,negated_conjecture,
% 1.96/0.90      ( k1_xboole_0 != sK4 ),
% 1.96/0.90      inference(cnf_transformation,[],[f82]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_847,plain,
% 1.96/0.90      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 1.96/0.90      | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.96/0.90      inference(global_propositional_subsumption,[status(thm)],[c_846,c_27]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_848,plain,
% 1.96/0.90      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 1.96/0.90      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 1.96/0.90      inference(renaming,[status(thm)],[c_847]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_914,plain,
% 1.96/0.90      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.96/0.90      inference(equality_resolution_simp,[status(thm)],[c_848]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1994,plain,
% 1.96/0.90      ( k2_enumset1(sK3,sK3,sK3,sK3) != k2_enumset1(sK3,sK3,sK3,sK3)
% 1.96/0.90      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 1.96/0.90      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 1.96/0.90      inference(light_normalisation,[status(thm)],[c_1993,c_914]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1995,plain,
% 1.96/0.90      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 1.96/0.90      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 1.96/0.90      inference(equality_resolution_simp,[status(thm)],[c_1994]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2147,plain,
% 1.96/0.90      ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),sK1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3)))),sK5) = iProver_top
% 1.96/0.90      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 1.96/0.90      inference(superposition,[status(thm)],[c_1539,c_1995]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2,plain,
% 1.96/0.90      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 1.96/0.90      inference(cnf_transformation,[],[f86]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1537,plain,
% 1.96/0.90      ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 1.96/0.90      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2311,plain,
% 1.96/0.90      ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),sK1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3)))),sK5) = iProver_top ),
% 1.96/0.90      inference(forward_subsumption_resolution,[status(thm)],[c_2147,c_1537]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_2837,plain,
% 1.96/0.90      ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),sK1(k1_xboole_0,sK0(k2_enumset1(sK3,sK3,sK3,sK3)))),k1_xboole_0) = iProver_top ),
% 1.96/0.90      inference(demodulation,[status(thm)],[c_2833,c_2311]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1,plain,
% 1.96/0.90      ( r1_tarski(k1_xboole_0,X0) ),
% 1.96/0.90      inference(cnf_transformation,[],[f51]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1538,plain,
% 1.96/0.90      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.96/0.90      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_13,plain,
% 1.96/0.90      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 1.96/0.90      inference(cnf_transformation,[],[f66]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1529,plain,
% 1.96/0.90      ( r1_tarski(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 1.96/0.90      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_1906,plain,
% 1.96/0.90      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.96/0.90      inference(superposition,[status(thm)],[c_1538,c_1529]) ).
% 1.96/0.90  
% 1.96/0.90  cnf(c_3456,plain,
% 1.96/0.90      ( $false ),
% 1.96/0.90      inference(forward_subsumption_resolution,[status(thm)],[c_2837,c_1906]) ).
% 1.96/0.90  
% 1.96/0.90  
% 1.96/0.90  % SZS output end CNFRefutation for theBenchmark.p
% 1.96/0.90  
% 1.96/0.90  ------                               Statistics
% 1.96/0.90  
% 1.96/0.90  ------ General
% 1.96/0.90  
% 1.96/0.90  abstr_ref_over_cycles:                  0
% 1.96/0.90  abstr_ref_under_cycles:                 0
% 1.96/0.90  gc_basic_clause_elim:                   0
% 1.96/0.90  forced_gc_time:                         0
% 1.96/0.90  parsing_time:                           0.008
% 1.96/0.90  unif_index_cands_time:                  0.
% 1.96/0.90  unif_index_add_time:                    0.
% 1.96/0.90  orderings_time:                         0.
% 1.96/0.90  out_proof_time:                         0.016
% 1.96/0.90  total_time:                             0.133
% 1.96/0.90  num_of_symbols:                         55
% 1.96/0.90  num_of_terms:                           2814
% 1.96/0.90  
% 1.96/0.90  ------ Preprocessing
% 1.96/0.90  
% 1.96/0.90  num_of_splits:                          0
% 1.96/0.90  num_of_split_atoms:                     0
% 1.96/0.90  num_of_reused_defs:                     0
% 1.96/0.90  num_eq_ax_congr_red:                    19
% 1.96/0.90  num_of_sem_filtered_clauses:            1
% 1.96/0.90  num_of_subtypes:                        0
% 1.96/0.90  monotx_restored_types:                  0
% 1.96/0.90  sat_num_of_epr_types:                   0
% 1.96/0.90  sat_num_of_non_cyclic_types:            0
% 1.96/0.90  sat_guarded_non_collapsed_types:        0
% 1.96/0.90  num_pure_diseq_elim:                    0
% 1.96/0.90  simp_replaced_by:                       0
% 1.96/0.90  res_preprocessed:                       135
% 1.96/0.90  prep_upred:                             0
% 1.96/0.90  prep_unflattend:                        76
% 1.96/0.90  smt_new_axioms:                         0
% 1.96/0.90  pred_elim_cands:                        4
% 1.96/0.90  pred_elim:                              4
% 1.96/0.90  pred_elim_cl:                           8
% 1.96/0.90  pred_elim_cycles:                       12
% 1.96/0.90  merged_defs:                            0
% 1.96/0.90  merged_defs_ncl:                        0
% 1.96/0.90  bin_hyper_res:                          0
% 1.96/0.90  prep_cycles:                            4
% 1.96/0.90  pred_elim_time:                         0.01
% 1.96/0.90  splitting_time:                         0.
% 1.96/0.90  sem_filter_time:                        0.
% 1.96/0.90  monotx_time:                            0.
% 1.96/0.90  subtype_inf_time:                       0.
% 1.96/0.90  
% 1.96/0.90  ------ Problem properties
% 1.96/0.90  
% 1.96/0.90  clauses:                                23
% 1.96/0.90  conjectures:                            2
% 1.96/0.90  epr:                                    3
% 1.96/0.90  horn:                                   19
% 1.96/0.90  ground:                                 5
% 1.96/0.90  unary:                                  9
% 1.96/0.90  binary:                                 5
% 1.96/0.90  lits:                                   50
% 1.96/0.90  lits_eq:                                30
% 1.96/0.90  fd_pure:                                0
% 1.96/0.90  fd_pseudo:                              0
% 1.96/0.90  fd_cond:                                2
% 1.96/0.90  fd_pseudo_cond:                         1
% 1.96/0.90  ac_symbols:                             0
% 1.96/0.90  
% 1.96/0.90  ------ Propositional Solver
% 1.96/0.90  
% 1.96/0.90  prop_solver_calls:                      28
% 1.96/0.90  prop_fast_solver_calls:                 912
% 1.96/0.90  smt_solver_calls:                       0
% 1.96/0.90  smt_fast_solver_calls:                  0
% 1.96/0.90  prop_num_of_clauses:                    1025
% 1.96/0.90  prop_preprocess_simplified:             4854
% 1.96/0.90  prop_fo_subsumed:                       27
% 1.96/0.90  prop_solver_time:                       0.
% 1.96/0.90  smt_solver_time:                        0.
% 1.96/0.90  smt_fast_solver_time:                   0.
% 1.96/0.90  prop_fast_solver_time:                  0.
% 1.96/0.90  prop_unsat_core_time:                   0.
% 1.96/0.90  
% 1.96/0.90  ------ QBF
% 1.96/0.90  
% 1.96/0.90  qbf_q_res:                              0
% 1.96/0.90  qbf_num_tautologies:                    0
% 1.96/0.90  qbf_prep_cycles:                        0
% 1.96/0.90  
% 1.96/0.90  ------ BMC1
% 1.96/0.90  
% 1.96/0.90  bmc1_current_bound:                     -1
% 1.96/0.90  bmc1_last_solved_bound:                 -1
% 1.96/0.90  bmc1_unsat_core_size:                   -1
% 1.96/0.90  bmc1_unsat_core_parents_size:           -1
% 1.96/0.90  bmc1_merge_next_fun:                    0
% 1.96/0.90  bmc1_unsat_core_clauses_time:           0.
% 1.96/0.90  
% 1.96/0.90  ------ Instantiation
% 1.96/0.90  
% 1.96/0.90  inst_num_of_clauses:                    363
% 1.96/0.90  inst_num_in_passive:                    141
% 1.96/0.90  inst_num_in_active:                     206
% 1.96/0.90  inst_num_in_unprocessed:                16
% 1.96/0.90  inst_num_of_loops:                      230
% 1.96/0.90  inst_num_of_learning_restarts:          0
% 1.96/0.90  inst_num_moves_active_passive:          21
% 1.96/0.90  inst_lit_activity:                      0
% 1.96/0.90  inst_lit_activity_moves:                0
% 1.96/0.90  inst_num_tautologies:                   0
% 1.96/0.90  inst_num_prop_implied:                  0
% 1.96/0.90  inst_num_existing_simplified:           0
% 1.96/0.90  inst_num_eq_res_simplified:             0
% 1.96/0.90  inst_num_child_elim:                    0
% 1.96/0.90  inst_num_of_dismatching_blockings:      46
% 1.96/0.90  inst_num_of_non_proper_insts:           285
% 1.96/0.90  inst_num_of_duplicates:                 0
% 1.96/0.90  inst_inst_num_from_inst_to_res:         0
% 1.96/0.90  inst_dismatching_checking_time:         0.
% 1.96/0.90  
% 1.96/0.90  ------ Resolution
% 1.96/0.90  
% 1.96/0.90  res_num_of_clauses:                     0
% 1.96/0.90  res_num_in_passive:                     0
% 1.96/0.90  res_num_in_active:                      0
% 1.96/0.90  res_num_of_loops:                       139
% 1.96/0.90  res_forward_subset_subsumed:            66
% 1.96/0.90  res_backward_subset_subsumed:           4
% 1.96/0.90  res_forward_subsumed:                   2
% 1.96/0.90  res_backward_subsumed:                  0
% 1.96/0.90  res_forward_subsumption_resolution:     0
% 1.96/0.90  res_backward_subsumption_resolution:    0
% 1.96/0.90  res_clause_to_clause_subsumption:       109
% 1.96/0.90  res_orphan_elimination:                 0
% 1.96/0.90  res_tautology_del:                      59
% 1.96/0.90  res_num_eq_res_simplified:              1
% 1.96/0.90  res_num_sel_changes:                    0
% 1.96/0.90  res_moves_from_active_to_pass:          0
% 1.96/0.90  
% 1.96/0.90  ------ Superposition
% 1.96/0.90  
% 1.96/0.90  sup_time_total:                         0.
% 1.96/0.90  sup_time_generating:                    0.
% 1.96/0.90  sup_time_sim_full:                      0.
% 1.96/0.90  sup_time_sim_immed:                     0.
% 1.96/0.90  
% 1.96/0.90  sup_num_of_clauses:                     31
% 1.96/0.90  sup_num_in_active:                      27
% 1.96/0.90  sup_num_in_passive:                     4
% 1.96/0.90  sup_num_of_loops:                       45
% 1.96/0.90  sup_fw_superposition:                   8
% 1.96/0.90  sup_bw_superposition:                   33
% 1.96/0.90  sup_immediate_simplified:               9
% 1.96/0.90  sup_given_eliminated:                   0
% 1.96/0.90  comparisons_done:                       0
% 1.96/0.90  comparisons_avoided:                    0
% 1.96/0.90  
% 1.96/0.90  ------ Simplifications
% 1.96/0.90  
% 1.96/0.90  
% 1.96/0.90  sim_fw_subset_subsumed:                 4
% 1.96/0.90  sim_bw_subset_subsumed:                 12
% 1.96/0.90  sim_fw_subsumed:                        4
% 1.96/0.90  sim_bw_subsumed:                        0
% 1.96/0.90  sim_fw_subsumption_res:                 3
% 1.96/0.90  sim_bw_subsumption_res:                 0
% 1.96/0.90  sim_tautology_del:                      0
% 1.96/0.90  sim_eq_tautology_del:                   5
% 1.96/0.90  sim_eq_res_simp:                        2
% 1.96/0.90  sim_fw_demodulated:                     0
% 1.96/0.90  sim_bw_demodulated:                     18
% 1.96/0.90  sim_light_normalised:                   3
% 1.96/0.90  sim_joinable_taut:                      0
% 1.96/0.90  sim_joinable_simp:                      0
% 1.96/0.90  sim_ac_normalised:                      0
% 1.96/0.90  sim_smt_subsumption:                    0
% 1.96/0.90  
%------------------------------------------------------------------------------
