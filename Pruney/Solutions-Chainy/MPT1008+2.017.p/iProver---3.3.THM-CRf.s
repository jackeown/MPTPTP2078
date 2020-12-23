%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:07 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  156 (2551 expanded)
%              Number of clauses        :   76 ( 498 expanded)
%              Number of leaves         :   23 ( 671 expanded)
%              Depth                    :   22
%              Number of atoms          :  468 (6364 expanded)
%              Number of equality atoms :  249 (3501 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f40,plain,(
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

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,
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

fof(f56,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f39,f55])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f98,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f97])).

fof(f106,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f94,f98])).

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

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f67,f97,f98,f98,f97])).

fof(f96,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f105,plain,(
    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f96,f98,f98])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f78,f98,f98])).

fof(f92,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f76,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f93,f98])).

fof(f95,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f52,f51])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1246,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1226,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_15])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_407,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_20])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_407])).

cnf(c_1224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_1521,plain,
    ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1224])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1237,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k2_enumset1(X0,X0,X0,X2) = X1
    | k2_enumset1(X2,X2,X2,X2) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3151,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1521,c_1237])).

cnf(c_3308,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_1226])).

cnf(c_32,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1467,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_765,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1460,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_1544,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_384,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_385,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_1225,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_386,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_1440,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1441,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1440])).

cnf(c_1475,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1225,c_39,c_386,c_1441])).

cnf(c_1476,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_1475])).

cnf(c_3299,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3151,c_1476])).

cnf(c_3648,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3308,c_34,c_32,c_1467,c_1544,c_3299])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1233,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3666,plain,
    ( sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3648,c_1233])).

cnf(c_1561,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_764,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1574,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_1888,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_3123,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1888])).

cnf(c_3124,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3123])).

cnf(c_3671,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3666,c_34,c_32,c_1440,c_1467,c_1544,c_1561,c_1574,c_3124,c_3299])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_522,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_524,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_34,c_33])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1229,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2992,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_524,c_1229])).

cnf(c_3282,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2992,c_39])).

cnf(c_3675,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3671,c_3282])).

cnf(c_4158,plain,
    ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3),X0),sK1(k1_xboole_0,sK0(k2_enumset1(sK3,sK3,sK3,sK3),X0))),k1_xboole_0) = iProver_top
    | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_3675])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1232,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4383,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3),X0),sK1(k1_xboole_0,sK0(k2_enumset1(sK3,sK3,sK3,sK3),X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4158,c_1232])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1242,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4614,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4383,c_1242])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1244,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2282,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
    | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_1244])).

cnf(c_3652,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3648,c_2282])).

cnf(c_4623,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4614,c_3652])).

cnf(c_3654,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_3648,c_1476])).

cnf(c_4174,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3654,c_3671])).

cnf(c_4654,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4623,c_4174])).

cnf(c_1230,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2267,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1226,c_1230])).

cnf(c_2423,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2267,c_32])).

cnf(c_3677,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3671,c_2423])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4654,c_3677])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.13/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/1.00  
% 3.13/1.00  ------  iProver source info
% 3.13/1.00  
% 3.13/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.13/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/1.00  git: non_committed_changes: false
% 3.13/1.00  git: last_make_outside_of_git: false
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options
% 3.13/1.00  
% 3.13/1.00  --out_options                           all
% 3.13/1.00  --tptp_safe_out                         true
% 3.13/1.00  --problem_path                          ""
% 3.13/1.00  --include_path                          ""
% 3.13/1.00  --clausifier                            res/vclausify_rel
% 3.13/1.00  --clausifier_options                    --mode clausify
% 3.13/1.00  --stdin                                 false
% 3.13/1.00  --stats_out                             all
% 3.13/1.00  
% 3.13/1.00  ------ General Options
% 3.13/1.00  
% 3.13/1.00  --fof                                   false
% 3.13/1.00  --time_out_real                         305.
% 3.13/1.00  --time_out_virtual                      -1.
% 3.13/1.00  --symbol_type_check                     false
% 3.13/1.00  --clausify_out                          false
% 3.13/1.00  --sig_cnt_out                           false
% 3.13/1.00  --trig_cnt_out                          false
% 3.13/1.00  --trig_cnt_out_tolerance                1.
% 3.13/1.00  --trig_cnt_out_sk_spl                   false
% 3.13/1.00  --abstr_cl_out                          false
% 3.13/1.00  
% 3.13/1.00  ------ Global Options
% 3.13/1.00  
% 3.13/1.00  --schedule                              default
% 3.13/1.00  --add_important_lit                     false
% 3.13/1.00  --prop_solver_per_cl                    1000
% 3.13/1.00  --min_unsat_core                        false
% 3.13/1.00  --soft_assumptions                      false
% 3.13/1.00  --soft_lemma_size                       3
% 3.13/1.00  --prop_impl_unit_size                   0
% 3.13/1.00  --prop_impl_unit                        []
% 3.13/1.00  --share_sel_clauses                     true
% 3.13/1.00  --reset_solvers                         false
% 3.13/1.00  --bc_imp_inh                            [conj_cone]
% 3.13/1.00  --conj_cone_tolerance                   3.
% 3.13/1.00  --extra_neg_conj                        none
% 3.13/1.00  --large_theory_mode                     true
% 3.13/1.00  --prolific_symb_bound                   200
% 3.13/1.00  --lt_threshold                          2000
% 3.13/1.00  --clause_weak_htbl                      true
% 3.13/1.00  --gc_record_bc_elim                     false
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing Options
% 3.13/1.00  
% 3.13/1.00  --preprocessing_flag                    true
% 3.13/1.00  --time_out_prep_mult                    0.1
% 3.13/1.00  --splitting_mode                        input
% 3.13/1.00  --splitting_grd                         true
% 3.13/1.00  --splitting_cvd                         false
% 3.13/1.00  --splitting_cvd_svl                     false
% 3.13/1.00  --splitting_nvd                         32
% 3.13/1.00  --sub_typing                            true
% 3.13/1.00  --prep_gs_sim                           true
% 3.13/1.00  --prep_unflatten                        true
% 3.13/1.00  --prep_res_sim                          true
% 3.13/1.00  --prep_upred                            true
% 3.13/1.00  --prep_sem_filter                       exhaustive
% 3.13/1.00  --prep_sem_filter_out                   false
% 3.13/1.00  --pred_elim                             true
% 3.13/1.00  --res_sim_input                         true
% 3.13/1.00  --eq_ax_congr_red                       true
% 3.13/1.00  --pure_diseq_elim                       true
% 3.13/1.00  --brand_transform                       false
% 3.13/1.00  --non_eq_to_eq                          false
% 3.13/1.00  --prep_def_merge                        true
% 3.13/1.00  --prep_def_merge_prop_impl              false
% 3.13/1.00  --prep_def_merge_mbd                    true
% 3.13/1.00  --prep_def_merge_tr_red                 false
% 3.13/1.00  --prep_def_merge_tr_cl                  false
% 3.13/1.00  --smt_preprocessing                     true
% 3.13/1.00  --smt_ac_axioms                         fast
% 3.13/1.00  --preprocessed_out                      false
% 3.13/1.00  --preprocessed_stats                    false
% 3.13/1.00  
% 3.13/1.00  ------ Abstraction refinement Options
% 3.13/1.00  
% 3.13/1.00  --abstr_ref                             []
% 3.13/1.00  --abstr_ref_prep                        false
% 3.13/1.00  --abstr_ref_until_sat                   false
% 3.13/1.00  --abstr_ref_sig_restrict                funpre
% 3.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.00  --abstr_ref_under                       []
% 3.13/1.00  
% 3.13/1.00  ------ SAT Options
% 3.13/1.00  
% 3.13/1.00  --sat_mode                              false
% 3.13/1.00  --sat_fm_restart_options                ""
% 3.13/1.00  --sat_gr_def                            false
% 3.13/1.00  --sat_epr_types                         true
% 3.13/1.00  --sat_non_cyclic_types                  false
% 3.13/1.00  --sat_finite_models                     false
% 3.13/1.00  --sat_fm_lemmas                         false
% 3.13/1.00  --sat_fm_prep                           false
% 3.13/1.00  --sat_fm_uc_incr                        true
% 3.13/1.00  --sat_out_model                         small
% 3.13/1.00  --sat_out_clauses                       false
% 3.13/1.00  
% 3.13/1.00  ------ QBF Options
% 3.13/1.00  
% 3.13/1.00  --qbf_mode                              false
% 3.13/1.00  --qbf_elim_univ                         false
% 3.13/1.00  --qbf_dom_inst                          none
% 3.13/1.00  --qbf_dom_pre_inst                      false
% 3.13/1.00  --qbf_sk_in                             false
% 3.13/1.00  --qbf_pred_elim                         true
% 3.13/1.00  --qbf_split                             512
% 3.13/1.00  
% 3.13/1.00  ------ BMC1 Options
% 3.13/1.00  
% 3.13/1.00  --bmc1_incremental                      false
% 3.13/1.00  --bmc1_axioms                           reachable_all
% 3.13/1.00  --bmc1_min_bound                        0
% 3.13/1.00  --bmc1_max_bound                        -1
% 3.13/1.00  --bmc1_max_bound_default                -1
% 3.13/1.00  --bmc1_symbol_reachability              true
% 3.13/1.00  --bmc1_property_lemmas                  false
% 3.13/1.00  --bmc1_k_induction                      false
% 3.13/1.00  --bmc1_non_equiv_states                 false
% 3.13/1.00  --bmc1_deadlock                         false
% 3.13/1.00  --bmc1_ucm                              false
% 3.13/1.00  --bmc1_add_unsat_core                   none
% 3.13/1.00  --bmc1_unsat_core_children              false
% 3.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.00  --bmc1_out_stat                         full
% 3.13/1.00  --bmc1_ground_init                      false
% 3.13/1.00  --bmc1_pre_inst_next_state              false
% 3.13/1.00  --bmc1_pre_inst_state                   false
% 3.13/1.00  --bmc1_pre_inst_reach_state             false
% 3.13/1.00  --bmc1_out_unsat_core                   false
% 3.13/1.00  --bmc1_aig_witness_out                  false
% 3.13/1.00  --bmc1_verbose                          false
% 3.13/1.00  --bmc1_dump_clauses_tptp                false
% 3.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.00  --bmc1_dump_file                        -
% 3.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.00  --bmc1_ucm_extend_mode                  1
% 3.13/1.00  --bmc1_ucm_init_mode                    2
% 3.13/1.00  --bmc1_ucm_cone_mode                    none
% 3.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.00  --bmc1_ucm_relax_model                  4
% 3.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.00  --bmc1_ucm_layered_model                none
% 3.13/1.00  --bmc1_ucm_max_lemma_size               10
% 3.13/1.00  
% 3.13/1.00  ------ AIG Options
% 3.13/1.00  
% 3.13/1.00  --aig_mode                              false
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation Options
% 3.13/1.00  
% 3.13/1.00  --instantiation_flag                    true
% 3.13/1.00  --inst_sos_flag                         false
% 3.13/1.00  --inst_sos_phase                        true
% 3.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel_side                     num_symb
% 3.13/1.00  --inst_solver_per_active                1400
% 3.13/1.00  --inst_solver_calls_frac                1.
% 3.13/1.00  --inst_passive_queue_type               priority_queues
% 3.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.00  --inst_passive_queues_freq              [25;2]
% 3.13/1.00  --inst_dismatching                      true
% 3.13/1.00  --inst_eager_unprocessed_to_passive     true
% 3.13/1.00  --inst_prop_sim_given                   true
% 3.13/1.00  --inst_prop_sim_new                     false
% 3.13/1.00  --inst_subs_new                         false
% 3.13/1.00  --inst_eq_res_simp                      false
% 3.13/1.00  --inst_subs_given                       false
% 3.13/1.00  --inst_orphan_elimination               true
% 3.13/1.00  --inst_learning_loop_flag               true
% 3.13/1.00  --inst_learning_start                   3000
% 3.13/1.00  --inst_learning_factor                  2
% 3.13/1.00  --inst_start_prop_sim_after_learn       3
% 3.13/1.00  --inst_sel_renew                        solver
% 3.13/1.00  --inst_lit_activity_flag                true
% 3.13/1.00  --inst_restr_to_given                   false
% 3.13/1.00  --inst_activity_threshold               500
% 3.13/1.00  --inst_out_proof                        true
% 3.13/1.00  
% 3.13/1.00  ------ Resolution Options
% 3.13/1.00  
% 3.13/1.00  --resolution_flag                       true
% 3.13/1.00  --res_lit_sel                           adaptive
% 3.13/1.00  --res_lit_sel_side                      none
% 3.13/1.00  --res_ordering                          kbo
% 3.13/1.00  --res_to_prop_solver                    active
% 3.13/1.00  --res_prop_simpl_new                    false
% 3.13/1.00  --res_prop_simpl_given                  true
% 3.13/1.00  --res_passive_queue_type                priority_queues
% 3.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.00  --res_passive_queues_freq               [15;5]
% 3.13/1.00  --res_forward_subs                      full
% 3.13/1.00  --res_backward_subs                     full
% 3.13/1.00  --res_forward_subs_resolution           true
% 3.13/1.00  --res_backward_subs_resolution          true
% 3.13/1.00  --res_orphan_elimination                true
% 3.13/1.00  --res_time_limit                        2.
% 3.13/1.00  --res_out_proof                         true
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Options
% 3.13/1.00  
% 3.13/1.00  --superposition_flag                    true
% 3.13/1.00  --sup_passive_queue_type                priority_queues
% 3.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.00  --demod_completeness_check              fast
% 3.13/1.00  --demod_use_ground                      true
% 3.13/1.00  --sup_to_prop_solver                    passive
% 3.13/1.00  --sup_prop_simpl_new                    true
% 3.13/1.00  --sup_prop_simpl_given                  true
% 3.13/1.00  --sup_fun_splitting                     false
% 3.13/1.00  --sup_smt_interval                      50000
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Simplification Setup
% 3.13/1.00  
% 3.13/1.00  --sup_indices_passive                   []
% 3.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_full_bw                           [BwDemod]
% 3.13/1.00  --sup_immed_triv                        [TrivRules]
% 3.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_immed_bw_main                     []
% 3.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  
% 3.13/1.00  ------ Combination Options
% 3.13/1.00  
% 3.13/1.00  --comb_res_mult                         3
% 3.13/1.00  --comb_sup_mult                         2
% 3.13/1.00  --comb_inst_mult                        10
% 3.13/1.00  
% 3.13/1.00  ------ Debug Options
% 3.13/1.00  
% 3.13/1.00  --dbg_backtrace                         false
% 3.13/1.00  --dbg_dump_prop_clauses                 false
% 3.13/1.00  --dbg_dump_prop_clauses_file            -
% 3.13/1.00  --dbg_out_stat                          false
% 3.13/1.00  ------ Parsing...
% 3.13/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/1.00  ------ Proving...
% 3.13/1.00  ------ Problem Properties 
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  clauses                                 29
% 3.13/1.00  conjectures                             3
% 3.13/1.00  EPR                                     6
% 3.13/1.00  Horn                                    25
% 3.13/1.00  unary                                   11
% 3.13/1.00  binary                                  6
% 3.13/1.00  lits                                    63
% 3.13/1.00  lits eq                                 23
% 3.13/1.00  fd_pure                                 0
% 3.13/1.00  fd_pseudo                               0
% 3.13/1.00  fd_cond                                 2
% 3.13/1.00  fd_pseudo_cond                          2
% 3.13/1.00  AC symbols                              0
% 3.13/1.00  
% 3.13/1.00  ------ Schedule dynamic 5 is on 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  Current options:
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options
% 3.13/1.00  
% 3.13/1.00  --out_options                           all
% 3.13/1.00  --tptp_safe_out                         true
% 3.13/1.00  --problem_path                          ""
% 3.13/1.00  --include_path                          ""
% 3.13/1.00  --clausifier                            res/vclausify_rel
% 3.13/1.00  --clausifier_options                    --mode clausify
% 3.13/1.00  --stdin                                 false
% 3.13/1.00  --stats_out                             all
% 3.13/1.00  
% 3.13/1.00  ------ General Options
% 3.13/1.00  
% 3.13/1.00  --fof                                   false
% 3.13/1.00  --time_out_real                         305.
% 3.13/1.00  --time_out_virtual                      -1.
% 3.13/1.00  --symbol_type_check                     false
% 3.13/1.00  --clausify_out                          false
% 3.13/1.00  --sig_cnt_out                           false
% 3.13/1.00  --trig_cnt_out                          false
% 3.13/1.00  --trig_cnt_out_tolerance                1.
% 3.13/1.00  --trig_cnt_out_sk_spl                   false
% 3.13/1.00  --abstr_cl_out                          false
% 3.13/1.00  
% 3.13/1.00  ------ Global Options
% 3.13/1.00  
% 3.13/1.00  --schedule                              default
% 3.13/1.00  --add_important_lit                     false
% 3.13/1.00  --prop_solver_per_cl                    1000
% 3.13/1.00  --min_unsat_core                        false
% 3.13/1.00  --soft_assumptions                      false
% 3.13/1.00  --soft_lemma_size                       3
% 3.13/1.00  --prop_impl_unit_size                   0
% 3.13/1.00  --prop_impl_unit                        []
% 3.13/1.00  --share_sel_clauses                     true
% 3.13/1.00  --reset_solvers                         false
% 3.13/1.00  --bc_imp_inh                            [conj_cone]
% 3.13/1.00  --conj_cone_tolerance                   3.
% 3.13/1.00  --extra_neg_conj                        none
% 3.13/1.00  --large_theory_mode                     true
% 3.13/1.00  --prolific_symb_bound                   200
% 3.13/1.00  --lt_threshold                          2000
% 3.13/1.00  --clause_weak_htbl                      true
% 3.13/1.00  --gc_record_bc_elim                     false
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing Options
% 3.13/1.00  
% 3.13/1.00  --preprocessing_flag                    true
% 3.13/1.00  --time_out_prep_mult                    0.1
% 3.13/1.00  --splitting_mode                        input
% 3.13/1.00  --splitting_grd                         true
% 3.13/1.00  --splitting_cvd                         false
% 3.13/1.00  --splitting_cvd_svl                     false
% 3.13/1.00  --splitting_nvd                         32
% 3.13/1.00  --sub_typing                            true
% 3.13/1.00  --prep_gs_sim                           true
% 3.13/1.00  --prep_unflatten                        true
% 3.13/1.00  --prep_res_sim                          true
% 3.13/1.00  --prep_upred                            true
% 3.13/1.00  --prep_sem_filter                       exhaustive
% 3.13/1.00  --prep_sem_filter_out                   false
% 3.13/1.00  --pred_elim                             true
% 3.13/1.00  --res_sim_input                         true
% 3.13/1.00  --eq_ax_congr_red                       true
% 3.13/1.00  --pure_diseq_elim                       true
% 3.13/1.00  --brand_transform                       false
% 3.13/1.00  --non_eq_to_eq                          false
% 3.13/1.00  --prep_def_merge                        true
% 3.13/1.00  --prep_def_merge_prop_impl              false
% 3.13/1.00  --prep_def_merge_mbd                    true
% 3.13/1.00  --prep_def_merge_tr_red                 false
% 3.13/1.00  --prep_def_merge_tr_cl                  false
% 3.13/1.00  --smt_preprocessing                     true
% 3.13/1.00  --smt_ac_axioms                         fast
% 3.13/1.00  --preprocessed_out                      false
% 3.13/1.00  --preprocessed_stats                    false
% 3.13/1.00  
% 3.13/1.00  ------ Abstraction refinement Options
% 3.13/1.00  
% 3.13/1.00  --abstr_ref                             []
% 3.13/1.00  --abstr_ref_prep                        false
% 3.13/1.00  --abstr_ref_until_sat                   false
% 3.13/1.00  --abstr_ref_sig_restrict                funpre
% 3.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.00  --abstr_ref_under                       []
% 3.13/1.00  
% 3.13/1.00  ------ SAT Options
% 3.13/1.00  
% 3.13/1.00  --sat_mode                              false
% 3.13/1.00  --sat_fm_restart_options                ""
% 3.13/1.00  --sat_gr_def                            false
% 3.13/1.00  --sat_epr_types                         true
% 3.13/1.00  --sat_non_cyclic_types                  false
% 3.13/1.00  --sat_finite_models                     false
% 3.13/1.00  --sat_fm_lemmas                         false
% 3.13/1.00  --sat_fm_prep                           false
% 3.13/1.00  --sat_fm_uc_incr                        true
% 3.13/1.00  --sat_out_model                         small
% 3.13/1.00  --sat_out_clauses                       false
% 3.13/1.00  
% 3.13/1.00  ------ QBF Options
% 3.13/1.00  
% 3.13/1.00  --qbf_mode                              false
% 3.13/1.00  --qbf_elim_univ                         false
% 3.13/1.00  --qbf_dom_inst                          none
% 3.13/1.00  --qbf_dom_pre_inst                      false
% 3.13/1.00  --qbf_sk_in                             false
% 3.13/1.00  --qbf_pred_elim                         true
% 3.13/1.00  --qbf_split                             512
% 3.13/1.00  
% 3.13/1.00  ------ BMC1 Options
% 3.13/1.00  
% 3.13/1.00  --bmc1_incremental                      false
% 3.13/1.00  --bmc1_axioms                           reachable_all
% 3.13/1.00  --bmc1_min_bound                        0
% 3.13/1.00  --bmc1_max_bound                        -1
% 3.13/1.00  --bmc1_max_bound_default                -1
% 3.13/1.00  --bmc1_symbol_reachability              true
% 3.13/1.00  --bmc1_property_lemmas                  false
% 3.13/1.00  --bmc1_k_induction                      false
% 3.13/1.00  --bmc1_non_equiv_states                 false
% 3.13/1.00  --bmc1_deadlock                         false
% 3.13/1.00  --bmc1_ucm                              false
% 3.13/1.00  --bmc1_add_unsat_core                   none
% 3.13/1.00  --bmc1_unsat_core_children              false
% 3.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.00  --bmc1_out_stat                         full
% 3.13/1.00  --bmc1_ground_init                      false
% 3.13/1.00  --bmc1_pre_inst_next_state              false
% 3.13/1.00  --bmc1_pre_inst_state                   false
% 3.13/1.00  --bmc1_pre_inst_reach_state             false
% 3.13/1.00  --bmc1_out_unsat_core                   false
% 3.13/1.00  --bmc1_aig_witness_out                  false
% 3.13/1.00  --bmc1_verbose                          false
% 3.13/1.00  --bmc1_dump_clauses_tptp                false
% 3.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.00  --bmc1_dump_file                        -
% 3.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.00  --bmc1_ucm_extend_mode                  1
% 3.13/1.00  --bmc1_ucm_init_mode                    2
% 3.13/1.00  --bmc1_ucm_cone_mode                    none
% 3.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.00  --bmc1_ucm_relax_model                  4
% 3.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.00  --bmc1_ucm_layered_model                none
% 3.13/1.00  --bmc1_ucm_max_lemma_size               10
% 3.13/1.00  
% 3.13/1.00  ------ AIG Options
% 3.13/1.00  
% 3.13/1.00  --aig_mode                              false
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation Options
% 3.13/1.00  
% 3.13/1.00  --instantiation_flag                    true
% 3.13/1.00  --inst_sos_flag                         false
% 3.13/1.00  --inst_sos_phase                        true
% 3.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel_side                     none
% 3.13/1.00  --inst_solver_per_active                1400
% 3.13/1.00  --inst_solver_calls_frac                1.
% 3.13/1.00  --inst_passive_queue_type               priority_queues
% 3.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.00  --inst_passive_queues_freq              [25;2]
% 3.13/1.00  --inst_dismatching                      true
% 3.13/1.00  --inst_eager_unprocessed_to_passive     true
% 3.13/1.00  --inst_prop_sim_given                   true
% 3.13/1.00  --inst_prop_sim_new                     false
% 3.13/1.00  --inst_subs_new                         false
% 3.13/1.00  --inst_eq_res_simp                      false
% 3.13/1.00  --inst_subs_given                       false
% 3.13/1.00  --inst_orphan_elimination               true
% 3.13/1.00  --inst_learning_loop_flag               true
% 3.13/1.00  --inst_learning_start                   3000
% 3.13/1.00  --inst_learning_factor                  2
% 3.13/1.00  --inst_start_prop_sim_after_learn       3
% 3.13/1.00  --inst_sel_renew                        solver
% 3.13/1.00  --inst_lit_activity_flag                true
% 3.13/1.00  --inst_restr_to_given                   false
% 3.13/1.00  --inst_activity_threshold               500
% 3.13/1.00  --inst_out_proof                        true
% 3.13/1.00  
% 3.13/1.00  ------ Resolution Options
% 3.13/1.00  
% 3.13/1.00  --resolution_flag                       false
% 3.13/1.00  --res_lit_sel                           adaptive
% 3.13/1.00  --res_lit_sel_side                      none
% 3.13/1.00  --res_ordering                          kbo
% 3.13/1.00  --res_to_prop_solver                    active
% 3.13/1.00  --res_prop_simpl_new                    false
% 3.13/1.00  --res_prop_simpl_given                  true
% 3.13/1.00  --res_passive_queue_type                priority_queues
% 3.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.00  --res_passive_queues_freq               [15;5]
% 3.13/1.00  --res_forward_subs                      full
% 3.13/1.00  --res_backward_subs                     full
% 3.13/1.00  --res_forward_subs_resolution           true
% 3.13/1.00  --res_backward_subs_resolution          true
% 3.13/1.00  --res_orphan_elimination                true
% 3.13/1.00  --res_time_limit                        2.
% 3.13/1.00  --res_out_proof                         true
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Options
% 3.13/1.00  
% 3.13/1.00  --superposition_flag                    true
% 3.13/1.00  --sup_passive_queue_type                priority_queues
% 3.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.00  --demod_completeness_check              fast
% 3.13/1.00  --demod_use_ground                      true
% 3.13/1.00  --sup_to_prop_solver                    passive
% 3.13/1.00  --sup_prop_simpl_new                    true
% 3.13/1.00  --sup_prop_simpl_given                  true
% 3.13/1.00  --sup_fun_splitting                     false
% 3.13/1.00  --sup_smt_interval                      50000
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Simplification Setup
% 3.13/1.00  
% 3.13/1.00  --sup_indices_passive                   []
% 3.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_full_bw                           [BwDemod]
% 3.13/1.00  --sup_immed_triv                        [TrivRules]
% 3.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_immed_bw_main                     []
% 3.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  
% 3.13/1.00  ------ Combination Options
% 3.13/1.00  
% 3.13/1.00  --comb_res_mult                         3
% 3.13/1.00  --comb_sup_mult                         2
% 3.13/1.00  --comb_inst_mult                        10
% 3.13/1.00  
% 3.13/1.00  ------ Debug Options
% 3.13/1.00  
% 3.13/1.00  --dbg_backtrace                         false
% 3.13/1.00  --dbg_dump_prop_clauses                 false
% 3.13/1.00  --dbg_dump_prop_clauses_file            -
% 3.13/1.00  --dbg_out_stat                          false
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ Proving...
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS status Theorem for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  fof(f1,axiom,(
% 3.13/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f22,plain,(
% 3.13/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.13/1.00    inference(ennf_transformation,[],[f1])).
% 3.13/1.00  
% 3.13/1.00  fof(f40,plain,(
% 3.13/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/1.00    inference(nnf_transformation,[],[f22])).
% 3.13/1.00  
% 3.13/1.00  fof(f41,plain,(
% 3.13/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/1.00    inference(rectify,[],[f40])).
% 3.13/1.00  
% 3.13/1.00  fof(f42,plain,(
% 3.13/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f43,plain,(
% 3.13/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.13/1.00  
% 3.13/1.00  fof(f58,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f43])).
% 3.13/1.00  
% 3.13/1.00  fof(f19,conjecture,(
% 3.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f20,negated_conjecture,(
% 3.13/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.13/1.00    inference(negated_conjecture,[],[f19])).
% 3.13/1.00  
% 3.13/1.00  fof(f38,plain,(
% 3.13/1.00    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.13/1.00    inference(ennf_transformation,[],[f20])).
% 3.13/1.00  
% 3.13/1.00  fof(f39,plain,(
% 3.13/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.13/1.00    inference(flattening,[],[f38])).
% 3.13/1.00  
% 3.13/1.00  fof(f55,plain,(
% 3.13/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f56,plain,(
% 3.13/1.00    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f39,f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f94,plain,(
% 3.13/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 3.13/1.00    inference(cnf_transformation,[],[f56])).
% 3.13/1.00  
% 3.13/1.00  fof(f4,axiom,(
% 3.13/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f64,plain,(
% 3.13/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f4])).
% 3.13/1.00  
% 3.13/1.00  fof(f5,axiom,(
% 3.13/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f65,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f5])).
% 3.13/1.00  
% 3.13/1.00  fof(f6,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f66,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f6])).
% 3.13/1.00  
% 3.13/1.00  fof(f97,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.13/1.00    inference(definition_unfolding,[],[f65,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f98,plain,(
% 3.13/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.13/1.00    inference(definition_unfolding,[],[f64,f97])).
% 3.13/1.00  
% 3.13/1.00  fof(f106,plain,(
% 3.13/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 3.13/1.00    inference(definition_unfolding,[],[f94,f98])).
% 3.13/1.00  
% 3.13/1.00  fof(f15,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f21,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.13/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.13/1.00  
% 3.13/1.00  fof(f33,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f21])).
% 3.13/1.00  
% 3.13/1.00  fof(f81,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f33])).
% 3.13/1.00  
% 3.13/1.00  fof(f10,axiom,(
% 3.13/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f26,plain,(
% 3.13/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f10])).
% 3.13/1.00  
% 3.13/1.00  fof(f48,plain,(
% 3.13/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(nnf_transformation,[],[f26])).
% 3.13/1.00  
% 3.13/1.00  fof(f74,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f48])).
% 3.13/1.00  
% 3.13/1.00  fof(f14,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f32,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f14])).
% 3.13/1.00  
% 3.13/1.00  fof(f80,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f32])).
% 3.13/1.00  
% 3.13/1.00  fof(f7,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f23,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f7])).
% 3.13/1.00  
% 3.13/1.00  fof(f46,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.13/1.00    inference(nnf_transformation,[],[f23])).
% 3.13/1.00  
% 3.13/1.00  fof(f47,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.13/1.00    inference(flattening,[],[f46])).
% 3.13/1.00  
% 3.13/1.00  fof(f67,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f47])).
% 3.13/1.00  
% 3.13/1.00  fof(f103,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 3.13/1.00    inference(definition_unfolding,[],[f67,f97,f98,f98,f97])).
% 3.13/1.00  
% 3.13/1.00  fof(f96,plain,(
% 3.13/1.00    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 3.13/1.00    inference(cnf_transformation,[],[f56])).
% 3.13/1.00  
% 3.13/1.00  fof(f105,plain,(
% 3.13/1.00    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)),
% 3.13/1.00    inference(definition_unfolding,[],[f96,f98,f98])).
% 3.13/1.00  
% 3.13/1.00  fof(f16,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f34,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f16])).
% 3.13/1.00  
% 3.13/1.00  fof(f82,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f12,axiom,(
% 3.13/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f29,plain,(
% 3.13/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.13/1.00    inference(ennf_transformation,[],[f12])).
% 3.13/1.00  
% 3.13/1.00  fof(f30,plain,(
% 3.13/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(flattening,[],[f29])).
% 3.13/1.00  
% 3.13/1.00  fof(f78,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f30])).
% 3.13/1.00  
% 3.13/1.00  fof(f104,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.13/1.00    inference(definition_unfolding,[],[f78,f98,f98])).
% 3.13/1.00  
% 3.13/1.00  fof(f92,plain,(
% 3.13/1.00    v1_funct_1(sK5)),
% 3.13/1.00    inference(cnf_transformation,[],[f56])).
% 3.13/1.00  
% 3.13/1.00  fof(f11,axiom,(
% 3.13/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f27,plain,(
% 3.13/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f11])).
% 3.13/1.00  
% 3.13/1.00  fof(f28,plain,(
% 3.13/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.13/1.00    inference(flattening,[],[f27])).
% 3.13/1.00  
% 3.13/1.00  fof(f76,plain,(
% 3.13/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f28])).
% 3.13/1.00  
% 3.13/1.00  fof(f18,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f36,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f18])).
% 3.13/1.00  
% 3.13/1.00  fof(f37,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(flattening,[],[f36])).
% 3.13/1.00  
% 3.13/1.00  fof(f54,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(nnf_transformation,[],[f37])).
% 3.13/1.00  
% 3.13/1.00  fof(f86,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f54])).
% 3.13/1.00  
% 3.13/1.00  fof(f93,plain,(
% 3.13/1.00    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 3.13/1.00    inference(cnf_transformation,[],[f56])).
% 3.13/1.00  
% 3.13/1.00  fof(f107,plain,(
% 3.13/1.00    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 3.13/1.00    inference(definition_unfolding,[],[f93,f98])).
% 3.13/1.00  
% 3.13/1.00  fof(f95,plain,(
% 3.13/1.00    k1_xboole_0 != sK4),
% 3.13/1.00    inference(cnf_transformation,[],[f56])).
% 3.13/1.00  
% 3.13/1.00  fof(f17,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f35,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.13/1.00    inference(ennf_transformation,[],[f17])).
% 3.13/1.00  
% 3.13/1.00  fof(f49,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.13/1.00    inference(nnf_transformation,[],[f35])).
% 3.13/1.00  
% 3.13/1.00  fof(f50,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.13/1.00    inference(rectify,[],[f49])).
% 3.13/1.00  
% 3.13/1.00  fof(f52,plain,(
% 3.13/1.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f51,plain,(
% 3.13/1.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f53,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f52,f51])).
% 3.13/1.00  
% 3.13/1.00  fof(f85,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f53])).
% 3.13/1.00  
% 3.13/1.00  fof(f13,axiom,(
% 3.13/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f31,plain,(
% 3.13/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f13])).
% 3.13/1.00  
% 3.13/1.00  fof(f79,plain,(
% 3.13/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f31])).
% 3.13/1.00  
% 3.13/1.00  fof(f3,axiom,(
% 3.13/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f63,plain,(
% 3.13/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f3])).
% 3.13/1.00  
% 3.13/1.00  fof(f2,axiom,(
% 3.13/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f44,plain,(
% 3.13/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.00    inference(nnf_transformation,[],[f2])).
% 3.13/1.00  
% 3.13/1.00  fof(f45,plain,(
% 3.13/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.00    inference(flattening,[],[f44])).
% 3.13/1.00  
% 3.13/1.00  fof(f62,plain,(
% 3.13/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f45])).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1,plain,
% 3.13/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1246,plain,
% 3.13/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.13/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_34,negated_conjecture,
% 3.13/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1226,plain,
% 3.13/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_21,plain,
% 3.13/1.00      ( v4_relat_1(X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_15,plain,
% 3.13/1.00      ( ~ v4_relat_1(X0,X1)
% 3.13/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.13/1.00      | ~ v1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_403,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.13/1.00      | ~ v1_relat_1(X0) ),
% 3.13/1.00      inference(resolution,[status(thm)],[c_21,c_15]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_20,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | v1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_407,plain,
% 3.13/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_403,c_20]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_408,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.13/1.00      inference(renaming,[status(thm)],[c_407]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1224,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1521,plain,
% 3.13/1.00      ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1226,c_1224]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_11,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 3.13/1.00      | k2_enumset1(X1,X1,X1,X2) = X0
% 3.13/1.00      | k2_enumset1(X2,X2,X2,X2) = X0
% 3.13/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.13/1.00      | k1_xboole_0 = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1237,plain,
% 3.13/1.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.13/1.00      | k2_enumset1(X0,X0,X0,X2) = X1
% 3.13/1.00      | k2_enumset1(X2,X2,X2,X2) = X1
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3151,plain,
% 3.13/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
% 3.13/1.00      | k1_relat_1(sK5) = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1521,c_1237]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3308,plain,
% 3.13/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 3.13/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_3151,c_1226]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_32,negated_conjecture,
% 3.13/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 3.13/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_22,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1467,plain,
% 3.13/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 3.13/1.00      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_765,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1460,plain,
% 3.13/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
% 3.13/1.00      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 3.13/1.00      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_765]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1544,plain,
% 3.13/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 3.13/1.00      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
% 3.13/1.00      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1460]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_18,plain,
% 3.13/1.00      ( ~ v1_funct_1(X0)
% 3.13/1.00      | ~ v1_relat_1(X0)
% 3.13/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.13/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_36,negated_conjecture,
% 3.13/1.00      ( v1_funct_1(sK5) ),
% 3.13/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_384,plain,
% 3.13/1.00      ( ~ v1_relat_1(X0)
% 3.13/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.13/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.13/1.00      | sK5 != X0 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_36]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_385,plain,
% 3.13/1.00      ( ~ v1_relat_1(sK5)
% 3.13/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 3.13/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_384]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1225,plain,
% 3.13/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 3.13/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 3.13/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_39,plain,
% 3.13/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_386,plain,
% 3.13/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 3.13/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 3.13/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1440,plain,
% 3.13/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 3.13/1.00      | v1_relat_1(sK5) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1441,plain,
% 3.13/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 3.13/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1440]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1475,plain,
% 3.13/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 3.13/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_1225,c_39,c_386,c_1441]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1476,plain,
% 3.13/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 3.13/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 3.13/1.00      inference(renaming,[status(thm)],[c_1475]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3299,plain,
% 3.13/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
% 3.13/1.00      | k1_relat_1(sK5) = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_3151,c_1476]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3648,plain,
% 3.13/1.00      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_3308,c_34,c_32,c_1467,c_1544,c_3299]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_17,plain,
% 3.13/1.00      ( ~ v1_relat_1(X0)
% 3.13/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1233,plain,
% 3.13/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3666,plain,
% 3.13/1.00      ( sK5 = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_3648,c_1233]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1561,plain,
% 3.13/1.00      ( ~ v1_relat_1(sK5)
% 3.13/1.00      | k1_relat_1(sK5) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = sK5 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_764,plain,( X0 = X0 ),theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1574,plain,
% 3.13/1.00      ( sK5 = sK5 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_764]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1888,plain,
% 3.13/1.00      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_765]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3123,plain,
% 3.13/1.00      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1888]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3124,plain,
% 3.13/1.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_3123]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3671,plain,
% 3.13/1.00      ( sK5 = k1_xboole_0 ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_3666,c_34,c_32,c_1440,c_1467,c_1544,c_1561,c_1574,
% 3.13/1.00                 c_3124,c_3299]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_31,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_35,negated_conjecture,
% 3.13/1.00      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 3.13/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_521,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 3.13/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.13/1.00      | sK4 != X2
% 3.13/1.00      | sK5 != X0
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_522,plain,
% 3.13/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 3.13/1.00      | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 3.13/1.00      | k1_xboole_0 = sK4 ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_521]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_33,negated_conjecture,
% 3.13/1.00      ( k1_xboole_0 != sK4 ),
% 3.13/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_524,plain,
% 3.13/1.00      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_522,c_34,c_33]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_23,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | ~ r2_hidden(X3,X1)
% 3.13/1.00      | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
% 3.13/1.00      | k1_relset_1(X1,X2,X0) != X1 ),
% 3.13/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1229,plain,
% 3.13/1.00      ( k1_relset_1(X0,X1,X2) != X0
% 3.13/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.13/1.00      | r2_hidden(X3,X0) != iProver_top
% 3.13/1.00      | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2992,plain,
% 3.13/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 3.13/1.00      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 3.13/1.00      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_524,c_1229]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3282,plain,
% 3.13/1.00      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 3.13/1.00      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_2992,c_39]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3675,plain,
% 3.13/1.00      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 3.13/1.00      | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_3671,c_3282]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4158,plain,
% 3.13/1.00      ( r2_hidden(k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3),X0),sK1(k1_xboole_0,sK0(k2_enumset1(sK3,sK3,sK3,sK3),X0))),k1_xboole_0) = iProver_top
% 3.13/1.00      | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1246,c_3675]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_19,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1232,plain,
% 3.13/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.13/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4383,plain,
% 3.13/1.00      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top
% 3.13/1.00      | r1_tarski(k1_xboole_0,k4_tarski(sK0(k2_enumset1(sK3,sK3,sK3,sK3),X0),sK1(k1_xboole_0,sK0(k2_enumset1(sK3,sK3,sK3,sK3),X0)))) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_4158,c_1232]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6,plain,
% 3.13/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1242,plain,
% 3.13/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4614,plain,
% 3.13/1.00      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
% 3.13/1.00      inference(forward_subsumption_resolution,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_4383,c_1242]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1244,plain,
% 3.13/1.00      ( X0 = X1
% 3.13/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.13/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2282,plain,
% 3.13/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
% 3.13/1.00      | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_relat_1(sK5)) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1521,c_1244]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3652,plain,
% 3.13/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 3.13/1.00      | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0) != iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_3648,c_2282]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4623,plain,
% 3.13/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_4614,c_3652]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3654,plain,
% 3.13/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 3.13/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_3648,c_1476]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4174,plain,
% 3.13/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 3.13/1.00      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_3654,c_3671]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4654,plain,
% 3.13/1.00      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k2_relat_1(k1_xboole_0) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_4623,c_4174]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1230,plain,
% 3.13/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.13/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2267,plain,
% 3.13/1.00      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1226,c_1230]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2423,plain,
% 3.13/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_2267,c_32]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3677,plain,
% 3.13/1.00      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_3671,c_2423]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(contradiction,plain,
% 3.13/1.00      ( $false ),
% 3.13/1.00      inference(minisat,[status(thm)],[c_4654,c_3677]) ).
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  ------                               Statistics
% 3.13/1.00  
% 3.13/1.00  ------ General
% 3.13/1.00  
% 3.13/1.00  abstr_ref_over_cycles:                  0
% 3.13/1.00  abstr_ref_under_cycles:                 0
% 3.13/1.00  gc_basic_clause_elim:                   0
% 3.13/1.00  forced_gc_time:                         0
% 3.13/1.00  parsing_time:                           0.014
% 3.13/1.00  unif_index_cands_time:                  0.
% 3.13/1.00  unif_index_add_time:                    0.
% 3.13/1.00  orderings_time:                         0.
% 3.13/1.00  out_proof_time:                         0.023
% 3.13/1.00  total_time:                             0.225
% 3.13/1.00  num_of_symbols:                         54
% 3.13/1.00  num_of_terms:                           5058
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing
% 3.13/1.00  
% 3.13/1.00  num_of_splits:                          0
% 3.13/1.00  num_of_split_atoms:                     0
% 3.13/1.00  num_of_reused_defs:                     0
% 3.13/1.00  num_eq_ax_congr_red:                    28
% 3.13/1.00  num_of_sem_filtered_clauses:            1
% 3.13/1.00  num_of_subtypes:                        0
% 3.13/1.00  monotx_restored_types:                  0
% 3.13/1.00  sat_num_of_epr_types:                   0
% 3.13/1.00  sat_num_of_non_cyclic_types:            0
% 3.13/1.00  sat_guarded_non_collapsed_types:        0
% 3.13/1.00  num_pure_diseq_elim:                    0
% 3.13/1.00  simp_replaced_by:                       0
% 3.13/1.00  res_preprocessed:                       154
% 3.13/1.00  prep_upred:                             0
% 3.13/1.00  prep_unflattend:                        30
% 3.13/1.00  smt_new_axioms:                         0
% 3.13/1.00  pred_elim_cands:                        4
% 3.13/1.00  pred_elim:                              3
% 3.13/1.00  pred_elim_cl:                           7
% 3.13/1.00  pred_elim_cycles:                       6
% 3.13/1.00  merged_defs:                            0
% 3.13/1.00  merged_defs_ncl:                        0
% 3.13/1.00  bin_hyper_res:                          0
% 3.13/1.00  prep_cycles:                            4
% 3.13/1.00  pred_elim_time:                         0.004
% 3.13/1.00  splitting_time:                         0.
% 3.13/1.00  sem_filter_time:                        0.
% 3.13/1.00  monotx_time:                            0.
% 3.13/1.00  subtype_inf_time:                       0.
% 3.13/1.00  
% 3.13/1.00  ------ Problem properties
% 3.13/1.00  
% 3.13/1.00  clauses:                                29
% 3.13/1.00  conjectures:                            3
% 3.13/1.00  epr:                                    6
% 3.13/1.00  horn:                                   25
% 3.13/1.00  ground:                                 6
% 3.13/1.00  unary:                                  11
% 3.13/1.00  binary:                                 6
% 3.13/1.00  lits:                                   63
% 3.13/1.00  lits_eq:                                23
% 3.13/1.00  fd_pure:                                0
% 3.13/1.00  fd_pseudo:                              0
% 3.13/1.00  fd_cond:                                2
% 3.13/1.00  fd_pseudo_cond:                         2
% 3.13/1.00  ac_symbols:                             0
% 3.13/1.00  
% 3.13/1.00  ------ Propositional Solver
% 3.13/1.00  
% 3.13/1.00  prop_solver_calls:                      27
% 3.13/1.00  prop_fast_solver_calls:                 917
% 3.13/1.00  smt_solver_calls:                       0
% 3.13/1.00  smt_fast_solver_calls:                  0
% 3.13/1.00  prop_num_of_clauses:                    1720
% 3.13/1.00  prop_preprocess_simplified:             6697
% 3.13/1.00  prop_fo_subsumed:                       16
% 3.13/1.00  prop_solver_time:                       0.
% 3.13/1.00  smt_solver_time:                        0.
% 3.13/1.00  smt_fast_solver_time:                   0.
% 3.13/1.00  prop_fast_solver_time:                  0.
% 3.13/1.00  prop_unsat_core_time:                   0.
% 3.13/1.00  
% 3.13/1.00  ------ QBF
% 3.13/1.00  
% 3.13/1.00  qbf_q_res:                              0
% 3.13/1.00  qbf_num_tautologies:                    0
% 3.13/1.00  qbf_prep_cycles:                        0
% 3.13/1.00  
% 3.13/1.00  ------ BMC1
% 3.13/1.00  
% 3.13/1.00  bmc1_current_bound:                     -1
% 3.13/1.00  bmc1_last_solved_bound:                 -1
% 3.13/1.00  bmc1_unsat_core_size:                   -1
% 3.13/1.00  bmc1_unsat_core_parents_size:           -1
% 3.13/1.00  bmc1_merge_next_fun:                    0
% 3.13/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation
% 3.13/1.00  
% 3.13/1.00  inst_num_of_clauses:                    549
% 3.13/1.00  inst_num_in_passive:                    199
% 3.13/1.00  inst_num_in_active:                     205
% 3.13/1.00  inst_num_in_unprocessed:                145
% 3.13/1.00  inst_num_of_loops:                      290
% 3.13/1.00  inst_num_of_learning_restarts:          0
% 3.13/1.00  inst_num_moves_active_passive:          83
% 3.13/1.00  inst_lit_activity:                      0
% 3.13/1.00  inst_lit_activity_moves:                0
% 3.13/1.00  inst_num_tautologies:                   0
% 3.13/1.00  inst_num_prop_implied:                  0
% 3.13/1.00  inst_num_existing_simplified:           0
% 3.13/1.00  inst_num_eq_res_simplified:             0
% 3.13/1.00  inst_num_child_elim:                    0
% 3.13/1.00  inst_num_of_dismatching_blockings:      137
% 3.13/1.00  inst_num_of_non_proper_insts:           405
% 3.13/1.00  inst_num_of_duplicates:                 0
% 3.13/1.00  inst_inst_num_from_inst_to_res:         0
% 3.13/1.00  inst_dismatching_checking_time:         0.
% 3.13/1.00  
% 3.13/1.00  ------ Resolution
% 3.13/1.00  
% 3.13/1.00  res_num_of_clauses:                     0
% 3.13/1.00  res_num_in_passive:                     0
% 3.13/1.00  res_num_in_active:                      0
% 3.13/1.00  res_num_of_loops:                       158
% 3.13/1.00  res_forward_subset_subsumed:            63
% 3.13/1.00  res_backward_subset_subsumed:           0
% 3.13/1.00  res_forward_subsumed:                   0
% 3.13/1.00  res_backward_subsumed:                  0
% 3.13/1.00  res_forward_subsumption_resolution:     0
% 3.13/1.00  res_backward_subsumption_resolution:    0
% 3.13/1.00  res_clause_to_clause_subsumption:       199
% 3.13/1.00  res_orphan_elimination:                 0
% 3.13/1.00  res_tautology_del:                      32
% 3.13/1.00  res_num_eq_res_simplified:              0
% 3.13/1.00  res_num_sel_changes:                    0
% 3.13/1.00  res_moves_from_active_to_pass:          0
% 3.13/1.00  
% 3.13/1.00  ------ Superposition
% 3.13/1.00  
% 3.13/1.00  sup_time_total:                         0.
% 3.13/1.00  sup_time_generating:                    0.
% 3.13/1.00  sup_time_sim_full:                      0.
% 3.13/1.00  sup_time_sim_immed:                     0.
% 3.13/1.00  
% 3.13/1.00  sup_num_of_clauses:                     54
% 3.13/1.00  sup_num_in_active:                      36
% 3.13/1.00  sup_num_in_passive:                     18
% 3.13/1.00  sup_num_of_loops:                       57
% 3.13/1.00  sup_fw_superposition:                   35
% 3.13/1.00  sup_bw_superposition:                   45
% 3.13/1.00  sup_immediate_simplified:               17
% 3.13/1.00  sup_given_eliminated:                   1
% 3.13/1.00  comparisons_done:                       0
% 3.13/1.00  comparisons_avoided:                    0
% 3.13/1.00  
% 3.13/1.00  ------ Simplifications
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  sim_fw_subset_subsumed:                 8
% 3.13/1.00  sim_bw_subset_subsumed:                 7
% 3.13/1.00  sim_fw_subsumed:                        11
% 3.13/1.00  sim_bw_subsumed:                        0
% 3.13/1.00  sim_fw_subsumption_res:                 2
% 3.13/1.00  sim_bw_subsumption_res:                 0
% 3.13/1.00  sim_tautology_del:                      1
% 3.13/1.00  sim_eq_tautology_del:                   13
% 3.13/1.00  sim_eq_res_simp:                        0
% 3.13/1.00  sim_fw_demodulated:                     2
% 3.13/1.00  sim_bw_demodulated:                     22
% 3.13/1.00  sim_light_normalised:                   7
% 3.13/1.00  sim_joinable_taut:                      0
% 3.13/1.00  sim_joinable_simp:                      0
% 3.13/1.00  sim_ac_normalised:                      0
% 3.13/1.00  sim_smt_subsumption:                    0
% 3.13/1.00  
%------------------------------------------------------------------------------
