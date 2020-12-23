%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:27 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 498 expanded)
%              Number of clauses        :   51 (  80 expanded)
%              Number of leaves         :   20 ( 134 expanded)
%              Depth                    :   22
%              Number of atoms          :  402 (1212 expanded)
%              Number of equality atoms :  233 ( 722 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,
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

fof(f42,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f41])).

fof(f79,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f82])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f83])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f84])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f85])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f86])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f79,f87])).

fof(f78,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    v1_funct_2(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f78,f87])).

fof(f15,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f18,f30,f29])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f63])).

fof(f36,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f37])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f62])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f68,f87,f87])).

fof(f77,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f81,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f81,f87,f87])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_409,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_410,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_2541,plain,
    ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k1_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_410])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_364,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_365,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_777,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X1
    | sK5 != sK5
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_365])).

cnf(c_778,plain,
    ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_779,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
    | k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_778,c_28])).

cnf(c_780,plain,
    ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_779])).

cnf(c_1243,plain,
    ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_780])).

cnf(c_2919,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2541,c_1243])).

cnf(c_14,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2337,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3553,plain,
    ( sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2919,c_2337])).

cnf(c_4,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2347,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2349,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4687,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2349])).

cnf(c_5824,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3553,c_4687])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_330,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_2334,plain,
    ( k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_6128,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5824,c_2334])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_349,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_350,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_2333,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_3062,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2333])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3877,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3878,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3877])).

cnf(c_4089,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3062,c_3878])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2335,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4094,plain,
    ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_4089,c_2335])).

cnf(c_6131,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6128,c_2919,c_4094])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_400,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_401,plain,
    ( k2_relset_1(X0,X1,sK5) = k2_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_2538,plain,
    ( k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_401])).

cnf(c_27,negated_conjecture,
    ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2581,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2538,c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6131,c_3878,c_3062,c_2581])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : iproveropt_run.sh %d %s
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 17:48:34 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  % Running in FOF mode
% 2.92/0.85  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/0.85  
% 2.92/0.85  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/0.85  
% 2.92/0.85  ------  iProver source info
% 2.92/0.85  
% 2.92/0.85  git: date: 2020-06-30 10:37:57 +0100
% 2.92/0.85  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/0.85  git: non_committed_changes: false
% 2.92/0.85  git: last_make_outside_of_git: false
% 2.92/0.85  
% 2.92/0.85  ------ 
% 2.92/0.85  
% 2.92/0.85  ------ Input Options
% 2.92/0.85  
% 2.92/0.85  --out_options                           all
% 2.92/0.85  --tptp_safe_out                         true
% 2.92/0.85  --problem_path                          ""
% 2.92/0.85  --include_path                          ""
% 2.92/0.85  --clausifier                            res/vclausify_rel
% 2.92/0.85  --clausifier_options                    --mode clausify
% 2.92/0.85  --stdin                                 false
% 2.92/0.85  --stats_out                             all
% 2.92/0.85  
% 2.92/0.85  ------ General Options
% 2.92/0.85  
% 2.92/0.85  --fof                                   false
% 2.92/0.85  --time_out_real                         305.
% 2.92/0.85  --time_out_virtual                      -1.
% 2.92/0.85  --symbol_type_check                     false
% 2.92/0.85  --clausify_out                          false
% 2.92/0.85  --sig_cnt_out                           false
% 2.92/0.85  --trig_cnt_out                          false
% 2.92/0.85  --trig_cnt_out_tolerance                1.
% 2.92/0.85  --trig_cnt_out_sk_spl                   false
% 2.92/0.85  --abstr_cl_out                          false
% 2.92/0.85  
% 2.92/0.85  ------ Global Options
% 2.92/0.85  
% 2.92/0.85  --schedule                              default
% 2.92/0.85  --add_important_lit                     false
% 2.92/0.85  --prop_solver_per_cl                    1000
% 2.92/0.85  --min_unsat_core                        false
% 2.92/0.85  --soft_assumptions                      false
% 2.92/0.85  --soft_lemma_size                       3
% 2.92/0.85  --prop_impl_unit_size                   0
% 2.92/0.85  --prop_impl_unit                        []
% 2.92/0.85  --share_sel_clauses                     true
% 2.92/0.85  --reset_solvers                         false
% 2.92/0.85  --bc_imp_inh                            [conj_cone]
% 2.92/0.85  --conj_cone_tolerance                   3.
% 2.92/0.85  --extra_neg_conj                        none
% 2.92/0.85  --large_theory_mode                     true
% 2.92/0.85  --prolific_symb_bound                   200
% 2.92/0.85  --lt_threshold                          2000
% 2.92/0.85  --clause_weak_htbl                      true
% 2.92/0.85  --gc_record_bc_elim                     false
% 2.92/0.85  
% 2.92/0.85  ------ Preprocessing Options
% 2.92/0.85  
% 2.92/0.85  --preprocessing_flag                    true
% 2.92/0.85  --time_out_prep_mult                    0.1
% 2.92/0.85  --splitting_mode                        input
% 2.92/0.85  --splitting_grd                         true
% 2.92/0.85  --splitting_cvd                         false
% 2.92/0.85  --splitting_cvd_svl                     false
% 2.92/0.85  --splitting_nvd                         32
% 2.92/0.85  --sub_typing                            true
% 2.92/0.85  --prep_gs_sim                           true
% 2.92/0.85  --prep_unflatten                        true
% 2.92/0.85  --prep_res_sim                          true
% 2.92/0.85  --prep_upred                            true
% 2.92/0.85  --prep_sem_filter                       exhaustive
% 2.92/0.85  --prep_sem_filter_out                   false
% 2.92/0.85  --pred_elim                             true
% 2.92/0.85  --res_sim_input                         true
% 2.92/0.85  --eq_ax_congr_red                       true
% 2.92/0.85  --pure_diseq_elim                       true
% 2.92/0.85  --brand_transform                       false
% 2.92/0.85  --non_eq_to_eq                          false
% 2.92/0.85  --prep_def_merge                        true
% 2.92/0.85  --prep_def_merge_prop_impl              false
% 2.92/0.85  --prep_def_merge_mbd                    true
% 2.92/0.85  --prep_def_merge_tr_red                 false
% 2.92/0.85  --prep_def_merge_tr_cl                  false
% 2.92/0.85  --smt_preprocessing                     true
% 2.92/0.85  --smt_ac_axioms                         fast
% 2.92/0.85  --preprocessed_out                      false
% 2.92/0.85  --preprocessed_stats                    false
% 2.92/0.85  
% 2.92/0.85  ------ Abstraction refinement Options
% 2.92/0.85  
% 2.92/0.85  --abstr_ref                             []
% 2.92/0.85  --abstr_ref_prep                        false
% 2.92/0.85  --abstr_ref_until_sat                   false
% 2.92/0.85  --abstr_ref_sig_restrict                funpre
% 2.92/0.85  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.85  --abstr_ref_under                       []
% 2.92/0.85  
% 2.92/0.85  ------ SAT Options
% 2.92/0.85  
% 2.92/0.85  --sat_mode                              false
% 2.92/0.85  --sat_fm_restart_options                ""
% 2.92/0.85  --sat_gr_def                            false
% 2.92/0.85  --sat_epr_types                         true
% 2.92/0.85  --sat_non_cyclic_types                  false
% 2.92/0.85  --sat_finite_models                     false
% 2.92/0.85  --sat_fm_lemmas                         false
% 2.92/0.85  --sat_fm_prep                           false
% 2.92/0.85  --sat_fm_uc_incr                        true
% 2.92/0.85  --sat_out_model                         small
% 2.92/0.85  --sat_out_clauses                       false
% 2.92/0.85  
% 2.92/0.85  ------ QBF Options
% 2.92/0.85  
% 2.92/0.85  --qbf_mode                              false
% 2.92/0.85  --qbf_elim_univ                         false
% 2.92/0.85  --qbf_dom_inst                          none
% 2.92/0.85  --qbf_dom_pre_inst                      false
% 2.92/0.85  --qbf_sk_in                             false
% 2.92/0.85  --qbf_pred_elim                         true
% 2.92/0.85  --qbf_split                             512
% 2.92/0.85  
% 2.92/0.85  ------ BMC1 Options
% 2.92/0.85  
% 2.92/0.85  --bmc1_incremental                      false
% 2.92/0.85  --bmc1_axioms                           reachable_all
% 2.92/0.85  --bmc1_min_bound                        0
% 2.92/0.85  --bmc1_max_bound                        -1
% 2.92/0.85  --bmc1_max_bound_default                -1
% 2.92/0.85  --bmc1_symbol_reachability              true
% 2.92/0.85  --bmc1_property_lemmas                  false
% 2.92/0.85  --bmc1_k_induction                      false
% 2.92/0.85  --bmc1_non_equiv_states                 false
% 2.92/0.85  --bmc1_deadlock                         false
% 2.92/0.85  --bmc1_ucm                              false
% 2.92/0.85  --bmc1_add_unsat_core                   none
% 2.92/0.85  --bmc1_unsat_core_children              false
% 2.92/0.85  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.85  --bmc1_out_stat                         full
% 2.92/0.85  --bmc1_ground_init                      false
% 2.92/0.85  --bmc1_pre_inst_next_state              false
% 2.92/0.85  --bmc1_pre_inst_state                   false
% 2.92/0.85  --bmc1_pre_inst_reach_state             false
% 2.92/0.85  --bmc1_out_unsat_core                   false
% 2.92/0.85  --bmc1_aig_witness_out                  false
% 2.92/0.85  --bmc1_verbose                          false
% 2.92/0.85  --bmc1_dump_clauses_tptp                false
% 2.92/0.85  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.85  --bmc1_dump_file                        -
% 2.92/0.85  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.85  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.85  --bmc1_ucm_extend_mode                  1
% 2.92/0.85  --bmc1_ucm_init_mode                    2
% 2.92/0.85  --bmc1_ucm_cone_mode                    none
% 2.92/0.85  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.85  --bmc1_ucm_relax_model                  4
% 2.92/0.85  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.85  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.85  --bmc1_ucm_layered_model                none
% 2.92/0.85  --bmc1_ucm_max_lemma_size               10
% 2.92/0.85  
% 2.92/0.85  ------ AIG Options
% 2.92/0.85  
% 2.92/0.85  --aig_mode                              false
% 2.92/0.85  
% 2.92/0.85  ------ Instantiation Options
% 2.92/0.85  
% 2.92/0.85  --instantiation_flag                    true
% 2.92/0.85  --inst_sos_flag                         false
% 2.92/0.85  --inst_sos_phase                        true
% 2.92/0.85  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.85  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.85  --inst_lit_sel_side                     num_symb
% 2.92/0.85  --inst_solver_per_active                1400
% 2.92/0.85  --inst_solver_calls_frac                1.
% 2.92/0.85  --inst_passive_queue_type               priority_queues
% 2.92/0.85  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.85  --inst_passive_queues_freq              [25;2]
% 2.92/0.85  --inst_dismatching                      true
% 2.92/0.85  --inst_eager_unprocessed_to_passive     true
% 2.92/0.85  --inst_prop_sim_given                   true
% 2.92/0.85  --inst_prop_sim_new                     false
% 2.92/0.85  --inst_subs_new                         false
% 2.92/0.85  --inst_eq_res_simp                      false
% 2.92/0.85  --inst_subs_given                       false
% 2.92/0.85  --inst_orphan_elimination               true
% 2.92/0.85  --inst_learning_loop_flag               true
% 2.92/0.85  --inst_learning_start                   3000
% 2.92/0.85  --inst_learning_factor                  2
% 2.92/0.85  --inst_start_prop_sim_after_learn       3
% 2.92/0.85  --inst_sel_renew                        solver
% 2.92/0.85  --inst_lit_activity_flag                true
% 2.92/0.85  --inst_restr_to_given                   false
% 2.92/0.85  --inst_activity_threshold               500
% 2.92/0.85  --inst_out_proof                        true
% 2.92/0.85  
% 2.92/0.85  ------ Resolution Options
% 2.92/0.85  
% 2.92/0.85  --resolution_flag                       true
% 2.92/0.85  --res_lit_sel                           adaptive
% 2.92/0.85  --res_lit_sel_side                      none
% 2.92/0.85  --res_ordering                          kbo
% 2.92/0.85  --res_to_prop_solver                    active
% 2.92/0.85  --res_prop_simpl_new                    false
% 2.92/0.85  --res_prop_simpl_given                  true
% 2.92/0.85  --res_passive_queue_type                priority_queues
% 2.92/0.85  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.86  --res_passive_queues_freq               [15;5]
% 2.92/0.86  --res_forward_subs                      full
% 2.92/0.86  --res_backward_subs                     full
% 2.92/0.86  --res_forward_subs_resolution           true
% 2.92/0.86  --res_backward_subs_resolution          true
% 2.92/0.86  --res_orphan_elimination                true
% 2.92/0.86  --res_time_limit                        2.
% 2.92/0.86  --res_out_proof                         true
% 2.92/0.86  
% 2.92/0.86  ------ Superposition Options
% 2.92/0.86  
% 2.92/0.86  --superposition_flag                    true
% 2.92/0.86  --sup_passive_queue_type                priority_queues
% 2.92/0.86  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.86  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.86  --demod_completeness_check              fast
% 2.92/0.86  --demod_use_ground                      true
% 2.92/0.86  --sup_to_prop_solver                    passive
% 2.92/0.86  --sup_prop_simpl_new                    true
% 2.92/0.86  --sup_prop_simpl_given                  true
% 2.92/0.86  --sup_fun_splitting                     false
% 2.92/0.86  --sup_smt_interval                      50000
% 2.92/0.86  
% 2.92/0.86  ------ Superposition Simplification Setup
% 2.92/0.86  
% 2.92/0.86  --sup_indices_passive                   []
% 2.92/0.86  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.86  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.86  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.86  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.86  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.86  --sup_full_bw                           [BwDemod]
% 2.92/0.86  --sup_immed_triv                        [TrivRules]
% 2.92/0.86  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.86  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.86  --sup_immed_bw_main                     []
% 2.92/0.86  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.86  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.86  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.86  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.86  
% 2.92/0.86  ------ Combination Options
% 2.92/0.86  
% 2.92/0.86  --comb_res_mult                         3
% 2.92/0.86  --comb_sup_mult                         2
% 2.92/0.86  --comb_inst_mult                        10
% 2.92/0.86  
% 2.92/0.86  ------ Debug Options
% 2.92/0.86  
% 2.92/0.86  --dbg_backtrace                         false
% 2.92/0.86  --dbg_dump_prop_clauses                 false
% 2.92/0.86  --dbg_dump_prop_clauses_file            -
% 2.92/0.86  --dbg_out_stat                          false
% 2.92/0.86  ------ Parsing...
% 2.92/0.86  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/0.86  
% 2.92/0.86  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.92/0.86  
% 2.92/0.86  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/0.86  
% 2.92/0.86  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/0.86  ------ Proving...
% 2.92/0.86  ------ Problem Properties 
% 2.92/0.86  
% 2.92/0.86  
% 2.92/0.86  clauses                                 26
% 2.92/0.86  conjectures                             2
% 2.92/0.86  EPR                                     12
% 2.92/0.86  Horn                                    23
% 2.92/0.86  unary                                   13
% 2.92/0.86  binary                                  4
% 2.92/0.86  lits                                    55
% 2.92/0.86  lits eq                                 26
% 2.92/0.86  fd_pure                                 0
% 2.92/0.86  fd_pseudo                               0
% 2.92/0.86  fd_cond                                 0
% 2.92/0.86  fd_pseudo_cond                          2
% 2.92/0.86  AC symbols                              0
% 2.92/0.86  
% 2.92/0.86  ------ Schedule dynamic 5 is on 
% 2.92/0.86  
% 2.92/0.86  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/0.86  
% 2.92/0.86  
% 2.92/0.86  ------ 
% 2.92/0.86  Current options:
% 2.92/0.86  ------ 
% 2.92/0.86  
% 2.92/0.86  ------ Input Options
% 2.92/0.86  
% 2.92/0.86  --out_options                           all
% 2.92/0.86  --tptp_safe_out                         true
% 2.92/0.86  --problem_path                          ""
% 2.92/0.86  --include_path                          ""
% 2.92/0.86  --clausifier                            res/vclausify_rel
% 2.92/0.86  --clausifier_options                    --mode clausify
% 2.92/0.86  --stdin                                 false
% 2.92/0.86  --stats_out                             all
% 2.92/0.86  
% 2.92/0.86  ------ General Options
% 2.92/0.86  
% 2.92/0.86  --fof                                   false
% 2.92/0.86  --time_out_real                         305.
% 2.92/0.86  --time_out_virtual                      -1.
% 2.92/0.86  --symbol_type_check                     false
% 2.92/0.86  --clausify_out                          false
% 2.92/0.86  --sig_cnt_out                           false
% 2.92/0.86  --trig_cnt_out                          false
% 2.92/0.86  --trig_cnt_out_tolerance                1.
% 2.92/0.86  --trig_cnt_out_sk_spl                   false
% 2.92/0.86  --abstr_cl_out                          false
% 2.92/0.86  
% 2.92/0.86  ------ Global Options
% 2.92/0.86  
% 2.92/0.86  --schedule                              default
% 2.92/0.86  --add_important_lit                     false
% 2.92/0.86  --prop_solver_per_cl                    1000
% 2.92/0.86  --min_unsat_core                        false
% 2.92/0.86  --soft_assumptions                      false
% 2.92/0.86  --soft_lemma_size                       3
% 2.92/0.86  --prop_impl_unit_size                   0
% 2.92/0.86  --prop_impl_unit                        []
% 2.92/0.86  --share_sel_clauses                     true
% 2.92/0.86  --reset_solvers                         false
% 2.92/0.86  --bc_imp_inh                            [conj_cone]
% 2.92/0.86  --conj_cone_tolerance                   3.
% 2.92/0.86  --extra_neg_conj                        none
% 2.92/0.86  --large_theory_mode                     true
% 2.92/0.86  --prolific_symb_bound                   200
% 2.92/0.86  --lt_threshold                          2000
% 2.92/0.86  --clause_weak_htbl                      true
% 2.92/0.86  --gc_record_bc_elim                     false
% 2.92/0.86  
% 2.92/0.86  ------ Preprocessing Options
% 2.92/0.86  
% 2.92/0.86  --preprocessing_flag                    true
% 2.92/0.86  --time_out_prep_mult                    0.1
% 2.92/0.86  --splitting_mode                        input
% 2.92/0.86  --splitting_grd                         true
% 2.92/0.86  --splitting_cvd                         false
% 2.92/0.86  --splitting_cvd_svl                     false
% 2.92/0.86  --splitting_nvd                         32
% 2.92/0.86  --sub_typing                            true
% 2.92/0.86  --prep_gs_sim                           true
% 2.92/0.86  --prep_unflatten                        true
% 2.92/0.86  --prep_res_sim                          true
% 2.92/0.86  --prep_upred                            true
% 2.92/0.86  --prep_sem_filter                       exhaustive
% 2.92/0.86  --prep_sem_filter_out                   false
% 2.92/0.86  --pred_elim                             true
% 2.92/0.86  --res_sim_input                         true
% 2.92/0.86  --eq_ax_congr_red                       true
% 2.92/0.86  --pure_diseq_elim                       true
% 2.92/0.86  --brand_transform                       false
% 2.92/0.86  --non_eq_to_eq                          false
% 2.92/0.86  --prep_def_merge                        true
% 2.92/0.86  --prep_def_merge_prop_impl              false
% 2.92/0.86  --prep_def_merge_mbd                    true
% 2.92/0.86  --prep_def_merge_tr_red                 false
% 2.92/0.86  --prep_def_merge_tr_cl                  false
% 2.92/0.86  --smt_preprocessing                     true
% 2.92/0.86  --smt_ac_axioms                         fast
% 2.92/0.86  --preprocessed_out                      false
% 2.92/0.86  --preprocessed_stats                    false
% 2.92/0.86  
% 2.92/0.86  ------ Abstraction refinement Options
% 2.92/0.86  
% 2.92/0.86  --abstr_ref                             []
% 2.92/0.86  --abstr_ref_prep                        false
% 2.92/0.86  --abstr_ref_until_sat                   false
% 2.92/0.86  --abstr_ref_sig_restrict                funpre
% 2.92/0.86  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.86  --abstr_ref_under                       []
% 2.92/0.86  
% 2.92/0.86  ------ SAT Options
% 2.92/0.86  
% 2.92/0.86  --sat_mode                              false
% 2.92/0.86  --sat_fm_restart_options                ""
% 2.92/0.86  --sat_gr_def                            false
% 2.92/0.86  --sat_epr_types                         true
% 2.92/0.86  --sat_non_cyclic_types                  false
% 2.92/0.86  --sat_finite_models                     false
% 2.92/0.86  --sat_fm_lemmas                         false
% 2.92/0.86  --sat_fm_prep                           false
% 2.92/0.86  --sat_fm_uc_incr                        true
% 2.92/0.86  --sat_out_model                         small
% 2.92/0.86  --sat_out_clauses                       false
% 2.92/0.86  
% 2.92/0.86  ------ QBF Options
% 2.92/0.86  
% 2.92/0.86  --qbf_mode                              false
% 2.92/0.86  --qbf_elim_univ                         false
% 2.92/0.86  --qbf_dom_inst                          none
% 2.92/0.86  --qbf_dom_pre_inst                      false
% 2.92/0.86  --qbf_sk_in                             false
% 2.92/0.86  --qbf_pred_elim                         true
% 2.92/0.86  --qbf_split                             512
% 2.92/0.86  
% 2.92/0.86  ------ BMC1 Options
% 2.92/0.86  
% 2.92/0.86  --bmc1_incremental                      false
% 2.92/0.86  --bmc1_axioms                           reachable_all
% 2.92/0.86  --bmc1_min_bound                        0
% 2.92/0.86  --bmc1_max_bound                        -1
% 2.92/0.86  --bmc1_max_bound_default                -1
% 2.92/0.86  --bmc1_symbol_reachability              true
% 2.92/0.86  --bmc1_property_lemmas                  false
% 2.92/0.86  --bmc1_k_induction                      false
% 2.92/0.86  --bmc1_non_equiv_states                 false
% 2.92/0.86  --bmc1_deadlock                         false
% 2.92/0.86  --bmc1_ucm                              false
% 2.92/0.86  --bmc1_add_unsat_core                   none
% 2.92/0.86  --bmc1_unsat_core_children              false
% 2.92/0.86  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.86  --bmc1_out_stat                         full
% 2.92/0.86  --bmc1_ground_init                      false
% 2.92/0.86  --bmc1_pre_inst_next_state              false
% 2.92/0.86  --bmc1_pre_inst_state                   false
% 2.92/0.86  --bmc1_pre_inst_reach_state             false
% 2.92/0.86  --bmc1_out_unsat_core                   false
% 2.92/0.86  --bmc1_aig_witness_out                  false
% 2.92/0.86  --bmc1_verbose                          false
% 2.92/0.86  --bmc1_dump_clauses_tptp                false
% 2.92/0.86  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.86  --bmc1_dump_file                        -
% 2.92/0.86  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.86  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.86  --bmc1_ucm_extend_mode                  1
% 2.92/0.86  --bmc1_ucm_init_mode                    2
% 2.92/0.86  --bmc1_ucm_cone_mode                    none
% 2.92/0.86  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.86  --bmc1_ucm_relax_model                  4
% 2.92/0.86  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.86  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.86  --bmc1_ucm_layered_model                none
% 2.92/0.86  --bmc1_ucm_max_lemma_size               10
% 2.92/0.86  
% 2.92/0.86  ------ AIG Options
% 2.92/0.86  
% 2.92/0.86  --aig_mode                              false
% 2.92/0.86  
% 2.92/0.86  ------ Instantiation Options
% 2.92/0.86  
% 2.92/0.86  --instantiation_flag                    true
% 2.92/0.86  --inst_sos_flag                         false
% 2.92/0.86  --inst_sos_phase                        true
% 2.92/0.86  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.86  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.86  --inst_lit_sel_side                     none
% 2.92/0.86  --inst_solver_per_active                1400
% 2.92/0.86  --inst_solver_calls_frac                1.
% 2.92/0.86  --inst_passive_queue_type               priority_queues
% 2.92/0.86  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.86  --inst_passive_queues_freq              [25;2]
% 2.92/0.86  --inst_dismatching                      true
% 2.92/0.86  --inst_eager_unprocessed_to_passive     true
% 2.92/0.86  --inst_prop_sim_given                   true
% 2.92/0.86  --inst_prop_sim_new                     false
% 2.92/0.86  --inst_subs_new                         false
% 2.92/0.86  --inst_eq_res_simp                      false
% 2.92/0.86  --inst_subs_given                       false
% 2.92/0.86  --inst_orphan_elimination               true
% 2.92/0.86  --inst_learning_loop_flag               true
% 2.92/0.86  --inst_learning_start                   3000
% 2.92/0.86  --inst_learning_factor                  2
% 2.92/0.86  --inst_start_prop_sim_after_learn       3
% 2.92/0.86  --inst_sel_renew                        solver
% 2.92/0.86  --inst_lit_activity_flag                true
% 2.92/0.86  --inst_restr_to_given                   false
% 2.92/0.86  --inst_activity_threshold               500
% 2.92/0.86  --inst_out_proof                        true
% 2.92/0.86  
% 2.92/0.86  ------ Resolution Options
% 2.92/0.86  
% 2.92/0.86  --resolution_flag                       false
% 2.92/0.86  --res_lit_sel                           adaptive
% 2.92/0.86  --res_lit_sel_side                      none
% 2.92/0.86  --res_ordering                          kbo
% 2.92/0.86  --res_to_prop_solver                    active
% 2.92/0.86  --res_prop_simpl_new                    false
% 2.92/0.86  --res_prop_simpl_given                  true
% 2.92/0.86  --res_passive_queue_type                priority_queues
% 2.92/0.86  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.86  --res_passive_queues_freq               [15;5]
% 2.92/0.86  --res_forward_subs                      full
% 2.92/0.86  --res_backward_subs                     full
% 2.92/0.86  --res_forward_subs_resolution           true
% 2.92/0.86  --res_backward_subs_resolution          true
% 2.92/0.86  --res_orphan_elimination                true
% 2.92/0.86  --res_time_limit                        2.
% 2.92/0.86  --res_out_proof                         true
% 2.92/0.86  
% 2.92/0.86  ------ Superposition Options
% 2.92/0.86  
% 2.92/0.86  --superposition_flag                    true
% 2.92/0.86  --sup_passive_queue_type                priority_queues
% 2.92/0.86  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.86  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.86  --demod_completeness_check              fast
% 2.92/0.86  --demod_use_ground                      true
% 2.92/0.86  --sup_to_prop_solver                    passive
% 2.92/0.86  --sup_prop_simpl_new                    true
% 2.92/0.86  --sup_prop_simpl_given                  true
% 2.92/0.86  --sup_fun_splitting                     false
% 2.92/0.86  --sup_smt_interval                      50000
% 2.92/0.86  
% 2.92/0.86  ------ Superposition Simplification Setup
% 2.92/0.86  
% 2.92/0.86  --sup_indices_passive                   []
% 2.92/0.86  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.86  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.86  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.86  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.86  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.86  --sup_full_bw                           [BwDemod]
% 2.92/0.86  --sup_immed_triv                        [TrivRules]
% 2.92/0.86  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.86  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.86  --sup_immed_bw_main                     []
% 2.92/0.86  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.86  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.86  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.86  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.86  
% 2.92/0.86  ------ Combination Options
% 2.92/0.86  
% 2.92/0.86  --comb_res_mult                         3
% 2.92/0.86  --comb_sup_mult                         2
% 2.92/0.86  --comb_inst_mult                        10
% 2.92/0.86  
% 2.92/0.86  ------ Debug Options
% 2.92/0.86  
% 2.92/0.86  --dbg_backtrace                         false
% 2.92/0.86  --dbg_dump_prop_clauses                 false
% 2.92/0.86  --dbg_dump_prop_clauses_file            -
% 2.92/0.86  --dbg_out_stat                          false
% 2.92/0.86  
% 2.92/0.86  
% 2.92/0.86  
% 2.92/0.86  
% 2.92/0.86  ------ Proving...
% 2.92/0.86  
% 2.92/0.86  
% 2.92/0.86  % SZS status Theorem for theBenchmark.p
% 2.92/0.86  
% 2.92/0.86  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/0.86  
% 2.92/0.86  fof(f13,axiom,(
% 2.92/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f23,plain,(
% 2.92/0.86    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.86    inference(ennf_transformation,[],[f13])).
% 2.92/0.86  
% 2.92/0.86  fof(f69,plain,(
% 2.92/0.86    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.86    inference(cnf_transformation,[],[f23])).
% 2.92/0.86  
% 2.92/0.86  fof(f16,conjecture,(
% 2.92/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f17,negated_conjecture,(
% 2.92/0.86    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.92/0.86    inference(negated_conjecture,[],[f16])).
% 2.92/0.86  
% 2.92/0.86  fof(f27,plain,(
% 2.92/0.86    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.92/0.86    inference(ennf_transformation,[],[f17])).
% 2.92/0.86  
% 2.92/0.86  fof(f28,plain,(
% 2.92/0.86    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.92/0.86    inference(flattening,[],[f27])).
% 2.92/0.86  
% 2.92/0.86  fof(f41,plain,(
% 2.92/0.86    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 2.92/0.86    introduced(choice_axiom,[])).
% 2.92/0.86  
% 2.92/0.86  fof(f42,plain,(
% 2.92/0.86    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 2.92/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f41])).
% 2.92/0.86  
% 2.92/0.86  fof(f79,plain,(
% 2.92/0.86    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 2.92/0.86    inference(cnf_transformation,[],[f42])).
% 2.92/0.86  
% 2.92/0.86  fof(f1,axiom,(
% 2.92/0.86    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f43,plain,(
% 2.92/0.86    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f1])).
% 2.92/0.86  
% 2.92/0.86  fof(f2,axiom,(
% 2.92/0.86    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f44,plain,(
% 2.92/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f2])).
% 2.92/0.86  
% 2.92/0.86  fof(f3,axiom,(
% 2.92/0.86    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f45,plain,(
% 2.92/0.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f3])).
% 2.92/0.86  
% 2.92/0.86  fof(f4,axiom,(
% 2.92/0.86    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f46,plain,(
% 2.92/0.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f4])).
% 2.92/0.86  
% 2.92/0.86  fof(f5,axiom,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f47,plain,(
% 2.92/0.86    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f5])).
% 2.92/0.86  
% 2.92/0.86  fof(f6,axiom,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f48,plain,(
% 2.92/0.86    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f6])).
% 2.92/0.86  
% 2.92/0.86  fof(f7,axiom,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f49,plain,(
% 2.92/0.86    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f7])).
% 2.92/0.86  
% 2.92/0.86  fof(f82,plain,(
% 2.92/0.86    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.92/0.86    inference(definition_unfolding,[],[f48,f49])).
% 2.92/0.86  
% 2.92/0.86  fof(f83,plain,(
% 2.92/0.86    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.92/0.86    inference(definition_unfolding,[],[f47,f82])).
% 2.92/0.86  
% 2.92/0.86  fof(f84,plain,(
% 2.92/0.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.92/0.86    inference(definition_unfolding,[],[f46,f83])).
% 2.92/0.86  
% 2.92/0.86  fof(f85,plain,(
% 2.92/0.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.92/0.86    inference(definition_unfolding,[],[f45,f84])).
% 2.92/0.86  
% 2.92/0.86  fof(f86,plain,(
% 2.92/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.92/0.86    inference(definition_unfolding,[],[f44,f85])).
% 2.92/0.86  
% 2.92/0.86  fof(f87,plain,(
% 2.92/0.86    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.92/0.86    inference(definition_unfolding,[],[f43,f86])).
% 2.92/0.86  
% 2.92/0.86  fof(f90,plain,(
% 2.92/0.86    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))),
% 2.92/0.86    inference(definition_unfolding,[],[f79,f87])).
% 2.92/0.86  
% 2.92/0.86  fof(f78,plain,(
% 2.92/0.86    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 2.92/0.86    inference(cnf_transformation,[],[f42])).
% 2.92/0.86  
% 2.92/0.86  fof(f91,plain,(
% 2.92/0.86    v1_funct_2(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)),
% 2.92/0.86    inference(definition_unfolding,[],[f78,f87])).
% 2.92/0.86  
% 2.92/0.86  fof(f15,axiom,(
% 2.92/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f25,plain,(
% 2.92/0.86    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.86    inference(ennf_transformation,[],[f15])).
% 2.92/0.86  
% 2.92/0.86  fof(f26,plain,(
% 2.92/0.86    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.86    inference(flattening,[],[f25])).
% 2.92/0.86  
% 2.92/0.86  fof(f40,plain,(
% 2.92/0.86    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.86    inference(nnf_transformation,[],[f26])).
% 2.92/0.86  
% 2.92/0.86  fof(f71,plain,(
% 2.92/0.86    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.86    inference(cnf_transformation,[],[f40])).
% 2.92/0.86  
% 2.92/0.86  fof(f80,plain,(
% 2.92/0.86    k1_xboole_0 != sK4),
% 2.92/0.86    inference(cnf_transformation,[],[f42])).
% 2.92/0.86  
% 2.92/0.86  fof(f8,axiom,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f18,plain,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 2.92/0.86    inference(ennf_transformation,[],[f8])).
% 2.92/0.86  
% 2.92/0.86  fof(f30,plain,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.92/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.92/0.86  
% 2.92/0.86  fof(f29,plain,(
% 2.92/0.86    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.92/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.92/0.86  
% 2.92/0.86  fof(f31,plain,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 2.92/0.86    inference(definition_folding,[],[f18,f30,f29])).
% 2.92/0.86  
% 2.92/0.86  fof(f39,plain,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 2.92/0.86    inference(nnf_transformation,[],[f31])).
% 2.92/0.86  
% 2.92/0.86  fof(f63,plain,(
% 2.92/0.86    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 2.92/0.86    inference(cnf_transformation,[],[f39])).
% 2.92/0.86  
% 2.92/0.86  fof(f100,plain,(
% 2.92/0.86    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.92/0.86    inference(equality_resolution,[],[f63])).
% 2.92/0.86  
% 2.92/0.86  fof(f36,plain,(
% 2.92/0.86    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.92/0.86    inference(nnf_transformation,[],[f29])).
% 2.92/0.86  
% 2.92/0.86  fof(f37,plain,(
% 2.92/0.86    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.92/0.86    inference(flattening,[],[f36])).
% 2.92/0.86  
% 2.92/0.86  fof(f38,plain,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.92/0.86    inference(rectify,[],[f37])).
% 2.92/0.86  
% 2.92/0.86  fof(f62,plain,(
% 2.92/0.86    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 2.92/0.86    inference(cnf_transformation,[],[f38])).
% 2.92/0.86  
% 2.92/0.86  fof(f92,plain,(
% 2.92/0.86    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.92/0.86    inference(equality_resolution,[],[f62])).
% 2.92/0.86  
% 2.92/0.86  fof(f32,plain,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.92/0.86    inference(nnf_transformation,[],[f30])).
% 2.92/0.86  
% 2.92/0.86  fof(f33,plain,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.92/0.86    inference(rectify,[],[f32])).
% 2.92/0.86  
% 2.92/0.86  fof(f34,plain,(
% 2.92/0.86    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 2.92/0.86    introduced(choice_axiom,[])).
% 2.92/0.86  
% 2.92/0.86  fof(f35,plain,(
% 2.92/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.92/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 2.92/0.86  
% 2.92/0.86  fof(f51,plain,(
% 2.92/0.86    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f35])).
% 2.92/0.86  
% 2.92/0.86  fof(f12,axiom,(
% 2.92/0.86    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))))),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f21,plain,(
% 2.92/0.86    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.92/0.86    inference(ennf_transformation,[],[f12])).
% 2.92/0.86  
% 2.92/0.86  fof(f22,plain,(
% 2.92/0.86    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.92/0.86    inference(flattening,[],[f21])).
% 2.92/0.86  
% 2.92/0.86  fof(f68,plain,(
% 2.92/0.86    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f22])).
% 2.92/0.86  
% 2.92/0.86  fof(f88,plain,(
% 2.92/0.86    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.92/0.86    inference(definition_unfolding,[],[f68,f87,f87])).
% 2.92/0.86  
% 2.92/0.86  fof(f77,plain,(
% 2.92/0.86    v1_funct_1(sK5)),
% 2.92/0.86    inference(cnf_transformation,[],[f42])).
% 2.92/0.86  
% 2.92/0.86  fof(f9,axiom,(
% 2.92/0.86    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f19,plain,(
% 2.92/0.86    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.92/0.86    inference(ennf_transformation,[],[f9])).
% 2.92/0.86  
% 2.92/0.86  fof(f65,plain,(
% 2.92/0.86    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f19])).
% 2.92/0.86  
% 2.92/0.86  fof(f10,axiom,(
% 2.92/0.86    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f66,plain,(
% 2.92/0.86    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.92/0.86    inference(cnf_transformation,[],[f10])).
% 2.92/0.86  
% 2.92/0.86  fof(f11,axiom,(
% 2.92/0.86    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f20,plain,(
% 2.92/0.86    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.92/0.86    inference(ennf_transformation,[],[f11])).
% 2.92/0.86  
% 2.92/0.86  fof(f67,plain,(
% 2.92/0.86    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 2.92/0.86    inference(cnf_transformation,[],[f20])).
% 2.92/0.86  
% 2.92/0.86  fof(f14,axiom,(
% 2.92/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.92/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.86  
% 2.92/0.86  fof(f24,plain,(
% 2.92/0.86    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.86    inference(ennf_transformation,[],[f14])).
% 2.92/0.86  
% 2.92/0.86  fof(f70,plain,(
% 2.92/0.86    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.86    inference(cnf_transformation,[],[f24])).
% 2.92/0.86  
% 2.92/0.86  fof(f81,plain,(
% 2.92/0.86    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 2.92/0.86    inference(cnf_transformation,[],[f42])).
% 2.92/0.86  
% 2.92/0.86  fof(f89,plain,(
% 2.92/0.86    k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5)),
% 2.92/0.86    inference(definition_unfolding,[],[f81,f87,f87])).
% 2.92/0.86  
% 2.92/0.86  cnf(c_19,plain,
% 2.92/0.86      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.86      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.92/0.86      inference(cnf_transformation,[],[f69]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_29,negated_conjecture,
% 2.92/0.86      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
% 2.92/0.86      inference(cnf_transformation,[],[f90]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_409,plain,
% 2.92/0.86      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.92/0.86      | sK5 != X2 ),
% 2.92/0.86      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_410,plain,
% 2.92/0.86      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.92/0.86      inference(unflattening,[status(thm)],[c_409]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2541,plain,
% 2.92/0.86      ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k1_relat_1(sK5) ),
% 2.92/0.86      inference(equality_resolution,[status(thm)],[c_410]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_30,negated_conjecture,
% 2.92/0.86      ( v1_funct_2(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) ),
% 2.92/0.86      inference(cnf_transformation,[],[f91]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_26,plain,
% 2.92/0.86      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.86      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.86      | k1_relset_1(X1,X2,X0) = X1
% 2.92/0.86      | k1_xboole_0 = X2 ),
% 2.92/0.86      inference(cnf_transformation,[],[f71]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_364,plain,
% 2.92/0.86      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.86      | k1_relset_1(X1,X2,X0) = X1
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.92/0.86      | sK5 != X0
% 2.92/0.86      | k1_xboole_0 = X2 ),
% 2.92/0.86      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_365,plain,
% 2.92/0.86      ( ~ v1_funct_2(sK5,X0,X1)
% 2.92/0.86      | k1_relset_1(X0,X1,sK5) = X0
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.92/0.86      | k1_xboole_0 = X1 ),
% 2.92/0.86      inference(unflattening,[status(thm)],[c_364]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_777,plain,
% 2.92/0.86      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
% 2.92/0.86      | k1_relset_1(X0,X1,sK5) = X0
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.92/0.86      | sK4 != X1
% 2.92/0.86      | sK5 != sK5
% 2.92/0.86      | k1_xboole_0 = X1 ),
% 2.92/0.86      inference(resolution_lifted,[status(thm)],[c_30,c_365]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_778,plain,
% 2.92/0.86      ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
% 2.92/0.86      | k1_xboole_0 = sK4 ),
% 2.92/0.86      inference(unflattening,[status(thm)],[c_777]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_28,negated_conjecture,
% 2.92/0.86      ( k1_xboole_0 != sK4 ),
% 2.92/0.86      inference(cnf_transformation,[],[f80]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_779,plain,
% 2.92/0.86      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
% 2.92/0.86      | k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 2.92/0.86      inference(global_propositional_subsumption,
% 2.92/0.86                [status(thm)],
% 2.92/0.86                [c_778,c_28]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_780,plain,
% 2.92/0.86      ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
% 2.92/0.86      inference(renaming,[status(thm)],[c_779]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_1243,plain,
% 2.92/0.86      ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 2.92/0.86      inference(equality_resolution_simp,[status(thm)],[c_780]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2919,plain,
% 2.92/0.86      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK5) ),
% 2.92/0.86      inference(demodulation,[status(thm)],[c_2541,c_1243]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_14,plain,
% 2.92/0.86      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.92/0.86      inference(cnf_transformation,[],[f100]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2337,plain,
% 2.92/0.86      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 2.92/0.86      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_3553,plain,
% 2.92/0.86      ( sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k1_relat_1(sK5)) = iProver_top ),
% 2.92/0.86      inference(superposition,[status(thm)],[c_2919,c_2337]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_4,plain,
% 2.92/0.86      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 2.92/0.86      inference(cnf_transformation,[],[f92]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2347,plain,
% 2.92/0.86      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 2.92/0.86      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2,plain,
% 2.92/0.86      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.92/0.86      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.92/0.86      | r2_hidden(X0,X9) ),
% 2.92/0.86      inference(cnf_transformation,[],[f51]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2349,plain,
% 2.92/0.86      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.92/0.86      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 2.92/0.86      | r2_hidden(X0,X9) = iProver_top ),
% 2.92/0.86      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_4687,plain,
% 2.92/0.86      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.92/0.86      | r2_hidden(X7,X8) = iProver_top ),
% 2.92/0.86      inference(superposition,[status(thm)],[c_2347,c_2349]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_5824,plain,
% 2.92/0.86      ( r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top ),
% 2.92/0.86      inference(superposition,[status(thm)],[c_3553,c_4687]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_18,plain,
% 2.92/0.86      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.92/0.86      | ~ v1_funct_1(X1)
% 2.92/0.86      | ~ v1_relat_1(X1)
% 2.92/0.86      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
% 2.92/0.86      inference(cnf_transformation,[],[f88]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_31,negated_conjecture,
% 2.92/0.86      ( v1_funct_1(sK5) ),
% 2.92/0.86      inference(cnf_transformation,[],[f77]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_330,plain,
% 2.92/0.86      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.92/0.86      | ~ v1_relat_1(X1)
% 2.92/0.86      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 2.92/0.86      | sK5 != X1 ),
% 2.92/0.86      inference(resolution_lifted,[status(thm)],[c_18,c_31]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_331,plain,
% 2.92/0.86      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.92/0.86      | ~ v1_relat_1(sK5)
% 2.92/0.86      | k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
% 2.92/0.86      inference(unflattening,[status(thm)],[c_330]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2334,plain,
% 2.92/0.86      ( k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 2.92/0.86      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.92/0.86      | v1_relat_1(sK5) != iProver_top ),
% 2.92/0.86      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_6128,plain,
% 2.92/0.86      ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
% 2.92/0.86      | v1_relat_1(sK5) != iProver_top ),
% 2.92/0.86      inference(superposition,[status(thm)],[c_5824,c_2334]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_15,plain,
% 2.92/0.86      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.92/0.86      | ~ v1_relat_1(X1)
% 2.92/0.86      | v1_relat_1(X0) ),
% 2.92/0.86      inference(cnf_transformation,[],[f65]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_349,plain,
% 2.92/0.86      ( ~ v1_relat_1(X0)
% 2.92/0.86      | v1_relat_1(X1)
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
% 2.92/0.86      | sK5 != X1 ),
% 2.92/0.86      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_350,plain,
% 2.92/0.86      ( ~ v1_relat_1(X0)
% 2.92/0.86      | v1_relat_1(sK5)
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0) ),
% 2.92/0.86      inference(unflattening,[status(thm)],[c_349]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2333,plain,
% 2.92/0.86      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
% 2.92/0.86      | v1_relat_1(X0) != iProver_top
% 2.92/0.86      | v1_relat_1(sK5) = iProver_top ),
% 2.92/0.86      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_3062,plain,
% 2.92/0.86      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != iProver_top
% 2.92/0.86      | v1_relat_1(sK5) = iProver_top ),
% 2.92/0.86      inference(equality_resolution,[status(thm)],[c_2333]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_16,plain,
% 2.92/0.86      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.92/0.86      inference(cnf_transformation,[],[f66]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_3877,plain,
% 2.92/0.86      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
% 2.92/0.86      inference(instantiation,[status(thm)],[c_16]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_3878,plain,
% 2.92/0.86      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) = iProver_top ),
% 2.92/0.86      inference(predicate_to_equality,[status(thm)],[c_3877]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_4089,plain,
% 2.92/0.86      ( v1_relat_1(sK5) = iProver_top ),
% 2.92/0.86      inference(global_propositional_subsumption,
% 2.92/0.86                [status(thm)],
% 2.92/0.86                [c_3062,c_3878]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_17,plain,
% 2.92/0.86      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 2.92/0.86      inference(cnf_transformation,[],[f67]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2335,plain,
% 2.92/0.86      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.92/0.86      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.86      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_4094,plain,
% 2.92/0.86      ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
% 2.92/0.86      inference(superposition,[status(thm)],[c_4089,c_2335]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_6131,plain,
% 2.92/0.86      ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
% 2.92/0.86      | v1_relat_1(sK5) != iProver_top ),
% 2.92/0.86      inference(light_normalisation,[status(thm)],[c_6128,c_2919,c_4094]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_20,plain,
% 2.92/0.86      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.86      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.92/0.86      inference(cnf_transformation,[],[f70]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_400,plain,
% 2.92/0.86      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.92/0.86      | sK5 != X2 ),
% 2.92/0.86      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_401,plain,
% 2.92/0.86      ( k2_relset_1(X0,X1,sK5) = k2_relat_1(sK5)
% 2.92/0.86      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.92/0.86      inference(unflattening,[status(thm)],[c_400]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2538,plain,
% 2.92/0.86      ( k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 2.92/0.86      inference(equality_resolution,[status(thm)],[c_401]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_27,negated_conjecture,
% 2.92/0.86      ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) ),
% 2.92/0.86      inference(cnf_transformation,[],[f89]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(c_2581,plain,
% 2.92/0.86      ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
% 2.92/0.86      inference(demodulation,[status(thm)],[c_2538,c_27]) ).
% 2.92/0.86  
% 2.92/0.86  cnf(contradiction,plain,
% 2.92/0.86      ( $false ),
% 2.92/0.86      inference(minisat,[status(thm)],[c_6131,c_3878,c_3062,c_2581]) ).
% 2.92/0.86  
% 2.92/0.86  
% 2.92/0.86  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/0.86  
% 2.92/0.86  ------                               Statistics
% 2.92/0.86  
% 2.92/0.86  ------ General
% 2.92/0.86  
% 2.92/0.86  abstr_ref_over_cycles:                  0
% 2.92/0.86  abstr_ref_under_cycles:                 0
% 2.92/0.86  gc_basic_clause_elim:                   0
% 2.92/0.86  forced_gc_time:                         0
% 2.92/0.86  parsing_time:                           0.008
% 2.92/0.86  unif_index_cands_time:                  0.
% 2.92/0.86  unif_index_add_time:                    0.
% 2.92/0.86  orderings_time:                         0.
% 2.92/0.86  out_proof_time:                         0.009
% 2.92/0.86  total_time:                             0.233
% 2.92/0.86  num_of_symbols:                         52
% 2.92/0.86  num_of_terms:                           6148
% 2.92/0.86  
% 2.92/0.86  ------ Preprocessing
% 2.92/0.86  
% 2.92/0.86  num_of_splits:                          0
% 2.92/0.86  num_of_split_atoms:                     0
% 2.92/0.86  num_of_reused_defs:                     0
% 2.92/0.86  num_eq_ax_congr_red:                    79
% 2.92/0.86  num_of_sem_filtered_clauses:            1
% 2.92/0.86  num_of_subtypes:                        0
% 2.92/0.86  monotx_restored_types:                  0
% 2.92/0.86  sat_num_of_epr_types:                   0
% 2.92/0.86  sat_num_of_non_cyclic_types:            0
% 2.92/0.86  sat_guarded_non_collapsed_types:        0
% 2.92/0.86  num_pure_diseq_elim:                    0
% 2.92/0.86  simp_replaced_by:                       0
% 2.92/0.86  res_preprocessed:                       141
% 2.92/0.86  prep_upred:                             0
% 2.92/0.86  prep_unflattend:                        638
% 2.92/0.86  smt_new_axioms:                         0
% 2.92/0.86  pred_elim_cands:                        4
% 2.92/0.86  pred_elim:                              3
% 2.92/0.86  pred_elim_cl:                           6
% 2.92/0.86  pred_elim_cycles:                       9
% 2.92/0.86  merged_defs:                            0
% 2.92/0.86  merged_defs_ncl:                        0
% 2.92/0.86  bin_hyper_res:                          0
% 2.92/0.86  prep_cycles:                            4
% 2.92/0.86  pred_elim_time:                         0.033
% 2.92/0.86  splitting_time:                         0.
% 2.92/0.86  sem_filter_time:                        0.
% 2.92/0.86  monotx_time:                            0.
% 2.92/0.86  subtype_inf_time:                       0.
% 2.92/0.86  
% 2.92/0.86  ------ Problem properties
% 2.92/0.86  
% 2.92/0.86  clauses:                                26
% 2.92/0.86  conjectures:                            2
% 2.92/0.86  epr:                                    12
% 2.92/0.86  horn:                                   23
% 2.92/0.86  ground:                                 5
% 2.92/0.86  unary:                                  13
% 2.92/0.86  binary:                                 4
% 2.92/0.86  lits:                                   55
% 2.92/0.86  lits_eq:                                26
% 2.92/0.86  fd_pure:                                0
% 2.92/0.86  fd_pseudo:                              0
% 2.92/0.86  fd_cond:                                0
% 2.92/0.86  fd_pseudo_cond:                         2
% 2.92/0.86  ac_symbols:                             0
% 2.92/0.86  
% 2.92/0.86  ------ Propositional Solver
% 2.92/0.86  
% 2.92/0.86  prop_solver_calls:                      26
% 2.92/0.86  prop_fast_solver_calls:                 1089
% 2.92/0.86  smt_solver_calls:                       0
% 2.92/0.86  smt_fast_solver_calls:                  0
% 2.92/0.86  prop_num_of_clauses:                    1753
% 2.92/0.86  prop_preprocess_simplified:             7025
% 2.92/0.86  prop_fo_subsumed:                       5
% 2.92/0.86  prop_solver_time:                       0.
% 2.92/0.86  smt_solver_time:                        0.
% 2.92/0.86  smt_fast_solver_time:                   0.
% 2.92/0.86  prop_fast_solver_time:                  0.
% 2.92/0.86  prop_unsat_core_time:                   0.
% 2.92/0.86  
% 2.92/0.86  ------ QBF
% 2.92/0.86  
% 2.92/0.86  qbf_q_res:                              0
% 2.92/0.86  qbf_num_tautologies:                    0
% 2.92/0.86  qbf_prep_cycles:                        0
% 2.92/0.86  
% 2.92/0.86  ------ BMC1
% 2.92/0.86  
% 2.92/0.86  bmc1_current_bound:                     -1
% 2.92/0.86  bmc1_last_solved_bound:                 -1
% 2.92/0.86  bmc1_unsat_core_size:                   -1
% 2.92/0.86  bmc1_unsat_core_parents_size:           -1
% 2.92/0.86  bmc1_merge_next_fun:                    0
% 2.92/0.86  bmc1_unsat_core_clauses_time:           0.
% 2.92/0.86  
% 2.92/0.86  ------ Instantiation
% 2.92/0.86  
% 2.92/0.86  inst_num_of_clauses:                    512
% 2.92/0.86  inst_num_in_passive:                    143
% 2.92/0.86  inst_num_in_active:                     218
% 2.92/0.86  inst_num_in_unprocessed:                151
% 2.92/0.86  inst_num_of_loops:                      260
% 2.92/0.86  inst_num_of_learning_restarts:          0
% 2.92/0.86  inst_num_moves_active_passive:          41
% 2.92/0.86  inst_lit_activity:                      0
% 2.92/0.86  inst_lit_activity_moves:                0
% 2.92/0.86  inst_num_tautologies:                   0
% 2.92/0.86  inst_num_prop_implied:                  0
% 2.92/0.86  inst_num_existing_simplified:           0
% 2.92/0.86  inst_num_eq_res_simplified:             0
% 2.92/0.86  inst_num_child_elim:                    0
% 2.92/0.86  inst_num_of_dismatching_blockings:      192
% 2.92/0.86  inst_num_of_non_proper_insts:           531
% 2.92/0.86  inst_num_of_duplicates:                 0
% 2.92/0.86  inst_inst_num_from_inst_to_res:         0
% 2.92/0.86  inst_dismatching_checking_time:         0.
% 2.92/0.86  
% 2.92/0.86  ------ Resolution
% 2.92/0.86  
% 2.92/0.86  res_num_of_clauses:                     0
% 2.92/0.86  res_num_in_passive:                     0
% 2.92/0.86  res_num_in_active:                      0
% 2.92/0.86  res_num_of_loops:                       145
% 2.92/0.86  res_forward_subset_subsumed:            291
% 2.92/0.86  res_backward_subset_subsumed:           0
% 2.92/0.86  res_forward_subsumed:                   0
% 2.92/0.86  res_backward_subsumed:                  0
% 2.92/0.86  res_forward_subsumption_resolution:     0
% 2.92/0.86  res_backward_subsumption_resolution:    0
% 2.92/0.86  res_clause_to_clause_subsumption:       1326
% 2.92/0.86  res_orphan_elimination:                 0
% 2.92/0.86  res_tautology_del:                      58
% 2.92/0.86  res_num_eq_res_simplified:              1
% 2.92/0.86  res_num_sel_changes:                    0
% 2.92/0.86  res_moves_from_active_to_pass:          0
% 2.92/0.86  
% 2.92/0.86  ------ Superposition
% 2.92/0.86  
% 2.92/0.86  sup_time_total:                         0.
% 2.92/0.86  sup_time_generating:                    0.
% 2.92/0.86  sup_time_sim_full:                      0.
% 2.92/0.86  sup_time_sim_immed:                     0.
% 2.92/0.86  
% 2.92/0.86  sup_num_of_clauses:                     65
% 2.92/0.86  sup_num_in_active:                      43
% 2.92/0.86  sup_num_in_passive:                     22
% 2.92/0.86  sup_num_of_loops:                       51
% 2.92/0.86  sup_fw_superposition:                   38
% 2.92/0.86  sup_bw_superposition:                   16
% 2.92/0.86  sup_immediate_simplified:               1
% 2.92/0.86  sup_given_eliminated:                   0
% 2.92/0.86  comparisons_done:                       0
% 2.92/0.86  comparisons_avoided:                    96
% 2.92/0.86  
% 2.92/0.86  ------ Simplifications
% 2.92/0.86  
% 2.92/0.86  
% 2.92/0.86  sim_fw_subset_subsumed:                 0
% 2.92/0.86  sim_bw_subset_subsumed:                 0
% 2.92/0.86  sim_fw_subsumed:                        0
% 2.92/0.86  sim_bw_subsumed:                        0
% 2.92/0.86  sim_fw_subsumption_res:                 0
% 2.92/0.86  sim_bw_subsumption_res:                 0
% 2.92/0.86  sim_tautology_del:                      4
% 2.92/0.86  sim_eq_tautology_del:                   4
% 2.92/0.86  sim_eq_res_simp:                        0
% 2.92/0.86  sim_fw_demodulated:                     0
% 2.92/0.86  sim_bw_demodulated:                     9
% 2.92/0.86  sim_light_normalised:                   1
% 2.92/0.86  sim_joinable_taut:                      0
% 2.92/0.86  sim_joinable_simp:                      0
% 2.92/0.86  sim_ac_normalised:                      0
% 2.92/0.86  sim_smt_subsumption:                    0
% 2.92/0.86  
%------------------------------------------------------------------------------
