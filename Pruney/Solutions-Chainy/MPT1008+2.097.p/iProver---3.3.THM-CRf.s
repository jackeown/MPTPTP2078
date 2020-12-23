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
% DateTime   : Thu Dec  3 12:05:24 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 693 expanded)
%              Number of clauses        :   58 ( 107 expanded)
%              Number of leaves         :   21 ( 186 expanded)
%              Depth                    :   22
%              Number of atoms          :  438 (1690 expanded)
%              Number of equality atoms :  246 ( 988 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,
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

fof(f46,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f45])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f87])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f88])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f89])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f90])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f91])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f84,f92])).

fof(f83,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    v1_funct_2(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f83,f92])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f33,plain,(
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

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f20,f34,f33])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f67])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f66])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f72,f92,f92])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f86,f92,f92])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_453,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_454,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_2583,plain,
    ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k1_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_454])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_408,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_409,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_825,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X1
    | sK5 != sK5
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_409])).

cnf(c_826,plain,
    ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_827,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
    | k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_29])).

cnf(c_828,plain,
    ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_827])).

cnf(c_1291,plain,
    ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_828])).

cnf(c_2954,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2583,c_1291])).

cnf(c_14,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2382,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3642,plain,
    ( sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2954,c_2382])).

cnf(c_4,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2392,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2394,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4833,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_2394])).

cnf(c_5040,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3642,c_4833])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_32])).

cnf(c_360,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_2380,plain,
    ( k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_5203,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5040,c_2380])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_19,c_17])).

cnf(c_393,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_341,c_30])).

cnf(c_394,plain,
    ( ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,X0) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_2378,plain,
    ( k7_relat_1(sK5,X0) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_378,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_379,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_2553,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_3179,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k7_relat_1(sK5,X0) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2378,c_16,c_394,c_2553])).

cnf(c_3180,plain,
    ( k7_relat_1(sK5,X0) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(renaming,[status(thm)],[c_3179])).

cnf(c_3184,plain,
    ( k7_relat_1(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK5 ),
    inference(equality_resolution,[status(thm)],[c_3180])).

cnf(c_4125,plain,
    ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_3184,c_2954])).

cnf(c_5206,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5203,c_2954,c_4125])).

cnf(c_3923,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3924,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3923])).

cnf(c_2379,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_3176,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2379])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_444,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_445,plain,
    ( k2_relset_1(X0,X1,sK5) = k2_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_2580,plain,
    ( k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_445])).

cnf(c_28,negated_conjecture,
    ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2623,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2580,c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5206,c_3924,c_3176,c_2623])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.25/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/0.98  
% 3.25/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/0.98  
% 3.25/0.98  ------  iProver source info
% 3.25/0.98  
% 3.25/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.25/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/0.98  git: non_committed_changes: false
% 3.25/0.98  git: last_make_outside_of_git: false
% 3.25/0.98  
% 3.25/0.98  ------ 
% 3.25/0.98  
% 3.25/0.98  ------ Input Options
% 3.25/0.98  
% 3.25/0.98  --out_options                           all
% 3.25/0.98  --tptp_safe_out                         true
% 3.25/0.98  --problem_path                          ""
% 3.25/0.98  --include_path                          ""
% 3.25/0.98  --clausifier                            res/vclausify_rel
% 3.25/0.98  --clausifier_options                    --mode clausify
% 3.25/0.98  --stdin                                 false
% 3.25/0.98  --stats_out                             all
% 3.25/0.98  
% 3.25/0.98  ------ General Options
% 3.25/0.98  
% 3.25/0.98  --fof                                   false
% 3.25/0.98  --time_out_real                         305.
% 3.25/0.98  --time_out_virtual                      -1.
% 3.25/0.98  --symbol_type_check                     false
% 3.25/0.98  --clausify_out                          false
% 3.25/0.98  --sig_cnt_out                           false
% 3.25/0.98  --trig_cnt_out                          false
% 3.25/0.98  --trig_cnt_out_tolerance                1.
% 3.25/0.98  --trig_cnt_out_sk_spl                   false
% 3.25/0.98  --abstr_cl_out                          false
% 3.25/0.98  
% 3.25/0.98  ------ Global Options
% 3.25/0.98  
% 3.25/0.98  --schedule                              default
% 3.25/0.98  --add_important_lit                     false
% 3.25/0.98  --prop_solver_per_cl                    1000
% 3.25/0.98  --min_unsat_core                        false
% 3.25/0.98  --soft_assumptions                      false
% 3.25/0.98  --soft_lemma_size                       3
% 3.25/0.98  --prop_impl_unit_size                   0
% 3.25/0.98  --prop_impl_unit                        []
% 3.25/0.98  --share_sel_clauses                     true
% 3.25/0.98  --reset_solvers                         false
% 3.25/0.98  --bc_imp_inh                            [conj_cone]
% 3.25/0.98  --conj_cone_tolerance                   3.
% 3.25/0.98  --extra_neg_conj                        none
% 3.25/0.98  --large_theory_mode                     true
% 3.25/0.98  --prolific_symb_bound                   200
% 3.25/0.98  --lt_threshold                          2000
% 3.25/0.98  --clause_weak_htbl                      true
% 3.25/0.98  --gc_record_bc_elim                     false
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing Options
% 3.25/0.98  
% 3.25/0.98  --preprocessing_flag                    true
% 3.25/0.98  --time_out_prep_mult                    0.1
% 3.25/0.98  --splitting_mode                        input
% 3.25/0.98  --splitting_grd                         true
% 3.25/0.98  --splitting_cvd                         false
% 3.25/0.98  --splitting_cvd_svl                     false
% 3.25/0.98  --splitting_nvd                         32
% 3.25/0.98  --sub_typing                            true
% 3.25/0.98  --prep_gs_sim                           true
% 3.25/0.98  --prep_unflatten                        true
% 3.25/0.98  --prep_res_sim                          true
% 3.25/0.98  --prep_upred                            true
% 3.25/0.98  --prep_sem_filter                       exhaustive
% 3.25/0.98  --prep_sem_filter_out                   false
% 3.25/0.98  --pred_elim                             true
% 3.25/0.98  --res_sim_input                         true
% 3.25/0.98  --eq_ax_congr_red                       true
% 3.25/0.98  --pure_diseq_elim                       true
% 3.25/0.98  --brand_transform                       false
% 3.25/0.98  --non_eq_to_eq                          false
% 3.25/0.98  --prep_def_merge                        true
% 3.25/0.98  --prep_def_merge_prop_impl              false
% 3.25/0.98  --prep_def_merge_mbd                    true
% 3.25/0.98  --prep_def_merge_tr_red                 false
% 3.25/0.98  --prep_def_merge_tr_cl                  false
% 3.25/0.98  --smt_preprocessing                     true
% 3.25/0.98  --smt_ac_axioms                         fast
% 3.25/0.98  --preprocessed_out                      false
% 3.25/0.98  --preprocessed_stats                    false
% 3.25/0.98  
% 3.25/0.98  ------ Abstraction refinement Options
% 3.25/0.98  
% 3.25/0.98  --abstr_ref                             []
% 3.25/0.98  --abstr_ref_prep                        false
% 3.25/0.98  --abstr_ref_until_sat                   false
% 3.25/0.98  --abstr_ref_sig_restrict                funpre
% 3.25/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.98  --abstr_ref_under                       []
% 3.25/0.98  
% 3.25/0.98  ------ SAT Options
% 3.25/0.98  
% 3.25/0.98  --sat_mode                              false
% 3.25/0.98  --sat_fm_restart_options                ""
% 3.25/0.98  --sat_gr_def                            false
% 3.25/0.98  --sat_epr_types                         true
% 3.25/0.98  --sat_non_cyclic_types                  false
% 3.25/0.98  --sat_finite_models                     false
% 3.25/0.98  --sat_fm_lemmas                         false
% 3.25/0.98  --sat_fm_prep                           false
% 3.25/0.98  --sat_fm_uc_incr                        true
% 3.25/0.98  --sat_out_model                         small
% 3.25/0.98  --sat_out_clauses                       false
% 3.25/0.98  
% 3.25/0.98  ------ QBF Options
% 3.25/0.98  
% 3.25/0.98  --qbf_mode                              false
% 3.25/0.98  --qbf_elim_univ                         false
% 3.25/0.98  --qbf_dom_inst                          none
% 3.25/0.98  --qbf_dom_pre_inst                      false
% 3.25/0.98  --qbf_sk_in                             false
% 3.25/0.98  --qbf_pred_elim                         true
% 3.25/0.98  --qbf_split                             512
% 3.25/0.98  
% 3.25/0.98  ------ BMC1 Options
% 3.25/0.98  
% 3.25/0.98  --bmc1_incremental                      false
% 3.25/0.98  --bmc1_axioms                           reachable_all
% 3.25/0.98  --bmc1_min_bound                        0
% 3.25/0.98  --bmc1_max_bound                        -1
% 3.25/0.98  --bmc1_max_bound_default                -1
% 3.25/0.98  --bmc1_symbol_reachability              true
% 3.25/0.98  --bmc1_property_lemmas                  false
% 3.25/0.98  --bmc1_k_induction                      false
% 3.25/0.98  --bmc1_non_equiv_states                 false
% 3.25/0.98  --bmc1_deadlock                         false
% 3.25/0.98  --bmc1_ucm                              false
% 3.25/0.98  --bmc1_add_unsat_core                   none
% 3.25/0.98  --bmc1_unsat_core_children              false
% 3.25/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.98  --bmc1_out_stat                         full
% 3.25/0.98  --bmc1_ground_init                      false
% 3.25/0.98  --bmc1_pre_inst_next_state              false
% 3.25/0.98  --bmc1_pre_inst_state                   false
% 3.25/0.98  --bmc1_pre_inst_reach_state             false
% 3.25/0.98  --bmc1_out_unsat_core                   false
% 3.25/0.98  --bmc1_aig_witness_out                  false
% 3.25/0.98  --bmc1_verbose                          false
% 3.25/0.98  --bmc1_dump_clauses_tptp                false
% 3.25/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.98  --bmc1_dump_file                        -
% 3.25/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.98  --bmc1_ucm_extend_mode                  1
% 3.25/0.98  --bmc1_ucm_init_mode                    2
% 3.25/0.98  --bmc1_ucm_cone_mode                    none
% 3.25/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.98  --bmc1_ucm_relax_model                  4
% 3.25/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.98  --bmc1_ucm_layered_model                none
% 3.25/0.98  --bmc1_ucm_max_lemma_size               10
% 3.25/0.98  
% 3.25/0.98  ------ AIG Options
% 3.25/0.98  
% 3.25/0.98  --aig_mode                              false
% 3.25/0.98  
% 3.25/0.98  ------ Instantiation Options
% 3.25/0.98  
% 3.25/0.98  --instantiation_flag                    true
% 3.25/0.98  --inst_sos_flag                         false
% 3.25/0.98  --inst_sos_phase                        true
% 3.25/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.98  --inst_lit_sel_side                     num_symb
% 3.25/0.98  --inst_solver_per_active                1400
% 3.25/0.98  --inst_solver_calls_frac                1.
% 3.25/0.98  --inst_passive_queue_type               priority_queues
% 3.25/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.98  --inst_passive_queues_freq              [25;2]
% 3.25/0.98  --inst_dismatching                      true
% 3.25/0.98  --inst_eager_unprocessed_to_passive     true
% 3.25/0.98  --inst_prop_sim_given                   true
% 3.25/0.98  --inst_prop_sim_new                     false
% 3.25/0.98  --inst_subs_new                         false
% 3.25/0.98  --inst_eq_res_simp                      false
% 3.25/0.98  --inst_subs_given                       false
% 3.25/0.98  --inst_orphan_elimination               true
% 3.25/0.98  --inst_learning_loop_flag               true
% 3.25/0.98  --inst_learning_start                   3000
% 3.25/0.98  --inst_learning_factor                  2
% 3.25/0.98  --inst_start_prop_sim_after_learn       3
% 3.25/0.98  --inst_sel_renew                        solver
% 3.25/0.98  --inst_lit_activity_flag                true
% 3.25/0.98  --inst_restr_to_given                   false
% 3.25/0.98  --inst_activity_threshold               500
% 3.25/0.98  --inst_out_proof                        true
% 3.25/0.98  
% 3.25/0.98  ------ Resolution Options
% 3.25/0.98  
% 3.25/0.98  --resolution_flag                       true
% 3.25/0.98  --res_lit_sel                           adaptive
% 3.25/0.98  --res_lit_sel_side                      none
% 3.25/0.98  --res_ordering                          kbo
% 3.25/0.98  --res_to_prop_solver                    active
% 3.25/0.98  --res_prop_simpl_new                    false
% 3.25/0.98  --res_prop_simpl_given                  true
% 3.25/0.98  --res_passive_queue_type                priority_queues
% 3.25/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.98  --res_passive_queues_freq               [15;5]
% 3.25/0.98  --res_forward_subs                      full
% 3.25/0.98  --res_backward_subs                     full
% 3.25/0.98  --res_forward_subs_resolution           true
% 3.25/0.98  --res_backward_subs_resolution          true
% 3.25/0.98  --res_orphan_elimination                true
% 3.25/0.98  --res_time_limit                        2.
% 3.25/0.98  --res_out_proof                         true
% 3.25/0.98  
% 3.25/0.98  ------ Superposition Options
% 3.25/0.98  
% 3.25/0.98  --superposition_flag                    true
% 3.25/0.98  --sup_passive_queue_type                priority_queues
% 3.25/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.98  --demod_completeness_check              fast
% 3.25/0.98  --demod_use_ground                      true
% 3.25/0.98  --sup_to_prop_solver                    passive
% 3.25/0.98  --sup_prop_simpl_new                    true
% 3.25/0.98  --sup_prop_simpl_given                  true
% 3.25/0.98  --sup_fun_splitting                     false
% 3.25/0.98  --sup_smt_interval                      50000
% 3.25/0.98  
% 3.25/0.98  ------ Superposition Simplification Setup
% 3.25/0.98  
% 3.25/0.98  --sup_indices_passive                   []
% 3.25/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_full_bw                           [BwDemod]
% 3.25/0.98  --sup_immed_triv                        [TrivRules]
% 3.25/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_immed_bw_main                     []
% 3.25/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.98  
% 3.25/0.98  ------ Combination Options
% 3.25/0.98  
% 3.25/0.98  --comb_res_mult                         3
% 3.25/0.98  --comb_sup_mult                         2
% 3.25/0.98  --comb_inst_mult                        10
% 3.25/0.98  
% 3.25/0.98  ------ Debug Options
% 3.25/0.98  
% 3.25/0.98  --dbg_backtrace                         false
% 3.25/0.98  --dbg_dump_prop_clauses                 false
% 3.25/0.98  --dbg_dump_prop_clauses_file            -
% 3.25/0.98  --dbg_out_stat                          false
% 3.25/0.98  ------ Parsing...
% 3.25/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/0.98  ------ Proving...
% 3.25/0.98  ------ Problem Properties 
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  clauses                                 26
% 3.25/0.98  conjectures                             2
% 3.25/0.98  EPR                                     12
% 3.25/0.98  Horn                                    23
% 3.25/0.98  unary                                   13
% 3.25/0.98  binary                                  3
% 3.25/0.98  lits                                    56
% 3.25/0.98  lits eq                                 27
% 3.25/0.98  fd_pure                                 0
% 3.25/0.98  fd_pseudo                               0
% 3.25/0.98  fd_cond                                 0
% 3.25/0.98  fd_pseudo_cond                          2
% 3.25/0.98  AC symbols                              0
% 3.25/0.98  
% 3.25/0.98  ------ Schedule dynamic 5 is on 
% 3.25/0.98  
% 3.25/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  ------ 
% 3.25/0.98  Current options:
% 3.25/0.98  ------ 
% 3.25/0.98  
% 3.25/0.98  ------ Input Options
% 3.25/0.98  
% 3.25/0.98  --out_options                           all
% 3.25/0.98  --tptp_safe_out                         true
% 3.25/0.98  --problem_path                          ""
% 3.25/0.98  --include_path                          ""
% 3.25/0.98  --clausifier                            res/vclausify_rel
% 3.25/0.98  --clausifier_options                    --mode clausify
% 3.25/0.98  --stdin                                 false
% 3.25/0.98  --stats_out                             all
% 3.25/0.98  
% 3.25/0.98  ------ General Options
% 3.25/0.98  
% 3.25/0.98  --fof                                   false
% 3.25/0.98  --time_out_real                         305.
% 3.25/0.98  --time_out_virtual                      -1.
% 3.25/0.98  --symbol_type_check                     false
% 3.25/0.98  --clausify_out                          false
% 3.25/0.98  --sig_cnt_out                           false
% 3.25/0.98  --trig_cnt_out                          false
% 3.25/0.98  --trig_cnt_out_tolerance                1.
% 3.25/0.98  --trig_cnt_out_sk_spl                   false
% 3.25/0.98  --abstr_cl_out                          false
% 3.25/0.98  
% 3.25/0.98  ------ Global Options
% 3.25/0.98  
% 3.25/0.98  --schedule                              default
% 3.25/0.98  --add_important_lit                     false
% 3.25/0.98  --prop_solver_per_cl                    1000
% 3.25/0.98  --min_unsat_core                        false
% 3.25/0.98  --soft_assumptions                      false
% 3.25/0.98  --soft_lemma_size                       3
% 3.25/0.98  --prop_impl_unit_size                   0
% 3.25/0.98  --prop_impl_unit                        []
% 3.25/0.98  --share_sel_clauses                     true
% 3.25/0.98  --reset_solvers                         false
% 3.25/0.98  --bc_imp_inh                            [conj_cone]
% 3.25/0.98  --conj_cone_tolerance                   3.
% 3.25/0.98  --extra_neg_conj                        none
% 3.25/0.98  --large_theory_mode                     true
% 3.25/0.98  --prolific_symb_bound                   200
% 3.25/0.98  --lt_threshold                          2000
% 3.25/0.98  --clause_weak_htbl                      true
% 3.25/0.98  --gc_record_bc_elim                     false
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing Options
% 3.25/0.98  
% 3.25/0.98  --preprocessing_flag                    true
% 3.25/0.98  --time_out_prep_mult                    0.1
% 3.25/0.98  --splitting_mode                        input
% 3.25/0.98  --splitting_grd                         true
% 3.25/0.98  --splitting_cvd                         false
% 3.25/0.98  --splitting_cvd_svl                     false
% 3.25/0.98  --splitting_nvd                         32
% 3.25/0.98  --sub_typing                            true
% 3.25/0.98  --prep_gs_sim                           true
% 3.25/0.98  --prep_unflatten                        true
% 3.25/0.98  --prep_res_sim                          true
% 3.25/0.98  --prep_upred                            true
% 3.25/0.98  --prep_sem_filter                       exhaustive
% 3.25/0.98  --prep_sem_filter_out                   false
% 3.25/0.98  --pred_elim                             true
% 3.25/0.98  --res_sim_input                         true
% 3.25/0.98  --eq_ax_congr_red                       true
% 3.25/0.98  --pure_diseq_elim                       true
% 3.25/0.98  --brand_transform                       false
% 3.25/0.98  --non_eq_to_eq                          false
% 3.25/0.98  --prep_def_merge                        true
% 3.25/0.98  --prep_def_merge_prop_impl              false
% 3.25/0.98  --prep_def_merge_mbd                    true
% 3.25/0.98  --prep_def_merge_tr_red                 false
% 3.25/0.98  --prep_def_merge_tr_cl                  false
% 3.25/0.98  --smt_preprocessing                     true
% 3.25/0.98  --smt_ac_axioms                         fast
% 3.25/0.98  --preprocessed_out                      false
% 3.25/0.98  --preprocessed_stats                    false
% 3.25/0.98  
% 3.25/0.98  ------ Abstraction refinement Options
% 3.25/0.98  
% 3.25/0.98  --abstr_ref                             []
% 3.25/0.98  --abstr_ref_prep                        false
% 3.25/0.98  --abstr_ref_until_sat                   false
% 3.25/0.98  --abstr_ref_sig_restrict                funpre
% 3.25/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.98  --abstr_ref_under                       []
% 3.25/0.98  
% 3.25/0.98  ------ SAT Options
% 3.25/0.98  
% 3.25/0.98  --sat_mode                              false
% 3.25/0.98  --sat_fm_restart_options                ""
% 3.25/0.98  --sat_gr_def                            false
% 3.25/0.98  --sat_epr_types                         true
% 3.25/0.98  --sat_non_cyclic_types                  false
% 3.25/0.98  --sat_finite_models                     false
% 3.25/0.98  --sat_fm_lemmas                         false
% 3.25/0.98  --sat_fm_prep                           false
% 3.25/0.98  --sat_fm_uc_incr                        true
% 3.25/0.98  --sat_out_model                         small
% 3.25/0.98  --sat_out_clauses                       false
% 3.25/0.98  
% 3.25/0.98  ------ QBF Options
% 3.25/0.98  
% 3.25/0.98  --qbf_mode                              false
% 3.25/0.98  --qbf_elim_univ                         false
% 3.25/0.98  --qbf_dom_inst                          none
% 3.25/0.98  --qbf_dom_pre_inst                      false
% 3.25/0.98  --qbf_sk_in                             false
% 3.25/0.98  --qbf_pred_elim                         true
% 3.25/0.98  --qbf_split                             512
% 3.25/0.98  
% 3.25/0.98  ------ BMC1 Options
% 3.25/0.98  
% 3.25/0.98  --bmc1_incremental                      false
% 3.25/0.98  --bmc1_axioms                           reachable_all
% 3.25/0.98  --bmc1_min_bound                        0
% 3.25/0.98  --bmc1_max_bound                        -1
% 3.25/0.98  --bmc1_max_bound_default                -1
% 3.25/0.98  --bmc1_symbol_reachability              true
% 3.25/0.98  --bmc1_property_lemmas                  false
% 3.25/0.98  --bmc1_k_induction                      false
% 3.25/0.98  --bmc1_non_equiv_states                 false
% 3.25/0.98  --bmc1_deadlock                         false
% 3.25/0.98  --bmc1_ucm                              false
% 3.25/0.98  --bmc1_add_unsat_core                   none
% 3.25/0.98  --bmc1_unsat_core_children              false
% 3.25/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.98  --bmc1_out_stat                         full
% 3.25/0.98  --bmc1_ground_init                      false
% 3.25/0.98  --bmc1_pre_inst_next_state              false
% 3.25/0.98  --bmc1_pre_inst_state                   false
% 3.25/0.98  --bmc1_pre_inst_reach_state             false
% 3.25/0.98  --bmc1_out_unsat_core                   false
% 3.25/0.98  --bmc1_aig_witness_out                  false
% 3.25/0.98  --bmc1_verbose                          false
% 3.25/0.98  --bmc1_dump_clauses_tptp                false
% 3.25/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.98  --bmc1_dump_file                        -
% 3.25/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.98  --bmc1_ucm_extend_mode                  1
% 3.25/0.98  --bmc1_ucm_init_mode                    2
% 3.25/0.98  --bmc1_ucm_cone_mode                    none
% 3.25/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.98  --bmc1_ucm_relax_model                  4
% 3.25/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.98  --bmc1_ucm_layered_model                none
% 3.25/0.98  --bmc1_ucm_max_lemma_size               10
% 3.25/0.98  
% 3.25/0.98  ------ AIG Options
% 3.25/0.98  
% 3.25/0.98  --aig_mode                              false
% 3.25/0.98  
% 3.25/0.98  ------ Instantiation Options
% 3.25/0.98  
% 3.25/0.98  --instantiation_flag                    true
% 3.25/0.98  --inst_sos_flag                         false
% 3.25/0.98  --inst_sos_phase                        true
% 3.25/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.98  --inst_lit_sel_side                     none
% 3.25/0.98  --inst_solver_per_active                1400
% 3.25/0.98  --inst_solver_calls_frac                1.
% 3.25/0.98  --inst_passive_queue_type               priority_queues
% 3.25/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.98  --inst_passive_queues_freq              [25;2]
% 3.25/0.98  --inst_dismatching                      true
% 3.25/0.98  --inst_eager_unprocessed_to_passive     true
% 3.25/0.98  --inst_prop_sim_given                   true
% 3.25/0.98  --inst_prop_sim_new                     false
% 3.25/0.98  --inst_subs_new                         false
% 3.25/0.98  --inst_eq_res_simp                      false
% 3.25/0.98  --inst_subs_given                       false
% 3.25/0.98  --inst_orphan_elimination               true
% 3.25/0.98  --inst_learning_loop_flag               true
% 3.25/0.98  --inst_learning_start                   3000
% 3.25/0.98  --inst_learning_factor                  2
% 3.25/0.98  --inst_start_prop_sim_after_learn       3
% 3.25/0.98  --inst_sel_renew                        solver
% 3.25/0.98  --inst_lit_activity_flag                true
% 3.25/0.98  --inst_restr_to_given                   false
% 3.25/0.98  --inst_activity_threshold               500
% 3.25/0.98  --inst_out_proof                        true
% 3.25/0.98  
% 3.25/0.98  ------ Resolution Options
% 3.25/0.98  
% 3.25/0.98  --resolution_flag                       false
% 3.25/0.98  --res_lit_sel                           adaptive
% 3.25/0.98  --res_lit_sel_side                      none
% 3.25/0.98  --res_ordering                          kbo
% 3.25/0.98  --res_to_prop_solver                    active
% 3.25/0.98  --res_prop_simpl_new                    false
% 3.25/0.98  --res_prop_simpl_given                  true
% 3.25/0.98  --res_passive_queue_type                priority_queues
% 3.25/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.98  --res_passive_queues_freq               [15;5]
% 3.25/0.98  --res_forward_subs                      full
% 3.25/0.98  --res_backward_subs                     full
% 3.25/0.98  --res_forward_subs_resolution           true
% 3.25/0.98  --res_backward_subs_resolution          true
% 3.25/0.98  --res_orphan_elimination                true
% 3.25/0.98  --res_time_limit                        2.
% 3.25/0.98  --res_out_proof                         true
% 3.25/0.98  
% 3.25/0.98  ------ Superposition Options
% 3.25/0.98  
% 3.25/0.98  --superposition_flag                    true
% 3.25/0.98  --sup_passive_queue_type                priority_queues
% 3.25/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.98  --demod_completeness_check              fast
% 3.25/0.98  --demod_use_ground                      true
% 3.25/0.98  --sup_to_prop_solver                    passive
% 3.25/0.98  --sup_prop_simpl_new                    true
% 3.25/0.98  --sup_prop_simpl_given                  true
% 3.25/0.98  --sup_fun_splitting                     false
% 3.25/0.98  --sup_smt_interval                      50000
% 3.25/0.98  
% 3.25/0.98  ------ Superposition Simplification Setup
% 3.25/0.98  
% 3.25/0.98  --sup_indices_passive                   []
% 3.25/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_full_bw                           [BwDemod]
% 3.25/0.98  --sup_immed_triv                        [TrivRules]
% 3.25/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_immed_bw_main                     []
% 3.25/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.98  
% 3.25/0.98  ------ Combination Options
% 3.25/0.98  
% 3.25/0.98  --comb_res_mult                         3
% 3.25/0.98  --comb_sup_mult                         2
% 3.25/0.98  --comb_inst_mult                        10
% 3.25/0.98  
% 3.25/0.98  ------ Debug Options
% 3.25/0.98  
% 3.25/0.98  --dbg_backtrace                         false
% 3.25/0.98  --dbg_dump_prop_clauses                 false
% 3.25/0.98  --dbg_dump_prop_clauses_file            -
% 3.25/0.98  --dbg_out_stat                          false
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  ------ Proving...
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  % SZS status Theorem for theBenchmark.p
% 3.25/0.98  
% 3.25/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/0.98  
% 3.25/0.98  fof(f14,axiom,(
% 3.25/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f27,plain,(
% 3.25/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.98    inference(ennf_transformation,[],[f14])).
% 3.25/0.98  
% 3.25/0.98  fof(f74,plain,(
% 3.25/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.98    inference(cnf_transformation,[],[f27])).
% 3.25/0.98  
% 3.25/0.98  fof(f17,conjecture,(
% 3.25/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f18,negated_conjecture,(
% 3.25/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.25/0.98    inference(negated_conjecture,[],[f17])).
% 3.25/0.98  
% 3.25/0.98  fof(f31,plain,(
% 3.25/0.98    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.25/0.98    inference(ennf_transformation,[],[f18])).
% 3.25/0.98  
% 3.25/0.98  fof(f32,plain,(
% 3.25/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.25/0.98    inference(flattening,[],[f31])).
% 3.25/0.98  
% 3.25/0.98  fof(f45,plain,(
% 3.25/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 3.25/0.98    introduced(choice_axiom,[])).
% 3.25/0.98  
% 3.25/0.98  fof(f46,plain,(
% 3.25/0.98    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 3.25/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f45])).
% 3.25/0.98  
% 3.25/0.98  fof(f84,plain,(
% 3.25/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 3.25/0.98    inference(cnf_transformation,[],[f46])).
% 3.25/0.98  
% 3.25/0.98  fof(f1,axiom,(
% 3.25/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f47,plain,(
% 3.25/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f1])).
% 3.25/0.98  
% 3.25/0.98  fof(f2,axiom,(
% 3.25/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f48,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f2])).
% 3.25/0.98  
% 3.25/0.98  fof(f3,axiom,(
% 3.25/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f49,plain,(
% 3.25/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f3])).
% 3.25/0.98  
% 3.25/0.98  fof(f4,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f50,plain,(
% 3.25/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f4])).
% 3.25/0.98  
% 3.25/0.98  fof(f5,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f51,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f5])).
% 3.25/0.98  
% 3.25/0.98  fof(f6,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f52,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f6])).
% 3.25/0.98  
% 3.25/0.98  fof(f7,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f53,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f7])).
% 3.25/0.98  
% 3.25/0.98  fof(f87,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f52,f53])).
% 3.25/0.98  
% 3.25/0.98  fof(f88,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f51,f87])).
% 3.25/0.98  
% 3.25/0.98  fof(f89,plain,(
% 3.25/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f50,f88])).
% 3.25/0.98  
% 3.25/0.98  fof(f90,plain,(
% 3.25/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f49,f89])).
% 3.25/0.98  
% 3.25/0.98  fof(f91,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f48,f90])).
% 3.25/0.98  
% 3.25/0.98  fof(f92,plain,(
% 3.25/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f47,f91])).
% 3.25/0.98  
% 3.25/0.98  fof(f95,plain,(
% 3.25/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))),
% 3.25/0.98    inference(definition_unfolding,[],[f84,f92])).
% 3.25/0.98  
% 3.25/0.98  fof(f83,plain,(
% 3.25/0.98    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 3.25/0.98    inference(cnf_transformation,[],[f46])).
% 3.25/0.98  
% 3.25/0.98  fof(f96,plain,(
% 3.25/0.98    v1_funct_2(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)),
% 3.25/0.98    inference(definition_unfolding,[],[f83,f92])).
% 3.25/0.98  
% 3.25/0.98  fof(f16,axiom,(
% 3.25/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f29,plain,(
% 3.25/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.98    inference(ennf_transformation,[],[f16])).
% 3.25/0.98  
% 3.25/0.98  fof(f30,plain,(
% 3.25/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.98    inference(flattening,[],[f29])).
% 3.25/0.98  
% 3.25/0.98  fof(f44,plain,(
% 3.25/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.98    inference(nnf_transformation,[],[f30])).
% 3.25/0.98  
% 3.25/0.98  fof(f76,plain,(
% 3.25/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.98    inference(cnf_transformation,[],[f44])).
% 3.25/0.98  
% 3.25/0.98  fof(f85,plain,(
% 3.25/0.98    k1_xboole_0 != sK4),
% 3.25/0.98    inference(cnf_transformation,[],[f46])).
% 3.25/0.98  
% 3.25/0.98  fof(f8,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f20,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 3.25/0.98    inference(ennf_transformation,[],[f8])).
% 3.25/0.98  
% 3.25/0.98  fof(f34,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.25/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.25/0.98  
% 3.25/0.98  fof(f33,plain,(
% 3.25/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 3.25/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.25/0.98  
% 3.25/0.98  fof(f35,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 3.25/0.98    inference(definition_folding,[],[f20,f34,f33])).
% 3.25/0.98  
% 3.25/0.98  fof(f43,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 3.25/0.98    inference(nnf_transformation,[],[f35])).
% 3.25/0.98  
% 3.25/0.98  fof(f67,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 3.25/0.98    inference(cnf_transformation,[],[f43])).
% 3.25/0.98  
% 3.25/0.98  fof(f105,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 3.25/0.98    inference(equality_resolution,[],[f67])).
% 3.25/0.98  
% 3.25/0.98  fof(f40,plain,(
% 3.25/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.25/0.98    inference(nnf_transformation,[],[f33])).
% 3.25/0.98  
% 3.25/0.98  fof(f41,plain,(
% 3.25/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.25/0.98    inference(flattening,[],[f40])).
% 3.25/0.98  
% 3.25/0.98  fof(f42,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.25/0.98    inference(rectify,[],[f41])).
% 3.25/0.98  
% 3.25/0.98  fof(f66,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 3.25/0.98    inference(cnf_transformation,[],[f42])).
% 3.25/0.98  
% 3.25/0.98  fof(f97,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.25/0.98    inference(equality_resolution,[],[f66])).
% 3.25/0.98  
% 3.25/0.98  fof(f36,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.25/0.98    inference(nnf_transformation,[],[f34])).
% 3.25/0.98  
% 3.25/0.98  fof(f37,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.25/0.98    inference(rectify,[],[f36])).
% 3.25/0.98  
% 3.25/0.98  fof(f38,plain,(
% 3.25/0.98    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 3.25/0.98    introduced(choice_axiom,[])).
% 3.25/0.98  
% 3.25/0.98  fof(f39,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.25/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 3.25/0.98  
% 3.25/0.98  fof(f55,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f39])).
% 3.25/0.98  
% 3.25/0.98  fof(f12,axiom,(
% 3.25/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f24,plain,(
% 3.25/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.25/0.98    inference(ennf_transformation,[],[f12])).
% 3.25/0.98  
% 3.25/0.98  fof(f25,plain,(
% 3.25/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.25/0.98    inference(flattening,[],[f24])).
% 3.25/0.98  
% 3.25/0.98  fof(f72,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f25])).
% 3.25/0.98  
% 3.25/0.98  fof(f93,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f72,f92,f92])).
% 3.25/0.98  
% 3.25/0.98  fof(f82,plain,(
% 3.25/0.98    v1_funct_1(sK5)),
% 3.25/0.98    inference(cnf_transformation,[],[f46])).
% 3.25/0.98  
% 3.25/0.98  fof(f13,axiom,(
% 3.25/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f19,plain,(
% 3.25/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.25/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.25/0.98  
% 3.25/0.98  fof(f26,plain,(
% 3.25/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.98    inference(ennf_transformation,[],[f19])).
% 3.25/0.98  
% 3.25/0.98  fof(f73,plain,(
% 3.25/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.98    inference(cnf_transformation,[],[f26])).
% 3.25/0.98  
% 3.25/0.98  fof(f11,axiom,(
% 3.25/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f22,plain,(
% 3.25/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.25/0.98    inference(ennf_transformation,[],[f11])).
% 3.25/0.98  
% 3.25/0.98  fof(f23,plain,(
% 3.25/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.25/0.98    inference(flattening,[],[f22])).
% 3.25/0.98  
% 3.25/0.98  fof(f71,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f23])).
% 3.25/0.98  
% 3.25/0.98  fof(f10,axiom,(
% 3.25/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f70,plain,(
% 3.25/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.25/0.98    inference(cnf_transformation,[],[f10])).
% 3.25/0.98  
% 3.25/0.98  fof(f9,axiom,(
% 3.25/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f21,plain,(
% 3.25/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.25/0.98    inference(ennf_transformation,[],[f9])).
% 3.25/0.98  
% 3.25/0.98  fof(f69,plain,(
% 3.25/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f21])).
% 3.25/0.98  
% 3.25/0.98  fof(f15,axiom,(
% 3.25/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f28,plain,(
% 3.25/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.98    inference(ennf_transformation,[],[f15])).
% 3.25/0.98  
% 3.25/0.98  fof(f75,plain,(
% 3.25/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.98    inference(cnf_transformation,[],[f28])).
% 3.25/0.98  
% 3.25/0.98  fof(f86,plain,(
% 3.25/0.98    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 3.25/0.98    inference(cnf_transformation,[],[f46])).
% 3.25/0.98  
% 3.25/0.98  fof(f94,plain,(
% 3.25/0.98    k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5)),
% 3.25/0.98    inference(definition_unfolding,[],[f86,f92,f92])).
% 3.25/0.98  
% 3.25/0.98  cnf(c_20,plain,
% 3.25/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.25/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_30,negated_conjecture,
% 3.25/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
% 3.25/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_453,plain,
% 3.25/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.25/0.98      | sK5 != X2 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_454,plain,
% 3.25/0.98      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_453]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2583,plain,
% 3.25/0.98      ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k1_relat_1(sK5) ),
% 3.25/0.98      inference(equality_resolution,[status(thm)],[c_454]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_31,negated_conjecture,
% 3.25/0.98      ( v1_funct_2(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) ),
% 3.25/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_27,plain,
% 3.25/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.25/0.98      | k1_xboole_0 = X2 ),
% 3.25/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_408,plain,
% 3.25/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.25/0.98      | sK5 != X0
% 3.25/0.98      | k1_xboole_0 = X2 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_409,plain,
% 3.25/0.98      ( ~ v1_funct_2(sK5,X0,X1)
% 3.25/0.98      | k1_relset_1(X0,X1,sK5) = X0
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.25/0.98      | k1_xboole_0 = X1 ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_408]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_825,plain,
% 3.25/0.98      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
% 3.25/0.98      | k1_relset_1(X0,X1,sK5) = X0
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.25/0.98      | sK4 != X1
% 3.25/0.98      | sK5 != sK5
% 3.25/0.98      | k1_xboole_0 = X1 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_31,c_409]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_826,plain,
% 3.25/0.98      ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
% 3.25/0.98      | k1_xboole_0 = sK4 ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_825]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_29,negated_conjecture,
% 3.25/0.98      ( k1_xboole_0 != sK4 ),
% 3.25/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_827,plain,
% 3.25/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
% 3.25/0.98      | k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.25/0.98      inference(global_propositional_subsumption,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_826,c_29]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_828,plain,
% 3.25/0.98      ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
% 3.25/0.98      inference(renaming,[status(thm)],[c_827]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_1291,plain,
% 3.25/0.98      ( k1_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.25/0.98      inference(equality_resolution_simp,[status(thm)],[c_828]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2954,plain,
% 3.25/0.98      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK5) ),
% 3.25/0.98      inference(demodulation,[status(thm)],[c_2583,c_1291]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_14,plain,
% 3.25/0.98      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 3.25/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2382,plain,
% 3.25/0.98      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3642,plain,
% 3.25/0.98      ( sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k1_relat_1(sK5)) = iProver_top ),
% 3.25/0.98      inference(superposition,[status(thm)],[c_2954,c_2382]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4,plain,
% 3.25/0.98      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.25/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2392,plain,
% 3.25/0.98      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2,plain,
% 3.25/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.25/0.98      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 3.25/0.98      | r2_hidden(X0,X9) ),
% 3.25/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2394,plain,
% 3.25/0.98      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 3.25/0.98      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 3.25/0.98      | r2_hidden(X0,X9) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4833,plain,
% 3.25/0.98      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 3.25/0.98      | r2_hidden(X7,X8) = iProver_top ),
% 3.25/0.98      inference(superposition,[status(thm)],[c_2392,c_2394]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_5040,plain,
% 3.25/0.98      ( r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top ),
% 3.25/0.98      inference(superposition,[status(thm)],[c_3642,c_4833]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_18,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.25/0.98      | ~ v1_funct_1(X1)
% 3.25/0.98      | ~ v1_relat_1(X1)
% 3.25/0.98      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
% 3.25/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_32,negated_conjecture,
% 3.25/0.98      ( v1_funct_1(sK5) ),
% 3.25/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_359,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.25/0.98      | ~ v1_relat_1(X1)
% 3.25/0.98      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 3.25/0.98      | sK5 != X1 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_32]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_360,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.25/0.98      | ~ v1_relat_1(sK5)
% 3.25/0.98      | k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_359]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2380,plain,
% 3.25/0.98      ( k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 3.25/0.98      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.25/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_5203,plain,
% 3.25/0.98      ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(k7_relat_1(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
% 3.25/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.25/0.98      inference(superposition,[status(thm)],[c_5040,c_2380]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_19,plain,
% 3.25/0.98      ( v4_relat_1(X0,X1)
% 3.25/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.25/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_17,plain,
% 3.25/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.25/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_341,plain,
% 3.25/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.98      | ~ v1_relat_1(X0)
% 3.25/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.25/0.98      inference(resolution,[status(thm)],[c_19,c_17]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_393,plain,
% 3.25/0.98      ( ~ v1_relat_1(X0)
% 3.25/0.98      | k7_relat_1(X0,X1) = X0
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.25/0.98      | sK5 != X0 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_341,c_30]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_394,plain,
% 3.25/0.98      ( ~ v1_relat_1(sK5)
% 3.25/0.98      | k7_relat_1(sK5,X0) = sK5
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_393]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2378,plain,
% 3.25/0.98      ( k7_relat_1(sK5,X0) = sK5
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.25/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_16,plain,
% 3.25/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_15,plain,
% 3.25/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.25/0.98      | ~ v1_relat_1(X1)
% 3.25/0.98      | v1_relat_1(X0) ),
% 3.25/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_378,plain,
% 3.25/0.98      ( ~ v1_relat_1(X0)
% 3.25/0.98      | v1_relat_1(X1)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
% 3.25/0.98      | sK5 != X1 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_379,plain,
% 3.25/0.98      ( ~ v1_relat_1(X0)
% 3.25/0.98      | v1_relat_1(sK5)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_378]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2553,plain,
% 3.25/0.98      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.25/0.98      | v1_relat_1(sK5)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_379]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3179,plain,
% 3.25/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.25/0.98      | k7_relat_1(sK5,X0) = sK5 ),
% 3.25/0.98      inference(global_propositional_subsumption,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_2378,c_16,c_394,c_2553]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3180,plain,
% 3.25/0.98      ( k7_relat_1(sK5,X0) = sK5
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/0.98      inference(renaming,[status(thm)],[c_3179]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3184,plain,
% 3.25/0.98      ( k7_relat_1(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK5 ),
% 3.25/0.98      inference(equality_resolution,[status(thm)],[c_3180]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4125,plain,
% 3.25/0.98      ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
% 3.25/0.98      inference(light_normalisation,[status(thm)],[c_3184,c_2954]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_5206,plain,
% 3.25/0.98      ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
% 3.25/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.25/0.98      inference(light_normalisation,[status(thm)],[c_5203,c_2954,c_4125]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3923,plain,
% 3.25/0.98      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3924,plain,
% 3.25/0.98      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_3923]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2379,plain,
% 3.25/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
% 3.25/0.98      | v1_relat_1(X0) != iProver_top
% 3.25/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3176,plain,
% 3.25/0.98      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != iProver_top
% 3.25/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.25/0.98      inference(equality_resolution,[status(thm)],[c_2379]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_21,plain,
% 3.25/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.25/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_444,plain,
% 3.25/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.25/0.98      | sK5 != X2 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_445,plain,
% 3.25/0.98      ( k2_relset_1(X0,X1,sK5) = k2_relat_1(sK5)
% 3.25/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_444]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2580,plain,
% 3.25/0.98      ( k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 3.25/0.98      inference(equality_resolution,[status(thm)],[c_445]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_28,negated_conjecture,
% 3.25/0.98      ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK5) ),
% 3.25/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2623,plain,
% 3.25/0.98      ( k6_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
% 3.25/0.98      inference(demodulation,[status(thm)],[c_2580,c_28]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(contradiction,plain,
% 3.25/0.98      ( $false ),
% 3.25/0.98      inference(minisat,[status(thm)],[c_5206,c_3924,c_3176,c_2623]) ).
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/0.98  
% 3.25/0.98  ------                               Statistics
% 3.25/0.98  
% 3.25/0.98  ------ General
% 3.25/0.98  
% 3.25/0.98  abstr_ref_over_cycles:                  0
% 3.25/0.98  abstr_ref_under_cycles:                 0
% 3.25/0.98  gc_basic_clause_elim:                   0
% 3.25/0.98  forced_gc_time:                         0
% 3.25/0.98  parsing_time:                           0.013
% 3.25/0.98  unif_index_cands_time:                  0.
% 3.25/0.98  unif_index_add_time:                    0.
% 3.25/0.98  orderings_time:                         0.
% 3.25/0.98  out_proof_time:                         0.011
% 3.25/0.98  total_time:                             0.22
% 3.25/0.98  num_of_symbols:                         53
% 3.25/0.98  num_of_terms:                           5092
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing
% 3.25/0.98  
% 3.25/0.98  num_of_splits:                          0
% 3.25/0.98  num_of_split_atoms:                     0
% 3.25/0.98  num_of_reused_defs:                     0
% 3.25/0.98  num_eq_ax_congr_red:                    81
% 3.25/0.98  num_of_sem_filtered_clauses:            1
% 3.25/0.98  num_of_subtypes:                        0
% 3.25/0.98  monotx_restored_types:                  0
% 3.25/0.98  sat_num_of_epr_types:                   0
% 3.25/0.98  sat_num_of_non_cyclic_types:            0
% 3.25/0.98  sat_guarded_non_collapsed_types:        0
% 3.25/0.98  num_pure_diseq_elim:                    0
% 3.25/0.98  simp_replaced_by:                       0
% 3.25/0.98  res_preprocessed:                       142
% 3.25/0.98  prep_upred:                             0
% 3.25/0.98  prep_unflattend:                        639
% 3.25/0.98  smt_new_axioms:                         0
% 3.25/0.98  pred_elim_cands:                        4
% 3.25/0.98  pred_elim:                              4
% 3.25/0.98  pred_elim_cl:                           7
% 3.25/0.98  pred_elim_cycles:                       10
% 3.25/0.98  merged_defs:                            0
% 3.25/0.98  merged_defs_ncl:                        0
% 3.25/0.98  bin_hyper_res:                          0
% 3.25/0.98  prep_cycles:                            4
% 3.25/0.98  pred_elim_time:                         0.034
% 3.25/0.98  splitting_time:                         0.
% 3.25/0.98  sem_filter_time:                        0.
% 3.25/0.98  monotx_time:                            0.
% 3.25/0.98  subtype_inf_time:                       0.
% 3.25/0.98  
% 3.25/0.98  ------ Problem properties
% 3.25/0.98  
% 3.25/0.98  clauses:                                26
% 3.25/0.98  conjectures:                            2
% 3.25/0.98  epr:                                    12
% 3.25/0.98  horn:                                   23
% 3.25/0.98  ground:                                 5
% 3.25/0.98  unary:                                  13
% 3.25/0.98  binary:                                 3
% 3.25/0.98  lits:                                   56
% 3.25/0.98  lits_eq:                                27
% 3.25/0.98  fd_pure:                                0
% 3.25/0.98  fd_pseudo:                              0
% 3.25/0.98  fd_cond:                                0
% 3.25/0.98  fd_pseudo_cond:                         2
% 3.25/0.98  ac_symbols:                             0
% 3.25/0.98  
% 3.25/0.98  ------ Propositional Solver
% 3.25/0.98  
% 3.25/0.98  prop_solver_calls:                      26
% 3.25/0.98  prop_fast_solver_calls:                 1062
% 3.25/0.98  smt_solver_calls:                       0
% 3.25/0.98  smt_fast_solver_calls:                  0
% 3.25/0.98  prop_num_of_clauses:                    1481
% 3.25/0.98  prop_preprocess_simplified:             6568
% 3.25/0.98  prop_fo_subsumed:                       8
% 3.25/0.98  prop_solver_time:                       0.
% 3.25/0.98  smt_solver_time:                        0.
% 3.25/0.98  smt_fast_solver_time:                   0.
% 3.25/0.98  prop_fast_solver_time:                  0.
% 3.25/0.98  prop_unsat_core_time:                   0.
% 3.25/0.98  
% 3.25/0.98  ------ QBF
% 3.25/0.98  
% 3.25/0.98  qbf_q_res:                              0
% 3.25/0.98  qbf_num_tautologies:                    0
% 3.25/0.98  qbf_prep_cycles:                        0
% 3.25/0.98  
% 3.25/0.98  ------ BMC1
% 3.25/0.98  
% 3.25/0.98  bmc1_current_bound:                     -1
% 3.25/0.98  bmc1_last_solved_bound:                 -1
% 3.25/0.98  bmc1_unsat_core_size:                   -1
% 3.25/0.98  bmc1_unsat_core_parents_size:           -1
% 3.25/0.98  bmc1_merge_next_fun:                    0
% 3.25/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.25/0.98  
% 3.25/0.98  ------ Instantiation
% 3.25/0.98  
% 3.25/0.98  inst_num_of_clauses:                    415
% 3.25/0.98  inst_num_in_passive:                    173
% 3.25/0.98  inst_num_in_active:                     181
% 3.25/0.98  inst_num_in_unprocessed:                61
% 3.25/0.98  inst_num_of_loops:                      220
% 3.25/0.98  inst_num_of_learning_restarts:          0
% 3.25/0.98  inst_num_moves_active_passive:          38
% 3.25/0.98  inst_lit_activity:                      0
% 3.25/0.98  inst_lit_activity_moves:                0
% 3.25/0.98  inst_num_tautologies:                   0
% 3.25/0.98  inst_num_prop_implied:                  0
% 3.25/0.98  inst_num_existing_simplified:           0
% 3.25/0.98  inst_num_eq_res_simplified:             0
% 3.25/0.98  inst_num_child_elim:                    0
% 3.25/0.98  inst_num_of_dismatching_blockings:      130
% 3.25/0.98  inst_num_of_non_proper_insts:           397
% 3.25/0.98  inst_num_of_duplicates:                 0
% 3.25/0.98  inst_inst_num_from_inst_to_res:         0
% 3.25/0.98  inst_dismatching_checking_time:         0.
% 3.25/0.98  
% 3.25/0.98  ------ Resolution
% 3.25/0.98  
% 3.25/0.98  res_num_of_clauses:                     0
% 3.25/0.98  res_num_in_passive:                     0
% 3.25/0.98  res_num_in_active:                      0
% 3.25/0.98  res_num_of_loops:                       146
% 3.25/0.98  res_forward_subset_subsumed:            254
% 3.25/0.98  res_backward_subset_subsumed:           0
% 3.25/0.98  res_forward_subsumed:                   0
% 3.25/0.98  res_backward_subsumed:                  0
% 3.25/0.98  res_forward_subsumption_resolution:     0
% 3.25/0.98  res_backward_subsumption_resolution:    0
% 3.25/0.98  res_clause_to_clause_subsumption:       1127
% 3.25/0.98  res_orphan_elimination:                 0
% 3.25/0.98  res_tautology_del:                      50
% 3.25/0.98  res_num_eq_res_simplified:              1
% 3.25/0.98  res_num_sel_changes:                    0
% 3.25/0.98  res_moves_from_active_to_pass:          0
% 3.25/0.98  
% 3.25/0.98  ------ Superposition
% 3.25/0.98  
% 3.25/0.98  sup_time_total:                         0.
% 3.25/0.98  sup_time_generating:                    0.
% 3.25/0.98  sup_time_sim_full:                      0.
% 3.25/0.98  sup_time_sim_immed:                     0.
% 3.25/0.98  
% 3.25/0.98  sup_num_of_clauses:                     45
% 3.25/0.98  sup_num_in_active:                      33
% 3.25/0.98  sup_num_in_passive:                     12
% 3.25/0.98  sup_num_of_loops:                       42
% 3.25/0.98  sup_fw_superposition:                   25
% 3.25/0.98  sup_bw_superposition:                   4
% 3.25/0.98  sup_immediate_simplified:               2
% 3.25/0.98  sup_given_eliminated:                   0
% 3.25/0.98  comparisons_done:                       0
% 3.25/0.98  comparisons_avoided:                    0
% 3.25/0.98  
% 3.25/0.98  ------ Simplifications
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  sim_fw_subset_subsumed:                 0
% 3.25/0.98  sim_bw_subset_subsumed:                 0
% 3.25/0.98  sim_fw_subsumed:                        0
% 3.25/0.98  sim_bw_subsumed:                        0
% 3.25/0.98  sim_fw_subsumption_res:                 0
% 3.25/0.98  sim_bw_subsumption_res:                 0
% 3.25/0.98  sim_tautology_del:                      2
% 3.25/0.98  sim_eq_tautology_del:                   4
% 3.25/0.98  sim_eq_res_simp:                        0
% 3.25/0.98  sim_fw_demodulated:                     0
% 3.25/0.98  sim_bw_demodulated:                     10
% 3.25/0.98  sim_light_normalised:                   3
% 3.25/0.98  sim_joinable_taut:                      0
% 3.25/0.98  sim_joinable_simp:                      0
% 3.25/0.98  sim_ac_normalised:                      0
% 3.25/0.98  sim_smt_subsumption:                    0
% 3.25/0.98  
%------------------------------------------------------------------------------
