%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:44 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  189 (2051 expanded)
%              Number of clauses        :  119 ( 708 expanded)
%              Number of leaves         :   22 ( 478 expanded)
%              Depth                    :   24
%              Number of atoms          :  695 (11500 expanded)
%              Number of equality atoms :  208 (2513 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_hidden(sK9,k5_partfun1(X0,X1,X2))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK9)
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK9,X0,X1)
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(sK6,sK7,sK8))
          & ( k1_xboole_0 = sK6
            | k1_xboole_0 != sK7 )
          & r1_partfun1(sK8,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
          & v1_funct_2(X3,sK6,sK7)
          & v1_funct_1(X3) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8))
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK7 )
    & r1_partfun1(sK8,sK9)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK9,sK6,sK7)
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f24,f46,f45])).

fof(f84,plain,(
    v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f47])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,(
    r1_partfun1(sK8,sK9) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    ~ r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f47])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f22,f26,f25])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
        & v1_partfun1(sK5(X0,X1,X2,X7),X1)
        & sK5(X0,X1,X2,X7) = X7
        & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
        & v1_partfun1(sK4(X0,X1,X2,X3),X1)
        & sK4(X0,X1,X2,X3) = X4
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK3(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK3(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK3(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
              & v1_partfun1(sK4(X0,X1,X2,X3),X1)
              & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3)
              & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK4(X0,X1,X2,X3)) )
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
                & v1_partfun1(sK5(X0,X1,X2,X7),X1)
                & sK5(X0,X1,X2,X7) = X7
                & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK5(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).

fof(f73,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f73])).

fof(f87,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5182,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5912,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5182,c_5180])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5183,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5186,plain,
    ( r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_280,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_281,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_352,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_281])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_474,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK7 != X2
    | sK6 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_475,plain,
    ( v1_partfun1(sK9,sK6)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK7) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_477,plain,
    ( v1_partfun1(sK9,sK6)
    | v1_xboole_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_38,c_36])).

cnf(c_572,plain,
    ( v1_partfun1(sK9,sK6)
    | ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_477])).

cnf(c_573,plain,
    ( v1_partfun1(sK9,sK6)
    | ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_5155,plain,
    ( v1_partfun1(sK9,sK6) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_6323,plain,
    ( v1_partfun1(sK9,sK6) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5186,c_5155])).

cnf(c_6536,plain,
    ( v1_partfun1(sK9,sK6) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5183,c_6323])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5184,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6826,plain,
    ( sK7 = X0
    | v1_partfun1(sK9,sK6) = iProver_top
    | r1_tarski(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6536,c_5184])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,negated_conjecture,
    ( r1_partfun1(sK8,sK9) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_107,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_113,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_112,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5522,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK7),k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5563,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,X0)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5564,plain,
    ( sK7 = X0
    | r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5563])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_32,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_491,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X4 != X1
    | X3 != X0
    | X5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_492,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_5492,plain,
    ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_5597,plain,
    ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_5492])).

cnf(c_4379,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5632,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_4379])).

cnf(c_5926,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | r1_tarski(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5927,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5926])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_545,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_352])).

cnf(c_546,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_6176,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,sK7),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_6848,plain,
    ( v1_partfun1(sK9,sK6)
    | ~ r1_tarski(X0,sK7)
    | sK7 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6826])).

cnf(c_6850,plain,
    ( v1_partfun1(sK9,sK6)
    | ~ r1_tarski(k1_xboole_0,sK7)
    | sK7 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6848])).

cnf(c_4385,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5474,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4385])).

cnf(c_5631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_5474])).

cnf(c_6954,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5631])).

cnf(c_6958,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
    | sK7 != k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6954])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,X4)
    | ~ v1_partfun1(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X4,X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5507,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,sK9)
    | ~ v1_partfun1(sK9,X1)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK9,X3)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_5618,plain,
    ( ~ sP0(sK8,X0,X1,X2)
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,X0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK9,X2)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_5507])).

cnf(c_5738,plain,
    ( ~ sP0(sK8,sK6,X0,X1)
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,sK6)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,X0)))
    | r2_hidden(sK9,X1)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_5618])).

cnf(c_6583,plain,
    ( ~ sP0(sK8,sK6,sK7,X0)
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,sK6)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | r2_hidden(sK9,X0)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_5738])).

cnf(c_7547,plain,
    ( ~ sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,sK6)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_6583])).

cnf(c_7551,plain,
    ( sK7 = X0
    | r1_tarski(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6826,c_40,c_39,c_38,c_36,c_35,c_33,c_107,c_113,c_112,c_5522,c_5564,c_5597,c_5632,c_5927,c_6176,c_6850,c_6958,c_7547])).

cnf(c_7560,plain,
    ( sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5912,c_7551])).

cnf(c_5166,plain,
    ( r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7586,plain,
    ( r2_hidden(sK9,k5_partfun1(sK6,k1_xboole_0,sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7560,c_5166])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 = sK6 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7589,plain,
    ( sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7560,c_34])).

cnf(c_7590,plain,
    ( sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7589])).

cnf(c_7601,plain,
    ( r2_hidden(sK9,k5_partfun1(k1_xboole_0,k1_xboole_0,sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7586,c_7590])).

cnf(c_5164,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7587,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7560,c_5164])).

cnf(c_7597,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7587,c_7590])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_7599,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7597,c_8])).

cnf(c_5162,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7588,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7560,c_5162])).

cnf(c_7593,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7588,c_7590])).

cnf(c_7595,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7593,c_8])).

cnf(c_6892,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
    | r1_tarski(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6893,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6892])).

cnf(c_6895,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6893])).

cnf(c_6681,plain,
    ( ~ sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8))
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,X0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK9,k5_partfun1(X0,X1,sK8))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_5618])).

cnf(c_6682,plain,
    ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8)) != iProver_top
    | r1_partfun1(sK8,sK9) != iProver_top
    | v1_partfun1(sK9,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK9,k5_partfun1(X0,X1,sK8)) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6681])).

cnf(c_6684,plain,
    ( sP0(sK8,k1_xboole_0,k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK8)) != iProver_top
    | r1_partfun1(sK8,sK9) != iProver_top
    | v1_partfun1(sK9,k1_xboole_0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r2_hidden(sK9,k5_partfun1(k1_xboole_0,k1_xboole_0,sK8)) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6682])).

cnf(c_6504,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(X0))
    | r1_tarski(sK9,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6505,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK9,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6504])).

cnf(c_6507,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6505])).

cnf(c_4381,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_5997,plain,
    ( ~ r1_tarski(sK8,X0)
    | r1_tarski(sK8,k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_4381])).

cnf(c_5998,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | r1_tarski(sK8,X2) != iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5997])).

cnf(c_6000,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_tarski(sK8,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5998])).

cnf(c_5977,plain,
    ( ~ r1_tarski(sK9,X0)
    | r1_tarski(sK9,k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_4381])).

cnf(c_5978,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | r1_tarski(sK9,X2) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5977])).

cnf(c_5980,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_tarski(sK9,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(sK9,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5978])).

cnf(c_15,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_533,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_534,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_5744,plain,
    ( v1_partfun1(sK9,k1_xboole_0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_5747,plain,
    ( v1_partfun1(sK9,k1_xboole_0) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5744])).

cnf(c_5749,plain,
    ( v1_partfun1(sK9,k1_xboole_0) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5747])).

cnf(c_5592,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK8,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5593,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5592])).

cnf(c_5595,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5593])).

cnf(c_5584,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK9,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5585,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5584])).

cnf(c_5587,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5585])).

cnf(c_917,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_492,c_40])).

cnf(c_918,plain,
    ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_919,plain,
    ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_921,plain,
    ( sP0(sK8,k1_xboole_0,k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK8)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_116,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_46,plain,
    ( r1_partfun1(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7601,c_7599,c_7595,c_6895,c_6684,c_6507,c_6000,c_5980,c_5749,c_5595,c_5587,c_921,c_116,c_46,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.74/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.99  
% 2.74/0.99  ------  iProver source info
% 2.74/0.99  
% 2.74/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.99  git: non_committed_changes: false
% 2.74/0.99  git: last_make_outside_of_git: false
% 2.74/0.99  
% 2.74/0.99  ------ 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options
% 2.74/0.99  
% 2.74/0.99  --out_options                           all
% 2.74/0.99  --tptp_safe_out                         true
% 2.74/0.99  --problem_path                          ""
% 2.74/0.99  --include_path                          ""
% 2.74/0.99  --clausifier                            res/vclausify_rel
% 2.74/0.99  --clausifier_options                    --mode clausify
% 2.74/0.99  --stdin                                 false
% 2.74/0.99  --stats_out                             all
% 2.74/0.99  
% 2.74/0.99  ------ General Options
% 2.74/0.99  
% 2.74/0.99  --fof                                   false
% 2.74/0.99  --time_out_real                         305.
% 2.74/0.99  --time_out_virtual                      -1.
% 2.74/0.99  --symbol_type_check                     false
% 2.74/0.99  --clausify_out                          false
% 2.74/0.99  --sig_cnt_out                           false
% 2.74/0.99  --trig_cnt_out                          false
% 2.74/0.99  --trig_cnt_out_tolerance                1.
% 2.74/0.99  --trig_cnt_out_sk_spl                   false
% 2.74/0.99  --abstr_cl_out                          false
% 2.74/0.99  
% 2.74/0.99  ------ Global Options
% 2.74/0.99  
% 2.74/0.99  --schedule                              default
% 2.74/0.99  --add_important_lit                     false
% 2.74/0.99  --prop_solver_per_cl                    1000
% 2.74/0.99  --min_unsat_core                        false
% 2.74/0.99  --soft_assumptions                      false
% 2.74/0.99  --soft_lemma_size                       3
% 2.74/0.99  --prop_impl_unit_size                   0
% 2.74/0.99  --prop_impl_unit                        []
% 2.74/0.99  --share_sel_clauses                     true
% 2.74/0.99  --reset_solvers                         false
% 2.74/0.99  --bc_imp_inh                            [conj_cone]
% 2.74/0.99  --conj_cone_tolerance                   3.
% 2.74/0.99  --extra_neg_conj                        none
% 2.74/0.99  --large_theory_mode                     true
% 2.74/0.99  --prolific_symb_bound                   200
% 2.74/0.99  --lt_threshold                          2000
% 2.74/0.99  --clause_weak_htbl                      true
% 2.74/0.99  --gc_record_bc_elim                     false
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing Options
% 2.74/0.99  
% 2.74/0.99  --preprocessing_flag                    true
% 2.74/0.99  --time_out_prep_mult                    0.1
% 2.74/0.99  --splitting_mode                        input
% 2.74/0.99  --splitting_grd                         true
% 2.74/0.99  --splitting_cvd                         false
% 2.74/0.99  --splitting_cvd_svl                     false
% 2.74/0.99  --splitting_nvd                         32
% 2.74/0.99  --sub_typing                            true
% 2.74/0.99  --prep_gs_sim                           true
% 2.74/0.99  --prep_unflatten                        true
% 2.74/0.99  --prep_res_sim                          true
% 2.74/0.99  --prep_upred                            true
% 2.74/0.99  --prep_sem_filter                       exhaustive
% 2.74/0.99  --prep_sem_filter_out                   false
% 2.74/0.99  --pred_elim                             true
% 2.74/0.99  --res_sim_input                         true
% 2.74/0.99  --eq_ax_congr_red                       true
% 2.74/0.99  --pure_diseq_elim                       true
% 2.74/0.99  --brand_transform                       false
% 2.74/0.99  --non_eq_to_eq                          false
% 2.74/0.99  --prep_def_merge                        true
% 2.74/0.99  --prep_def_merge_prop_impl              false
% 2.74/0.99  --prep_def_merge_mbd                    true
% 2.74/0.99  --prep_def_merge_tr_red                 false
% 2.74/0.99  --prep_def_merge_tr_cl                  false
% 2.74/0.99  --smt_preprocessing                     true
% 2.74/0.99  --smt_ac_axioms                         fast
% 2.74/0.99  --preprocessed_out                      false
% 2.74/0.99  --preprocessed_stats                    false
% 2.74/0.99  
% 2.74/0.99  ------ Abstraction refinement Options
% 2.74/0.99  
% 2.74/0.99  --abstr_ref                             []
% 2.74/0.99  --abstr_ref_prep                        false
% 2.74/0.99  --abstr_ref_until_sat                   false
% 2.74/0.99  --abstr_ref_sig_restrict                funpre
% 2.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.99  --abstr_ref_under                       []
% 2.74/0.99  
% 2.74/0.99  ------ SAT Options
% 2.74/0.99  
% 2.74/0.99  --sat_mode                              false
% 2.74/0.99  --sat_fm_restart_options                ""
% 2.74/0.99  --sat_gr_def                            false
% 2.74/0.99  --sat_epr_types                         true
% 2.74/0.99  --sat_non_cyclic_types                  false
% 2.74/0.99  --sat_finite_models                     false
% 2.74/0.99  --sat_fm_lemmas                         false
% 2.74/0.99  --sat_fm_prep                           false
% 2.74/0.99  --sat_fm_uc_incr                        true
% 2.74/0.99  --sat_out_model                         small
% 2.74/0.99  --sat_out_clauses                       false
% 2.74/0.99  
% 2.74/0.99  ------ QBF Options
% 2.74/0.99  
% 2.74/0.99  --qbf_mode                              false
% 2.74/0.99  --qbf_elim_univ                         false
% 2.74/0.99  --qbf_dom_inst                          none
% 2.74/0.99  --qbf_dom_pre_inst                      false
% 2.74/0.99  --qbf_sk_in                             false
% 2.74/0.99  --qbf_pred_elim                         true
% 2.74/0.99  --qbf_split                             512
% 2.74/0.99  
% 2.74/0.99  ------ BMC1 Options
% 2.74/0.99  
% 2.74/0.99  --bmc1_incremental                      false
% 2.74/0.99  --bmc1_axioms                           reachable_all
% 2.74/0.99  --bmc1_min_bound                        0
% 2.74/0.99  --bmc1_max_bound                        -1
% 2.74/0.99  --bmc1_max_bound_default                -1
% 2.74/0.99  --bmc1_symbol_reachability              true
% 2.74/0.99  --bmc1_property_lemmas                  false
% 2.74/0.99  --bmc1_k_induction                      false
% 2.74/0.99  --bmc1_non_equiv_states                 false
% 2.74/0.99  --bmc1_deadlock                         false
% 2.74/0.99  --bmc1_ucm                              false
% 2.74/0.99  --bmc1_add_unsat_core                   none
% 2.74/0.99  --bmc1_unsat_core_children              false
% 2.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.99  --bmc1_out_stat                         full
% 2.74/0.99  --bmc1_ground_init                      false
% 2.74/0.99  --bmc1_pre_inst_next_state              false
% 2.74/0.99  --bmc1_pre_inst_state                   false
% 2.74/0.99  --bmc1_pre_inst_reach_state             false
% 2.74/0.99  --bmc1_out_unsat_core                   false
% 2.74/0.99  --bmc1_aig_witness_out                  false
% 2.74/0.99  --bmc1_verbose                          false
% 2.74/0.99  --bmc1_dump_clauses_tptp                false
% 2.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.99  --bmc1_dump_file                        -
% 2.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.99  --bmc1_ucm_extend_mode                  1
% 2.74/0.99  --bmc1_ucm_init_mode                    2
% 2.74/0.99  --bmc1_ucm_cone_mode                    none
% 2.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.99  --bmc1_ucm_relax_model                  4
% 2.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.99  --bmc1_ucm_layered_model                none
% 2.74/0.99  --bmc1_ucm_max_lemma_size               10
% 2.74/0.99  
% 2.74/0.99  ------ AIG Options
% 2.74/0.99  
% 2.74/0.99  --aig_mode                              false
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation Options
% 2.74/0.99  
% 2.74/0.99  --instantiation_flag                    true
% 2.74/0.99  --inst_sos_flag                         false
% 2.74/0.99  --inst_sos_phase                        true
% 2.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel_side                     num_symb
% 2.74/0.99  --inst_solver_per_active                1400
% 2.74/0.99  --inst_solver_calls_frac                1.
% 2.74/0.99  --inst_passive_queue_type               priority_queues
% 2.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.99  --inst_passive_queues_freq              [25;2]
% 2.74/0.99  --inst_dismatching                      true
% 2.74/0.99  --inst_eager_unprocessed_to_passive     true
% 2.74/0.99  --inst_prop_sim_given                   true
% 2.74/0.99  --inst_prop_sim_new                     false
% 2.74/0.99  --inst_subs_new                         false
% 2.74/0.99  --inst_eq_res_simp                      false
% 2.74/0.99  --inst_subs_given                       false
% 2.74/0.99  --inst_orphan_elimination               true
% 2.74/0.99  --inst_learning_loop_flag               true
% 2.74/0.99  --inst_learning_start                   3000
% 2.74/0.99  --inst_learning_factor                  2
% 2.74/0.99  --inst_start_prop_sim_after_learn       3
% 2.74/0.99  --inst_sel_renew                        solver
% 2.74/0.99  --inst_lit_activity_flag                true
% 2.74/0.99  --inst_restr_to_given                   false
% 2.74/0.99  --inst_activity_threshold               500
% 2.74/0.99  --inst_out_proof                        true
% 2.74/0.99  
% 2.74/0.99  ------ Resolution Options
% 2.74/0.99  
% 2.74/0.99  --resolution_flag                       true
% 2.74/0.99  --res_lit_sel                           adaptive
% 2.74/0.99  --res_lit_sel_side                      none
% 2.74/0.99  --res_ordering                          kbo
% 2.74/0.99  --res_to_prop_solver                    active
% 2.74/0.99  --res_prop_simpl_new                    false
% 2.74/0.99  --res_prop_simpl_given                  true
% 2.74/0.99  --res_passive_queue_type                priority_queues
% 2.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.99  --res_passive_queues_freq               [15;5]
% 2.74/0.99  --res_forward_subs                      full
% 2.74/0.99  --res_backward_subs                     full
% 2.74/0.99  --res_forward_subs_resolution           true
% 2.74/0.99  --res_backward_subs_resolution          true
% 2.74/0.99  --res_orphan_elimination                true
% 2.74/0.99  --res_time_limit                        2.
% 2.74/0.99  --res_out_proof                         true
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Options
% 2.74/0.99  
% 2.74/0.99  --superposition_flag                    true
% 2.74/0.99  --sup_passive_queue_type                priority_queues
% 2.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.99  --demod_completeness_check              fast
% 2.74/0.99  --demod_use_ground                      true
% 2.74/0.99  --sup_to_prop_solver                    passive
% 2.74/0.99  --sup_prop_simpl_new                    true
% 2.74/0.99  --sup_prop_simpl_given                  true
% 2.74/0.99  --sup_fun_splitting                     false
% 2.74/0.99  --sup_smt_interval                      50000
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Simplification Setup
% 2.74/0.99  
% 2.74/0.99  --sup_indices_passive                   []
% 2.74/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_full_bw                           [BwDemod]
% 2.74/0.99  --sup_immed_triv                        [TrivRules]
% 2.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_immed_bw_main                     []
% 2.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  
% 2.74/0.99  ------ Combination Options
% 2.74/0.99  
% 2.74/0.99  --comb_res_mult                         3
% 2.74/0.99  --comb_sup_mult                         2
% 2.74/0.99  --comb_inst_mult                        10
% 2.74/0.99  
% 2.74/0.99  ------ Debug Options
% 2.74/0.99  
% 2.74/0.99  --dbg_backtrace                         false
% 2.74/0.99  --dbg_dump_prop_clauses                 false
% 2.74/0.99  --dbg_dump_prop_clauses_file            -
% 2.74/0.99  --dbg_out_stat                          false
% 2.74/0.99  ------ Parsing...
% 2.74/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.99  ------ Proving...
% 2.74/0.99  ------ Problem Properties 
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  clauses                                 37
% 2.74/0.99  conjectures                             7
% 2.74/0.99  EPR                                     9
% 2.74/0.99  Horn                                    29
% 2.74/0.99  unary                                   10
% 2.74/0.99  binary                                  7
% 2.74/0.99  lits                                    91
% 2.74/0.99  lits eq                                 11
% 2.74/0.99  fd_pure                                 0
% 2.74/0.99  fd_pseudo                               0
% 2.74/0.99  fd_cond                                 1
% 2.74/0.99  fd_pseudo_cond                          2
% 2.74/0.99  AC symbols                              0
% 2.74/0.99  
% 2.74/0.99  ------ Schedule dynamic 5 is on 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  ------ 
% 2.74/0.99  Current options:
% 2.74/0.99  ------ 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options
% 2.74/0.99  
% 2.74/0.99  --out_options                           all
% 2.74/0.99  --tptp_safe_out                         true
% 2.74/0.99  --problem_path                          ""
% 2.74/0.99  --include_path                          ""
% 2.74/0.99  --clausifier                            res/vclausify_rel
% 2.74/0.99  --clausifier_options                    --mode clausify
% 2.74/0.99  --stdin                                 false
% 2.74/0.99  --stats_out                             all
% 2.74/0.99  
% 2.74/0.99  ------ General Options
% 2.74/0.99  
% 2.74/0.99  --fof                                   false
% 2.74/0.99  --time_out_real                         305.
% 2.74/0.99  --time_out_virtual                      -1.
% 2.74/0.99  --symbol_type_check                     false
% 2.74/0.99  --clausify_out                          false
% 2.74/0.99  --sig_cnt_out                           false
% 2.74/0.99  --trig_cnt_out                          false
% 2.74/0.99  --trig_cnt_out_tolerance                1.
% 2.74/0.99  --trig_cnt_out_sk_spl                   false
% 2.74/0.99  --abstr_cl_out                          false
% 2.74/0.99  
% 2.74/0.99  ------ Global Options
% 2.74/0.99  
% 2.74/0.99  --schedule                              default
% 2.74/0.99  --add_important_lit                     false
% 2.74/0.99  --prop_solver_per_cl                    1000
% 2.74/0.99  --min_unsat_core                        false
% 2.74/0.99  --soft_assumptions                      false
% 2.74/0.99  --soft_lemma_size                       3
% 2.74/0.99  --prop_impl_unit_size                   0
% 2.74/0.99  --prop_impl_unit                        []
% 2.74/0.99  --share_sel_clauses                     true
% 2.74/0.99  --reset_solvers                         false
% 2.74/0.99  --bc_imp_inh                            [conj_cone]
% 2.74/0.99  --conj_cone_tolerance                   3.
% 2.74/0.99  --extra_neg_conj                        none
% 2.74/0.99  --large_theory_mode                     true
% 2.74/0.99  --prolific_symb_bound                   200
% 2.74/0.99  --lt_threshold                          2000
% 2.74/0.99  --clause_weak_htbl                      true
% 2.74/0.99  --gc_record_bc_elim                     false
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing Options
% 2.74/0.99  
% 2.74/0.99  --preprocessing_flag                    true
% 2.74/0.99  --time_out_prep_mult                    0.1
% 2.74/0.99  --splitting_mode                        input
% 2.74/0.99  --splitting_grd                         true
% 2.74/0.99  --splitting_cvd                         false
% 2.74/0.99  --splitting_cvd_svl                     false
% 2.74/0.99  --splitting_nvd                         32
% 2.74/0.99  --sub_typing                            true
% 2.74/0.99  --prep_gs_sim                           true
% 2.74/0.99  --prep_unflatten                        true
% 2.74/0.99  --prep_res_sim                          true
% 2.74/0.99  --prep_upred                            true
% 2.74/0.99  --prep_sem_filter                       exhaustive
% 2.74/0.99  --prep_sem_filter_out                   false
% 2.74/0.99  --pred_elim                             true
% 2.74/0.99  --res_sim_input                         true
% 2.74/0.99  --eq_ax_congr_red                       true
% 2.74/0.99  --pure_diseq_elim                       true
% 2.74/0.99  --brand_transform                       false
% 2.74/0.99  --non_eq_to_eq                          false
% 2.74/0.99  --prep_def_merge                        true
% 2.74/0.99  --prep_def_merge_prop_impl              false
% 2.74/0.99  --prep_def_merge_mbd                    true
% 2.74/0.99  --prep_def_merge_tr_red                 false
% 2.74/0.99  --prep_def_merge_tr_cl                  false
% 2.74/0.99  --smt_preprocessing                     true
% 2.74/0.99  --smt_ac_axioms                         fast
% 2.74/0.99  --preprocessed_out                      false
% 2.74/0.99  --preprocessed_stats                    false
% 2.74/0.99  
% 2.74/0.99  ------ Abstraction refinement Options
% 2.74/0.99  
% 2.74/0.99  --abstr_ref                             []
% 2.74/0.99  --abstr_ref_prep                        false
% 2.74/0.99  --abstr_ref_until_sat                   false
% 2.74/0.99  --abstr_ref_sig_restrict                funpre
% 2.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.99  --abstr_ref_under                       []
% 2.74/0.99  
% 2.74/0.99  ------ SAT Options
% 2.74/0.99  
% 2.74/0.99  --sat_mode                              false
% 2.74/0.99  --sat_fm_restart_options                ""
% 2.74/0.99  --sat_gr_def                            false
% 2.74/0.99  --sat_epr_types                         true
% 2.74/0.99  --sat_non_cyclic_types                  false
% 2.74/0.99  --sat_finite_models                     false
% 2.74/0.99  --sat_fm_lemmas                         false
% 2.74/0.99  --sat_fm_prep                           false
% 2.74/0.99  --sat_fm_uc_incr                        true
% 2.74/0.99  --sat_out_model                         small
% 2.74/0.99  --sat_out_clauses                       false
% 2.74/0.99  
% 2.74/0.99  ------ QBF Options
% 2.74/0.99  
% 2.74/0.99  --qbf_mode                              false
% 2.74/0.99  --qbf_elim_univ                         false
% 2.74/0.99  --qbf_dom_inst                          none
% 2.74/0.99  --qbf_dom_pre_inst                      false
% 2.74/0.99  --qbf_sk_in                             false
% 2.74/0.99  --qbf_pred_elim                         true
% 2.74/0.99  --qbf_split                             512
% 2.74/0.99  
% 2.74/0.99  ------ BMC1 Options
% 2.74/0.99  
% 2.74/0.99  --bmc1_incremental                      false
% 2.74/0.99  --bmc1_axioms                           reachable_all
% 2.74/0.99  --bmc1_min_bound                        0
% 2.74/0.99  --bmc1_max_bound                        -1
% 2.74/0.99  --bmc1_max_bound_default                -1
% 2.74/0.99  --bmc1_symbol_reachability              true
% 2.74/0.99  --bmc1_property_lemmas                  false
% 2.74/0.99  --bmc1_k_induction                      false
% 2.74/0.99  --bmc1_non_equiv_states                 false
% 2.74/0.99  --bmc1_deadlock                         false
% 2.74/0.99  --bmc1_ucm                              false
% 2.74/0.99  --bmc1_add_unsat_core                   none
% 2.74/0.99  --bmc1_unsat_core_children              false
% 2.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.99  --bmc1_out_stat                         full
% 2.74/0.99  --bmc1_ground_init                      false
% 2.74/0.99  --bmc1_pre_inst_next_state              false
% 2.74/0.99  --bmc1_pre_inst_state                   false
% 2.74/0.99  --bmc1_pre_inst_reach_state             false
% 2.74/0.99  --bmc1_out_unsat_core                   false
% 2.74/0.99  --bmc1_aig_witness_out                  false
% 2.74/0.99  --bmc1_verbose                          false
% 2.74/0.99  --bmc1_dump_clauses_tptp                false
% 2.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.99  --bmc1_dump_file                        -
% 2.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.99  --bmc1_ucm_extend_mode                  1
% 2.74/0.99  --bmc1_ucm_init_mode                    2
% 2.74/0.99  --bmc1_ucm_cone_mode                    none
% 2.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.99  --bmc1_ucm_relax_model                  4
% 2.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.99  --bmc1_ucm_layered_model                none
% 2.74/0.99  --bmc1_ucm_max_lemma_size               10
% 2.74/0.99  
% 2.74/0.99  ------ AIG Options
% 2.74/0.99  
% 2.74/0.99  --aig_mode                              false
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation Options
% 2.74/0.99  
% 2.74/0.99  --instantiation_flag                    true
% 2.74/0.99  --inst_sos_flag                         false
% 2.74/0.99  --inst_sos_phase                        true
% 2.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel_side                     none
% 2.74/0.99  --inst_solver_per_active                1400
% 2.74/0.99  --inst_solver_calls_frac                1.
% 2.74/0.99  --inst_passive_queue_type               priority_queues
% 2.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.99  --inst_passive_queues_freq              [25;2]
% 2.74/0.99  --inst_dismatching                      true
% 2.74/0.99  --inst_eager_unprocessed_to_passive     true
% 2.74/0.99  --inst_prop_sim_given                   true
% 2.74/0.99  --inst_prop_sim_new                     false
% 2.74/0.99  --inst_subs_new                         false
% 2.74/0.99  --inst_eq_res_simp                      false
% 2.74/0.99  --inst_subs_given                       false
% 2.74/0.99  --inst_orphan_elimination               true
% 2.74/0.99  --inst_learning_loop_flag               true
% 2.74/0.99  --inst_learning_start                   3000
% 2.74/0.99  --inst_learning_factor                  2
% 2.74/0.99  --inst_start_prop_sim_after_learn       3
% 2.74/0.99  --inst_sel_renew                        solver
% 2.74/0.99  --inst_lit_activity_flag                true
% 2.74/0.99  --inst_restr_to_given                   false
% 2.74/0.99  --inst_activity_threshold               500
% 2.74/0.99  --inst_out_proof                        true
% 2.74/0.99  
% 2.74/0.99  ------ Resolution Options
% 2.74/0.99  
% 2.74/0.99  --resolution_flag                       false
% 2.74/0.99  --res_lit_sel                           adaptive
% 2.74/0.99  --res_lit_sel_side                      none
% 2.74/0.99  --res_ordering                          kbo
% 2.74/0.99  --res_to_prop_solver                    active
% 2.74/0.99  --res_prop_simpl_new                    false
% 2.74/0.99  --res_prop_simpl_given                  true
% 2.74/0.99  --res_passive_queue_type                priority_queues
% 2.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.99  --res_passive_queues_freq               [15;5]
% 2.74/0.99  --res_forward_subs                      full
% 2.74/0.99  --res_backward_subs                     full
% 2.74/0.99  --res_forward_subs_resolution           true
% 2.74/0.99  --res_backward_subs_resolution          true
% 2.74/0.99  --res_orphan_elimination                true
% 2.74/0.99  --res_time_limit                        2.
% 2.74/0.99  --res_out_proof                         true
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Options
% 2.74/0.99  
% 2.74/0.99  --superposition_flag                    true
% 2.74/0.99  --sup_passive_queue_type                priority_queues
% 2.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.99  --demod_completeness_check              fast
% 2.74/0.99  --demod_use_ground                      true
% 2.74/0.99  --sup_to_prop_solver                    passive
% 2.74/0.99  --sup_prop_simpl_new                    true
% 2.74/0.99  --sup_prop_simpl_given                  true
% 2.74/0.99  --sup_fun_splitting                     false
% 2.74/0.99  --sup_smt_interval                      50000
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Simplification Setup
% 2.74/0.99  
% 2.74/0.99  --sup_indices_passive                   []
% 2.74/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_full_bw                           [BwDemod]
% 2.74/0.99  --sup_immed_triv                        [TrivRules]
% 2.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_immed_bw_main                     []
% 2.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  
% 2.74/0.99  ------ Combination Options
% 2.74/0.99  
% 2.74/0.99  --comb_res_mult                         3
% 2.74/0.99  --comb_sup_mult                         2
% 2.74/0.99  --comb_inst_mult                        10
% 2.74/0.99  
% 2.74/0.99  ------ Debug Options
% 2.74/0.99  
% 2.74/0.99  --dbg_backtrace                         false
% 2.74/0.99  --dbg_dump_prop_clauses                 false
% 2.74/0.99  --dbg_dump_prop_clauses_file            -
% 2.74/0.99  --dbg_out_stat                          false
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  ------ Proving...
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS status Theorem for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  fof(f5,axiom,(
% 2.74/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f58,plain,(
% 2.74/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f5])).
% 2.74/0.99  
% 2.74/0.99  fof(f6,axiom,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f36,plain,(
% 2.74/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.74/0.99    inference(nnf_transformation,[],[f6])).
% 2.74/0.99  
% 2.74/0.99  fof(f59,plain,(
% 2.74/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f36])).
% 2.74/0.99  
% 2.74/0.99  fof(f3,axiom,(
% 2.74/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f32,plain,(
% 2.74/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.74/0.99    inference(nnf_transformation,[],[f3])).
% 2.74/0.99  
% 2.74/0.99  fof(f33,plain,(
% 2.74/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.74/0.99    inference(flattening,[],[f32])).
% 2.74/0.99  
% 2.74/0.99  fof(f52,plain,(
% 2.74/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.74/0.99    inference(cnf_transformation,[],[f33])).
% 2.74/0.99  
% 2.74/0.99  fof(f90,plain,(
% 2.74/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.74/0.99    inference(equality_resolution,[],[f52])).
% 2.74/0.99  
% 2.74/0.99  fof(f1,axiom,(
% 2.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f14,plain,(
% 2.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f1])).
% 2.74/0.99  
% 2.74/0.99  fof(f28,plain,(
% 2.74/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/0.99    inference(nnf_transformation,[],[f14])).
% 2.74/0.99  
% 2.74/0.99  fof(f29,plain,(
% 2.74/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/0.99    inference(rectify,[],[f28])).
% 2.74/0.99  
% 2.74/0.99  fof(f30,plain,(
% 2.74/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f31,plain,(
% 2.74/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 2.74/0.99  
% 2.74/0.99  fof(f49,plain,(
% 2.74/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f8,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f17,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.74/0.99    inference(ennf_transformation,[],[f8])).
% 2.74/0.99  
% 2.74/0.99  fof(f62,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f17])).
% 2.74/0.99  
% 2.74/0.99  fof(f60,plain,(
% 2.74/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f36])).
% 2.74/0.99  
% 2.74/0.99  fof(f10,axiom,(
% 2.74/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f19,plain,(
% 2.74/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.74/0.99    inference(ennf_transformation,[],[f10])).
% 2.74/0.99  
% 2.74/0.99  fof(f20,plain,(
% 2.74/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.74/0.99    inference(flattening,[],[f19])).
% 2.74/0.99  
% 2.74/0.99  fof(f65,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f20])).
% 2.74/0.99  
% 2.74/0.99  fof(f12,conjecture,(
% 2.74/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f13,negated_conjecture,(
% 2.74/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.74/0.99    inference(negated_conjecture,[],[f12])).
% 2.74/0.99  
% 2.74/0.99  fof(f23,plain,(
% 2.74/0.99    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.74/0.99    inference(ennf_transformation,[],[f13])).
% 2.74/0.99  
% 2.74/0.99  fof(f24,plain,(
% 2.74/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.74/0.99    inference(flattening,[],[f23])).
% 2.74/0.99  
% 2.74/0.99  fof(f46,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(sK9,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK9) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK9,X0,X1) & v1_funct_1(sK9))) )),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f45,plain,(
% 2.74/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK6,sK7,sK8)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK7) & r1_partfun1(sK8,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(X3,sK6,sK7) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK8))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f47,plain,(
% 2.74/0.99    (~r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK7) & r1_partfun1(sK8,sK9) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK9,sK6,sK7) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK8)),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f24,f46,f45])).
% 2.74/0.99  
% 2.74/0.99  fof(f84,plain,(
% 2.74/0.99    v1_funct_2(sK9,sK6,sK7)),
% 2.74/0.99    inference(cnf_transformation,[],[f47])).
% 2.74/0.99  
% 2.74/0.99  fof(f83,plain,(
% 2.74/0.99    v1_funct_1(sK9)),
% 2.74/0.99    inference(cnf_transformation,[],[f47])).
% 2.74/0.99  
% 2.74/0.99  fof(f85,plain,(
% 2.74/0.99    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 2.74/0.99    inference(cnf_transformation,[],[f47])).
% 2.74/0.99  
% 2.74/0.99  fof(f54,plain,(
% 2.74/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f33])).
% 2.74/0.99  
% 2.74/0.99  fof(f81,plain,(
% 2.74/0.99    v1_funct_1(sK8)),
% 2.74/0.99    inference(cnf_transformation,[],[f47])).
% 2.74/0.99  
% 2.74/0.99  fof(f82,plain,(
% 2.74/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 2.74/0.99    inference(cnf_transformation,[],[f47])).
% 2.74/0.99  
% 2.74/0.99  fof(f86,plain,(
% 2.74/0.99    r1_partfun1(sK8,sK9)),
% 2.74/0.99    inference(cnf_transformation,[],[f47])).
% 2.74/0.99  
% 2.74/0.99  fof(f88,plain,(
% 2.74/0.99    ~r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8))),
% 2.74/0.99    inference(cnf_transformation,[],[f47])).
% 2.74/0.99  
% 2.74/0.99  fof(f26,plain,(
% 2.74/0.99    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 2.74/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.74/0.99  
% 2.74/0.99  fof(f37,plain,(
% 2.74/0.99    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 2.74/0.99    inference(nnf_transformation,[],[f26])).
% 2.74/0.99  
% 2.74/0.99  fof(f38,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 2.74/0.99    inference(rectify,[],[f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f66,plain,(
% 2.74/0.99    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f38])).
% 2.74/0.99  
% 2.74/0.99  fof(f93,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 2.74/0.99    inference(equality_resolution,[],[f66])).
% 2.74/0.99  
% 2.74/0.99  fof(f11,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f21,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.74/0.99    inference(ennf_transformation,[],[f11])).
% 2.74/0.99  
% 2.74/0.99  fof(f22,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.74/0.99    inference(flattening,[],[f21])).
% 2.74/0.99  
% 2.74/0.99  fof(f25,plain,(
% 2.74/0.99    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 2.74/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.74/0.99  
% 2.74/0.99  fof(f27,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.74/0.99    inference(definition_folding,[],[f22,f26,f25])).
% 2.74/0.99  
% 2.74/0.99  fof(f80,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f27])).
% 2.74/0.99  
% 2.74/0.99  fof(f2,axiom,(
% 2.74/0.99    v1_xboole_0(k1_xboole_0)),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f51,plain,(
% 2.74/0.99    v1_xboole_0(k1_xboole_0)),
% 2.74/0.99    inference(cnf_transformation,[],[f2])).
% 2.74/0.99  
% 2.74/0.99  fof(f39,plain,(
% 2.74/0.99    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 2.74/0.99    inference(nnf_transformation,[],[f25])).
% 2.74/0.99  
% 2.74/0.99  fof(f40,plain,(
% 2.74/0.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.74/0.99    inference(rectify,[],[f39])).
% 2.74/0.99  
% 2.74/0.99  fof(f43,plain,(
% 2.74/0.99    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f42,plain,(
% 2.74/0.99    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK4(X0,X1,X2,X3) = X4 & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))))) )),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f41,plain,(
% 2.74/0.99    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK3(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f44,plain,(
% 2.74/0.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))) | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).
% 2.74/0.99  
% 2.74/0.99  fof(f73,plain,(
% 2.74/0.99    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f44])).
% 2.74/0.99  
% 2.74/0.99  fof(f95,plain,(
% 2.74/0.99    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.74/0.99    inference(equality_resolution,[],[f73])).
% 2.74/0.99  
% 2.74/0.99  fof(f87,plain,(
% 2.74/0.99    k1_xboole_0 = sK6 | k1_xboole_0 != sK7),
% 2.74/0.99    inference(cnf_transformation,[],[f47])).
% 2.74/0.99  
% 2.74/0.99  fof(f4,axiom,(
% 2.74/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f34,plain,(
% 2.74/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.74/0.99    inference(nnf_transformation,[],[f4])).
% 2.74/0.99  
% 2.74/0.99  fof(f35,plain,(
% 2.74/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.74/0.99    inference(flattening,[],[f34])).
% 2.74/0.99  
% 2.74/0.99  fof(f56,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.74/0.99    inference(cnf_transformation,[],[f35])).
% 2.74/0.99  
% 2.74/0.99  fof(f92,plain,(
% 2.74/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.74/0.99    inference(equality_resolution,[],[f56])).
% 2.74/0.99  
% 2.74/0.99  fof(f9,axiom,(
% 2.74/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f18,plain,(
% 2.74/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.74/0.99    inference(ennf_transformation,[],[f9])).
% 2.74/0.99  
% 2.74/0.99  fof(f63,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f18])).
% 2.74/0.99  
% 2.74/0.99  cnf(c_10,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5182,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_12,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5180,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5912,plain,
% 2.74/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_5182,c_5180]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6,plain,
% 2.74/0.99      ( r1_tarski(X0,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5183,plain,
% 2.74/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1,plain,
% 2.74/0.99      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5186,plain,
% 2.74/0.99      ( r2_hidden(sK2(X0,X1),X0) = iProver_top
% 2.74/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_14,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.99      | ~ r2_hidden(X2,X0)
% 2.74/0.99      | ~ v1_xboole_0(X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_11,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_280,plain,
% 2.74/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.74/0.99      inference(prop_impl,[status(thm)],[c_11]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_281,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_280]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_352,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.74/0.99      inference(bin_hyper_res,[status(thm)],[c_14,c_281]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_16,plain,
% 2.74/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.99      | v1_partfun1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | v1_xboole_0(X2) ),
% 2.74/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_37,negated_conjecture,
% 2.74/0.99      ( v1_funct_2(sK9,sK6,sK7) ),
% 2.74/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_474,plain,
% 2.74/0.99      ( v1_partfun1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | v1_xboole_0(X2)
% 2.74/0.99      | sK7 != X2
% 2.74/0.99      | sK6 != X1
% 2.74/0.99      | sK9 != X0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_475,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6)
% 2.74/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 2.74/0.99      | ~ v1_funct_1(sK9)
% 2.74/0.99      | v1_xboole_0(sK7) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_474]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_38,negated_conjecture,
% 2.74/0.99      ( v1_funct_1(sK9) ),
% 2.74/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_36,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 2.74/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_477,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6) | v1_xboole_0(sK7) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_475,c_38,c_36]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_572,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6)
% 2.74/0.99      | ~ r2_hidden(X0,X1)
% 2.74/0.99      | ~ r1_tarski(X1,X2)
% 2.74/0.99      | sK7 != X2 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_352,c_477]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_573,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6) | ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,sK7) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_572]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5155,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6) = iProver_top
% 2.74/0.99      | r2_hidden(X0,X1) != iProver_top
% 2.74/0.99      | r1_tarski(X1,sK7) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6323,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6) = iProver_top
% 2.74/0.99      | r1_tarski(X0,X1) = iProver_top
% 2.74/0.99      | r1_tarski(X0,sK7) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_5186,c_5155]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6536,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6) = iProver_top
% 2.74/0.99      | r1_tarski(sK7,X0) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_5183,c_6323]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4,plain,
% 2.74/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5184,plain,
% 2.74/0.99      ( X0 = X1
% 2.74/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.74/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6826,plain,
% 2.74/0.99      ( sK7 = X0
% 2.74/0.99      | v1_partfun1(sK9,sK6) = iProver_top
% 2.74/0.99      | r1_tarski(X0,sK7) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_6536,c_5184]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_40,negated_conjecture,
% 2.74/0.99      ( v1_funct_1(sK8) ),
% 2.74/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_39,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 2.74/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_35,negated_conjecture,
% 2.74/0.99      ( r1_partfun1(sK8,sK9) ),
% 2.74/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_33,negated_conjecture,
% 2.74/0.99      ( ~ r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_107,plain,
% 2.74/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.74/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_113,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_112,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5522,plain,
% 2.74/0.99      ( r2_hidden(sK2(k1_xboole_0,sK7),k1_xboole_0)
% 2.74/0.99      | r1_tarski(k1_xboole_0,sK7) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5563,plain,
% 2.74/0.99      ( ~ r1_tarski(X0,sK7) | ~ r1_tarski(sK7,X0) | sK7 = X0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5564,plain,
% 2.74/0.99      ( sK7 = X0
% 2.74/0.99      | r1_tarski(X0,sK7) != iProver_top
% 2.74/0.99      | r1_tarski(sK7,X0) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5563]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_19,plain,
% 2.74/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_32,plain,
% 2.74/0.99      ( sP1(X0,X1,X2)
% 2.74/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.74/0.99      | ~ v1_funct_1(X2) ),
% 2.74/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_491,plain,
% 2.74/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.74/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.74/0.99      | ~ v1_funct_1(X3)
% 2.74/0.99      | X4 != X1
% 2.74/0.99      | X3 != X0
% 2.74/0.99      | X5 != X2 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_492,plain,
% 2.74/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | ~ v1_funct_1(X0) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_491]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5492,plain,
% 2.74/0.99      ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8))
% 2.74/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.99      | ~ v1_funct_1(sK8) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_492]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5597,plain,
% 2.74/0.99      ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
% 2.74/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 2.74/0.99      | ~ v1_funct_1(sK8) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5492]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4379,plain,( X0 = X0 ),theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5632,plain,
% 2.74/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_4379]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5926,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0)) | r1_tarski(sK7,X0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5927,plain,
% 2.74/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(X0)) != iProver_top
% 2.74/0.99      | r1_tarski(sK7,X0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5926]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3,plain,
% 2.74/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_545,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_352]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_546,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_545]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6176,plain,
% 2.74/0.99      ( ~ r2_hidden(sK2(k1_xboole_0,sK7),k1_xboole_0)
% 2.74/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_546]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6848,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6) | ~ r1_tarski(X0,sK7) | sK7 = X0 ),
% 2.74/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6826]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6850,plain,
% 2.74/0.99      ( v1_partfun1(sK9,sK6)
% 2.74/0.99      | ~ r1_tarski(k1_xboole_0,sK7)
% 2.74/0.99      | sK7 = k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_6848]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4385,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5474,plain,
% 2.74/0.99      ( m1_subset_1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 2.74/0.99      | X1 != k1_zfmisc_1(X2)
% 2.74/0.99      | X0 != k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_4385]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5631,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 2.74/0.99      | X0 != k1_xboole_0
% 2.74/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5474]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6954,plain,
% 2.74/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(X0))
% 2.74/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 2.74/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
% 2.74/0.99      | sK7 != k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5631]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6958,plain,
% 2.74/0.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
% 2.74/0.99      | sK7 != k1_xboole_0
% 2.74/0.99      | m1_subset_1(sK7,k1_zfmisc_1(X0)) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_6954]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_26,plain,
% 2.74/0.99      ( ~ sP0(X0,X1,X2,X3)
% 2.74/0.99      | ~ r1_partfun1(X0,X4)
% 2.74/0.99      | ~ v1_partfun1(X4,X1)
% 2.74/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | r2_hidden(X4,X3)
% 2.74/0.99      | ~ v1_funct_1(X4) ),
% 2.74/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5507,plain,
% 2.74/0.99      ( ~ sP0(X0,X1,X2,X3)
% 2.74/0.99      | ~ r1_partfun1(X0,sK9)
% 2.74/0.99      | ~ v1_partfun1(sK9,X1)
% 2.74/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | r2_hidden(sK9,X3)
% 2.74/0.99      | ~ v1_funct_1(sK9) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5618,plain,
% 2.74/0.99      ( ~ sP0(sK8,X0,X1,X2)
% 2.74/0.99      | ~ r1_partfun1(sK8,sK9)
% 2.74/0.99      | ~ v1_partfun1(sK9,X0)
% 2.74/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.99      | r2_hidden(sK9,X2)
% 2.74/0.99      | ~ v1_funct_1(sK9) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5507]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5738,plain,
% 2.74/0.99      ( ~ sP0(sK8,sK6,X0,X1)
% 2.74/0.99      | ~ r1_partfun1(sK8,sK9)
% 2.74/0.99      | ~ v1_partfun1(sK9,sK6)
% 2.74/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,X0)))
% 2.74/0.99      | r2_hidden(sK9,X1)
% 2.74/0.99      | ~ v1_funct_1(sK9) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5618]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6583,plain,
% 2.74/0.99      ( ~ sP0(sK8,sK6,sK7,X0)
% 2.74/0.99      | ~ r1_partfun1(sK8,sK9)
% 2.74/0.99      | ~ v1_partfun1(sK9,sK6)
% 2.74/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 2.74/0.99      | r2_hidden(sK9,X0)
% 2.74/0.99      | ~ v1_funct_1(sK9) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5738]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7547,plain,
% 2.74/0.99      ( ~ sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
% 2.74/0.99      | ~ r1_partfun1(sK8,sK9)
% 2.74/0.99      | ~ v1_partfun1(sK9,sK6)
% 2.74/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 2.74/0.99      | r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8))
% 2.74/0.99      | ~ v1_funct_1(sK9) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_6583]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7551,plain,
% 2.74/0.99      ( sK7 = X0 | r1_tarski(X0,sK7) != iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_6826,c_40,c_39,c_38,c_36,c_35,c_33,c_107,c_113,c_112,
% 2.74/0.99                 c_5522,c_5564,c_5597,c_5632,c_5927,c_6176,c_6850,c_6958,
% 2.74/0.99                 c_7547]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7560,plain,
% 2.74/0.99      ( sK7 = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_5912,c_7551]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5166,plain,
% 2.74/0.99      ( r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7586,plain,
% 2.74/0.99      ( r2_hidden(sK9,k5_partfun1(sK6,k1_xboole_0,sK8)) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_7560,c_5166]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_34,negated_conjecture,
% 2.74/0.99      ( k1_xboole_0 != sK7 | k1_xboole_0 = sK6 ),
% 2.74/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7589,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_7560,c_34]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7590,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0 ),
% 2.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_7589]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7601,plain,
% 2.74/0.99      ( r2_hidden(sK9,k5_partfun1(k1_xboole_0,k1_xboole_0,sK8)) != iProver_top ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_7586,c_7590]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5164,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7587,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_7560,c_5164]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7597,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_7587,c_7590]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_8,plain,
% 2.74/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7599,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_7597,c_8]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5162,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7588,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_7560,c_5162]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7593,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_7588,c_7590]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7595,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_7593,c_8]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6892,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0)) | r1_tarski(sK8,X0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6893,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(X0)) != iProver_top
% 2.74/0.99      | r1_tarski(sK8,X0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_6892]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6895,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_6893]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6681,plain,
% 2.74/0.99      ( ~ sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8))
% 2.74/0.99      | ~ r1_partfun1(sK8,sK9)
% 2.74/0.99      | ~ v1_partfun1(sK9,X0)
% 2.74/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.99      | r2_hidden(sK9,k5_partfun1(X0,X1,sK8))
% 2.74/0.99      | ~ v1_funct_1(sK9) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5618]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6682,plain,
% 2.74/0.99      ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8)) != iProver_top
% 2.74/0.99      | r1_partfun1(sK8,sK9) != iProver_top
% 2.74/0.99      | v1_partfun1(sK9,X0) != iProver_top
% 2.74/0.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.74/0.99      | r2_hidden(sK9,k5_partfun1(X0,X1,sK8)) = iProver_top
% 2.74/0.99      | v1_funct_1(sK9) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_6681]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6684,plain,
% 2.74/0.99      ( sP0(sK8,k1_xboole_0,k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK8)) != iProver_top
% 2.74/0.99      | r1_partfun1(sK8,sK9) != iProver_top
% 2.74/0.99      | v1_partfun1(sK9,k1_xboole_0) != iProver_top
% 2.74/0.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 2.74/0.99      | r2_hidden(sK9,k5_partfun1(k1_xboole_0,k1_xboole_0,sK8)) = iProver_top
% 2.74/0.99      | v1_funct_1(sK9) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_6682]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6504,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(X0)) | r1_tarski(sK9,X0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6505,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(X0)) != iProver_top
% 2.74/0.99      | r1_tarski(sK9,X0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_6504]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6507,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_6505]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4381,plain,
% 2.74/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5997,plain,
% 2.74/0.99      ( ~ r1_tarski(sK8,X0)
% 2.74/0.99      | r1_tarski(sK8,k2_zfmisc_1(X1,X2))
% 2.74/0.99      | k2_zfmisc_1(X1,X2) != X0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_4381]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5998,plain,
% 2.74/0.99      ( k2_zfmisc_1(X0,X1) != X2
% 2.74/0.99      | r1_tarski(sK8,X2) != iProver_top
% 2.74/0.99      | r1_tarski(sK8,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5997]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6000,plain,
% 2.74/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.74/0.99      | r1_tarski(sK8,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 2.74/0.99      | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5998]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5977,plain,
% 2.74/0.99      ( ~ r1_tarski(sK9,X0)
% 2.74/0.99      | r1_tarski(sK9,k2_zfmisc_1(X1,X2))
% 2.74/0.99      | k2_zfmisc_1(X1,X2) != X0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_4381]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5978,plain,
% 2.74/0.99      ( k2_zfmisc_1(X0,X1) != X2
% 2.74/0.99      | r1_tarski(sK9,X2) != iProver_top
% 2.74/0.99      | r1_tarski(sK9,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5977]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5980,plain,
% 2.74/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.74/0.99      | r1_tarski(sK9,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 2.74/0.99      | r1_tarski(sK9,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5978]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_15,plain,
% 2.74/0.99      ( v1_partfun1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | ~ v1_xboole_0(X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_533,plain,
% 2.74/0.99      ( v1_partfun1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k1_xboole_0 != X1 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_534,plain,
% 2.74/0.99      ( v1_partfun1(X0,k1_xboole_0)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_533]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5744,plain,
% 2.74/0.99      ( v1_partfun1(sK9,k1_xboole_0)
% 2.74/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_534]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5747,plain,
% 2.74/0.99      ( v1_partfun1(sK9,k1_xboole_0) = iProver_top
% 2.74/0.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5744]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5749,plain,
% 2.74/0.99      ( v1_partfun1(sK9,k1_xboole_0) = iProver_top
% 2.74/0.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5747]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5592,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.99      | ~ r1_tarski(sK8,k2_zfmisc_1(X0,X1)) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5593,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.74/0.99      | r1_tarski(sK8,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5592]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5595,plain,
% 2.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 2.74/0.99      | r1_tarski(sK8,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5593]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5584,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.99      | ~ r1_tarski(sK9,k2_zfmisc_1(X0,X1)) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5585,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.74/0.99      | r1_tarski(sK9,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5584]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5587,plain,
% 2.74/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 2.74/0.99      | r1_tarski(sK9,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_5585]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_917,plain,
% 2.74/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | sK8 != X0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_492,c_40]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_918,plain,
% 2.74/0.99      ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8))
% 2.74/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_917]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_919,plain,
% 2.74/0.99      ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8)) = iProver_top
% 2.74/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_921,plain,
% 2.74/0.99      ( sP0(sK8,k1_xboole_0,k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK8)) = iProver_top
% 2.74/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_919]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_116,plain,
% 2.74/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_46,plain,
% 2.74/0.99      ( r1_partfun1(sK8,sK9) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_43,plain,
% 2.74/0.99      ( v1_funct_1(sK9) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(contradiction,plain,
% 2.74/0.99      ( $false ),
% 2.74/0.99      inference(minisat,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_7601,c_7599,c_7595,c_6895,c_6684,c_6507,c_6000,c_5980,
% 2.74/0.99                 c_5749,c_5595,c_5587,c_921,c_116,c_46,c_43]) ).
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  ------                               Statistics
% 2.74/0.99  
% 2.74/0.99  ------ General
% 2.74/0.99  
% 2.74/0.99  abstr_ref_over_cycles:                  0
% 2.74/0.99  abstr_ref_under_cycles:                 0
% 2.74/0.99  gc_basic_clause_elim:                   0
% 2.74/0.99  forced_gc_time:                         0
% 2.74/0.99  parsing_time:                           0.01
% 2.74/0.99  unif_index_cands_time:                  0.
% 2.74/0.99  unif_index_add_time:                    0.
% 2.74/0.99  orderings_time:                         0.
% 2.74/0.99  out_proof_time:                         0.011
% 2.74/0.99  total_time:                             0.208
% 2.74/0.99  num_of_symbols:                         53
% 2.74/0.99  num_of_terms:                           4171
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing
% 2.74/0.99  
% 2.74/0.99  num_of_splits:                          0
% 2.74/0.99  num_of_split_atoms:                     0
% 2.74/0.99  num_of_reused_defs:                     0
% 2.74/0.99  num_eq_ax_congr_red:                    59
% 2.74/0.99  num_of_sem_filtered_clauses:            1
% 2.74/0.99  num_of_subtypes:                        0
% 2.74/0.99  monotx_restored_types:                  0
% 2.74/0.99  sat_num_of_epr_types:                   0
% 2.74/0.99  sat_num_of_non_cyclic_types:            0
% 2.74/0.99  sat_guarded_non_collapsed_types:        0
% 2.74/0.99  num_pure_diseq_elim:                    0
% 2.74/0.99  simp_replaced_by:                       0
% 2.74/0.99  res_preprocessed:                       175
% 2.74/0.99  prep_upred:                             0
% 2.74/0.99  prep_unflattend:                        111
% 2.74/0.99  smt_new_axioms:                         0
% 2.74/0.99  pred_elim_cands:                        7
% 2.74/0.99  pred_elim:                              3
% 2.74/0.99  pred_elim_cl:                           2
% 2.74/0.99  pred_elim_cycles:                       9
% 2.74/0.99  merged_defs:                            8
% 2.74/0.99  merged_defs_ncl:                        0
% 2.74/0.99  bin_hyper_res:                          9
% 2.74/0.99  prep_cycles:                            4
% 2.74/0.99  pred_elim_time:                         0.085
% 2.74/0.99  splitting_time:                         0.
% 2.74/0.99  sem_filter_time:                        0.
% 2.74/0.99  monotx_time:                            0.001
% 2.74/0.99  subtype_inf_time:                       0.
% 2.74/0.99  
% 2.74/0.99  ------ Problem properties
% 2.74/0.99  
% 2.74/0.99  clauses:                                37
% 2.74/0.99  conjectures:                            7
% 2.74/0.99  epr:                                    9
% 2.74/0.99  horn:                                   29
% 2.74/0.99  ground:                                 7
% 2.74/0.99  unary:                                  10
% 2.74/0.99  binary:                                 7
% 2.74/0.99  lits:                                   91
% 2.74/0.99  lits_eq:                                11
% 2.74/0.99  fd_pure:                                0
% 2.74/0.99  fd_pseudo:                              0
% 2.74/0.99  fd_cond:                                1
% 2.74/0.99  fd_pseudo_cond:                         2
% 2.74/0.99  ac_symbols:                             0
% 2.74/0.99  
% 2.74/0.99  ------ Propositional Solver
% 2.74/0.99  
% 2.74/0.99  prop_solver_calls:                      27
% 2.74/0.99  prop_fast_solver_calls:                 1752
% 2.74/0.99  smt_solver_calls:                       0
% 2.74/0.99  smt_fast_solver_calls:                  0
% 2.74/0.99  prop_num_of_clauses:                    1552
% 2.74/0.99  prop_preprocess_simplified:             7564
% 2.74/0.99  prop_fo_subsumed:                       9
% 2.74/0.99  prop_solver_time:                       0.
% 2.74/0.99  smt_solver_time:                        0.
% 2.74/0.99  smt_fast_solver_time:                   0.
% 2.74/0.99  prop_fast_solver_time:                  0.
% 2.74/0.99  prop_unsat_core_time:                   0.
% 2.74/0.99  
% 2.74/0.99  ------ QBF
% 2.74/0.99  
% 2.74/0.99  qbf_q_res:                              0
% 2.74/0.99  qbf_num_tautologies:                    0
% 2.74/0.99  qbf_prep_cycles:                        0
% 2.74/0.99  
% 2.74/0.99  ------ BMC1
% 2.74/0.99  
% 2.74/0.99  bmc1_current_bound:                     -1
% 2.74/0.99  bmc1_last_solved_bound:                 -1
% 2.74/0.99  bmc1_unsat_core_size:                   -1
% 2.74/0.99  bmc1_unsat_core_parents_size:           -1
% 2.74/0.99  bmc1_merge_next_fun:                    0
% 2.74/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation
% 2.74/0.99  
% 2.74/0.99  inst_num_of_clauses:                    441
% 2.74/0.99  inst_num_in_passive:                    239
% 2.74/0.99  inst_num_in_active:                     186
% 2.74/0.99  inst_num_in_unprocessed:                16
% 2.74/0.99  inst_num_of_loops:                      220
% 2.74/0.99  inst_num_of_learning_restarts:          0
% 2.74/0.99  inst_num_moves_active_passive:          31
% 2.74/0.99  inst_lit_activity:                      0
% 2.74/0.99  inst_lit_activity_moves:                0
% 2.74/0.99  inst_num_tautologies:                   0
% 2.74/0.99  inst_num_prop_implied:                  0
% 2.74/0.99  inst_num_existing_simplified:           0
% 2.74/0.99  inst_num_eq_res_simplified:             0
% 2.74/0.99  inst_num_child_elim:                    0
% 2.74/0.99  inst_num_of_dismatching_blockings:      40
% 2.74/0.99  inst_num_of_non_proper_insts:           280
% 2.74/0.99  inst_num_of_duplicates:                 0
% 2.74/0.99  inst_inst_num_from_inst_to_res:         0
% 2.74/0.99  inst_dismatching_checking_time:         0.
% 2.74/0.99  
% 2.74/0.99  ------ Resolution
% 2.74/0.99  
% 2.74/0.99  res_num_of_clauses:                     0
% 2.74/0.99  res_num_in_passive:                     0
% 2.74/0.99  res_num_in_active:                      0
% 2.74/0.99  res_num_of_loops:                       179
% 2.74/0.99  res_forward_subset_subsumed:            25
% 2.74/0.99  res_backward_subset_subsumed:           0
% 2.74/0.99  res_forward_subsumed:                   0
% 2.74/0.99  res_backward_subsumed:                  0
% 2.74/0.99  res_forward_subsumption_resolution:     2
% 2.74/0.99  res_backward_subsumption_resolution:    0
% 2.74/0.99  res_clause_to_clause_subsumption:       305
% 2.74/0.99  res_orphan_elimination:                 0
% 2.74/0.99  res_tautology_del:                      28
% 2.74/0.99  res_num_eq_res_simplified:              0
% 2.74/0.99  res_num_sel_changes:                    0
% 2.74/0.99  res_moves_from_active_to_pass:          0
% 2.74/0.99  
% 2.74/0.99  ------ Superposition
% 2.74/0.99  
% 2.74/0.99  sup_time_total:                         0.
% 2.74/0.99  sup_time_generating:                    0.
% 2.74/0.99  sup_time_sim_full:                      0.
% 2.74/0.99  sup_time_sim_immed:                     0.
% 2.74/0.99  
% 2.74/0.99  sup_num_of_clauses:                     49
% 2.74/0.99  sup_num_in_active:                      20
% 2.74/0.99  sup_num_in_passive:                     29
% 2.74/0.99  sup_num_of_loops:                       43
% 2.74/0.99  sup_fw_superposition:                   35
% 2.74/0.99  sup_bw_superposition:                   13
% 2.74/0.99  sup_immediate_simplified:               22
% 2.74/0.99  sup_given_eliminated:                   1
% 2.74/0.99  comparisons_done:                       0
% 2.74/0.99  comparisons_avoided:                    0
% 2.74/0.99  
% 2.74/0.99  ------ Simplifications
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  sim_fw_subset_subsumed:                 5
% 2.74/0.99  sim_bw_subset_subsumed:                 0
% 2.74/0.99  sim_fw_subsumed:                        2
% 2.74/0.99  sim_bw_subsumed:                        0
% 2.74/0.99  sim_fw_subsumption_res:                 0
% 2.74/0.99  sim_bw_subsumption_res:                 0
% 2.74/0.99  sim_tautology_del:                      1
% 2.74/0.99  sim_eq_tautology_del:                   7
% 2.74/0.99  sim_eq_res_simp:                        1
% 2.74/0.99  sim_fw_demodulated:                     11
% 2.74/0.99  sim_bw_demodulated:                     23
% 2.74/0.99  sim_light_normalised:                   17
% 2.74/0.99  sim_joinable_taut:                      0
% 2.74/0.99  sim_joinable_simp:                      0
% 2.74/0.99  sim_ac_normalised:                      0
% 2.74/0.99  sim_smt_subsumption:                    0
% 2.74/0.99  
%------------------------------------------------------------------------------
