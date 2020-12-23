%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1047+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:46 EST 2020

% Result     : Theorem 15.74s
% Output     : CNFRefutation 15.74s
% Verified   : 
% Statistics : Number of formulae       :  260 (22531 expanded)
%              Number of clauses        :  179 (7306 expanded)
%              Number of leaves         :   24 (5403 expanded)
%              Depth                    :   32
%              Number of atoms          : 1044 (123839 expanded)
%              Number of equality atoms :  516 (39003 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f56])).

fof(f92,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f91])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
     => ( k1_tarski(sK10) != k5_partfun1(X0,k1_tarski(X1),X2)
        & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(sK10,X0,k1_tarski(X1))
        & v1_funct_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
          & v1_funct_2(X3,sK7,k1_tarski(sK8))
          & v1_funct_1(X3) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k1_tarski(sK10) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    & v1_funct_2(sK10,sK7,k1_tarski(sK8))
    & v1_funct_1(sK10)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f31,f51,f50])).

fof(f89,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v1_funct_2(sK10,sK7,k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f52])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f3,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f32,plain,(
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

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f17,f33,f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f42,f45,f44,f43])).

fof(f66,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f66])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    k1_tarski(sK10) != k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(cnf_transformation,[],[f52])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X1,X0,X2) = X3
      | ~ sP0(X2,X1,X0,X3)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK5(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK5(X0,X1,X2,X7),X1)
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f4,f47])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9271,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_9249,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_9274,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13753,plain,
    ( v1_funct_2(sK10,sK7,k1_tarski(sK8)) != iProver_top
    | v1_partfun1(sK10,sK7) = iProver_top
    | v1_xboole_0(k1_tarski(sK8)) = iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9249,c_9274])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK10,sK7,k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_41,plain,
    ( v1_funct_2(sK10,sK7,k1_tarski(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_15172,plain,
    ( v1_xboole_0(k1_tarski(sK8)) = iProver_top
    | v1_partfun1(sK10,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13753,c_40,c_41])).

cnf(c_15173,plain,
    ( v1_partfun1(sK10,sK7) = iProver_top
    | v1_xboole_0(k1_tarski(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_15172])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_20,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_405,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X5 != X2
    | X4 != X1
    | X3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_406,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_9244,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,X4)
    | r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X4,X1)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_9263,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13885,plain,
    ( sP0(X0,sK7,k1_tarski(sK8),X1) != iProver_top
    | r1_partfun1(X0,sK10) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9249,c_9263])).

cnf(c_14465,plain,
    ( v1_partfun1(sK10,sK7) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top
    | r1_partfun1(X0,sK10) != iProver_top
    | sP0(X0,sK7,k1_tarski(sK8),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13885,c_40])).

cnf(c_14466,plain,
    ( sP0(X0,sK7,k1_tarski(sK8),X1) != iProver_top
    | r1_partfun1(X0,sK10) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_14465])).

cnf(c_14475,plain,
    ( r1_partfun1(X0,sK10) != iProver_top
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9244,c_14466])).

cnf(c_24,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_9256,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13176,plain,
    ( r1_partfun1(X0,sK10) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9249,c_9256])).

cnf(c_15393,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14475,c_40,c_13176])).

cnf(c_15405,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9249,c_15393])).

cnf(c_42,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9613,plain,
    ( r1_partfun1(X0,sK10)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK10) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_9614,plain,
    ( r1_partfun1(X0,sK10) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9613])).

cnf(c_9616,plain,
    ( r1_partfun1(sK10,sK10) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9614])).

cnf(c_14477,plain,
    ( r1_partfun1(sK10,sK10) != iProver_top
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14475])).

cnf(c_15458,plain,
    ( v1_partfun1(sK10,sK7) != iProver_top
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15405,c_40,c_42,c_9616,c_14477])).

cnf(c_15459,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_15458])).

cnf(c_3,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9272,plain,
    ( sK2(X0,X1) = X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_9255,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12558,plain,
    ( k5_partfun1(X0,X1,X2) = k1_tarski(X3)
    | sK2(X3,k5_partfun1(X0,X1,X2)) = X3
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK2(X3,k5_partfun1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9272,c_9255])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,plain,
    ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
    | ~ v1_funct_2(X3,X0,k1_tarski(X1))
    | ~ v1_funct_2(X2,X0,k1_tarski(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,k1_tarski(X2))
    | ~ v1_funct_2(X3,X1,k1_tarski(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X1 != X5
    | X3 != X4
    | X0 != X7
    | X7 = X4
    | k1_tarski(X2) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_450,plain,
    ( ~ v1_funct_2(X0,X1,k1_tarski(X2))
    | ~ v1_funct_2(X3,X1,k1_tarski(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_9242,plain,
    ( X0 = X1
    | v1_funct_2(X1,X2,k1_tarski(X3)) != iProver_top
    | v1_funct_2(X0,X2,k1_tarski(X3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_9749,plain,
    ( sK10 = X0
    | v1_funct_2(X0,sK7,k1_tarski(sK8)) != iProver_top
    | v1_funct_2(sK10,sK7,k1_tarski(sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9249,c_9242])).

cnf(c_10121,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | sK10 = X0
    | v1_funct_2(X0,sK7,k1_tarski(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9749,c_40,c_41])).

cnf(c_10122,plain,
    ( sK10 = X0
    | v1_funct_2(X0,sK7,k1_tarski(sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10121])).

cnf(c_37769,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),X0) = k1_tarski(X1)
    | sK2(X1,k5_partfun1(sK7,k1_tarski(sK8),X0)) = X1
    | sK2(X1,k5_partfun1(sK7,k1_tarski(sK8),X0)) = sK10
    | v1_funct_2(sK2(X1,k5_partfun1(sK7,k1_tarski(sK8),X0)),sK7,k1_tarski(sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2(X1,k5_partfun1(sK7,k1_tarski(sK8),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12558,c_10122])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9253,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11397,plain,
    ( k5_partfun1(X0,X1,X2) = k1_tarski(X3)
    | sK2(X3,k5_partfun1(X0,X1,X2)) = X3
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2(X3,k5_partfun1(X0,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9272,c_9253])).

cnf(c_26,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9254,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12307,plain,
    ( k5_partfun1(X0,X1,X2) = k1_tarski(X3)
    | sK2(X3,k5_partfun1(X0,X1,X2)) = X3
    | v1_funct_2(sK2(X3,k5_partfun1(X0,X1,X2)),X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9272,c_9254])).

cnf(c_45024,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),X0) = k1_tarski(X1)
    | sK2(X1,k5_partfun1(sK7,k1_tarski(sK8),X0)) = X1
    | sK2(X1,k5_partfun1(sK7,k1_tarski(sK8),X0)) = sK10
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37769,c_11397,c_12307])).

cnf(c_45030,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = sK10
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9249,c_45024])).

cnf(c_45181,plain,
    ( ~ v1_funct_1(sK10)
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = sK10 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45030])).

cnf(c_45207,plain,
    ( sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = sK10
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45030,c_40])).

cnf(c_45208,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = sK10 ),
    inference(renaming,[status(thm)],[c_45207])).

cnf(c_45218,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_45208,c_9272])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_32,negated_conjecture,
    ( k1_tarski(sK10) != k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_118,plain,
    ( ~ r2_hidden(sK10,k1_tarski(sK10))
    | sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_121,plain,
    ( r2_hidden(sK10,k1_tarski(sK10)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8669,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_8680,plain,
    ( k1_tarski(sK10) = k1_tarski(sK10)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_8669])).

cnf(c_9636,plain,
    ( sP0(sK9,sK7,k1_tarski(sK8),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_8662,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_9574,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != X0
    | k1_tarski(sK10) != X0
    | k1_tarski(sK10) = k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_8662])).

cnf(c_9824,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != k1_tarski(sK10)
    | k1_tarski(sK10) = k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | k1_tarski(sK10) != k1_tarski(sK10) ),
    inference(instantiation,[status(thm)],[c_9574])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ sP1(X2,X1,X0)
    | k5_partfun1(X1,X2,X0) = X3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_420,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ v1_funct_1(X4)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | k5_partfun1(X1,X2,X0) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_421,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k5_partfun1(X1,X2,X0) = X3 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_9706,plain,
    ( ~ sP0(sK9,sK7,k1_tarski(sK8),X0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK9)
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_9968,plain,
    ( ~ sP0(sK9,sK7,k1_tarski(sK8),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK9)
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_9706])).

cnf(c_9246,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_15406,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9246,c_15393])).

cnf(c_15600,plain,
    ( v1_partfun1(sK10,sK7) != iProver_top
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15406,c_38])).

cnf(c_15601,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_15600])).

cnf(c_15602,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ v1_partfun1(sK10,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15601])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36873,plain,
    ( ~ r2_hidden(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != X0
    | k1_tarski(X0) = k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_36875,plain,
    ( ~ r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != sK10
    | k1_tarski(sK10) = k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_36873])).

cnf(c_8670,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_12671,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X2,X3),X3)
    | X3 != X1
    | sK2(X2,X3) != X0 ),
    inference(instantiation,[status(thm)],[c_8670])).

cnf(c_17283,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X2,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) != X1
    | sK2(X2,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_12671])).

cnf(c_39829,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | r2_hidden(sK2(X1,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | sK2(X1,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_17283])).

cnf(c_39831,plain,
    ( r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != sK10 ),
    inference(instantiation,[status(thm)],[c_39829])).

cnf(c_45031,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = X0
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9246,c_45024])).

cnf(c_45185,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(sK10)
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10
    | v1_funct_1(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_45031])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | sK5(X0,X1,X2,X4) = X4 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9260,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | sP0(X0,X1,X2,X4) != iProver_top
    | r2_hidden(X3,X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11353,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9244,c_9260])).

cnf(c_12503,plain,
    ( sK5(X0,X1,X2,sK2(X3,k5_partfun1(X1,X2,X0))) = sK2(X3,k5_partfun1(X1,X2,X0))
    | k5_partfun1(X1,X2,X0) = k1_tarski(X3)
    | sK2(X3,k5_partfun1(X1,X2,X0)) = X3
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9272,c_11353])).

cnf(c_31331,plain,
    ( sK5(sK10,sK7,k1_tarski(sK8),sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10))) = sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10))
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9249,c_12503])).

cnf(c_31722,plain,
    ( sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK5(sK10,sK7,k1_tarski(sK8),sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10))) = sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31331,c_40])).

cnf(c_31723,plain,
    ( sK5(sK10,sK7,k1_tarski(sK8),sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10))) = sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10))
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0 ),
    inference(renaming,[status(thm)],[c_31722])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | v1_partfun1(sK5(X0,X1,X2,X4),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9261,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | v1_partfun1(sK5(X0,X1,X2,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11351,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_partfun1(sK5(X3,X1,X2,X0),X1) = iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9244,c_9261])).

cnf(c_31731,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | r2_hidden(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)),k5_partfun1(sK7,k1_tarski(sK8),sK10)) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_partfun1(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)),sK7) = iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_31723,c_11351])).

cnf(c_9633,plain,
    ( sP0(sK10,sK7,k1_tarski(sK8),k5_partfun1(sK7,k1_tarski(sK8),sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK10) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_9634,plain,
    ( sP0(sK10,sK7,k1_tarski(sK8),k5_partfun1(sK7,k1_tarski(sK8),sK10)) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9633])).

cnf(c_9701,plain,
    ( ~ sP0(sK10,sK7,k1_tarski(sK8),X0)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK10)
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = X0 ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_10580,plain,
    ( ~ sP0(sK10,sK7,k1_tarski(sK8),k1_tarski(X0))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK10)
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_9701])).

cnf(c_10582,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sP0(sK10,sK7,k1_tarski(sK8),k1_tarski(X0)) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10580])).

cnf(c_16895,plain,
    ( r2_hidden(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)),k5_partfun1(sK7,k1_tarski(sK8),sK10))
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | k1_tarski(X0) = k5_partfun1(sK7,k1_tarski(sK8),sK10) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16900,plain,
    ( sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | k1_tarski(X0) = k5_partfun1(sK7,k1_tarski(sK8),sK10)
    | r2_hidden(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)),k5_partfun1(sK7,k1_tarski(sK8),sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16895])).

cnf(c_8672,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | sP0(X0,X1,X2,X4)
    | X4 != X3 ),
    theory(equality)).

cnf(c_9929,plain,
    ( ~ sP0(sK10,sK7,k1_tarski(sK8),X0)
    | sP0(sK10,sK7,k1_tarski(sK8),X1)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_8672])).

cnf(c_12446,plain,
    ( ~ sP0(sK10,sK7,k1_tarski(sK8),X0)
    | sP0(sK10,sK7,k1_tarski(sK8),k1_tarski(X1))
    | k1_tarski(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_9929])).

cnf(c_21712,plain,
    ( ~ sP0(sK10,sK7,k1_tarski(sK8),k5_partfun1(sK7,k1_tarski(sK8),sK10))
    | sP0(sK10,sK7,k1_tarski(sK8),k1_tarski(X0))
    | k1_tarski(X0) != k5_partfun1(sK7,k1_tarski(sK8),sK10) ),
    inference(instantiation,[status(thm)],[c_12446])).

cnf(c_21713,plain,
    ( k1_tarski(X0) != k5_partfun1(sK7,k1_tarski(sK8),sK10)
    | sP0(sK10,sK7,k1_tarski(sK8),k5_partfun1(sK7,k1_tarski(sK8),sK10)) != iProver_top
    | sP0(sK10,sK7,k1_tarski(sK8),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21712])).

cnf(c_34032,plain,
    ( v1_partfun1(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)),sK7) = iProver_top
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31731,c_40,c_42,c_9634,c_10582,c_16900,c_21713])).

cnf(c_34033,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | v1_partfun1(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_34032])).

cnf(c_45225,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | v1_partfun1(sK10,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_45208,c_34033])).

cnf(c_45302,plain,
    ( v1_partfun1(sK10,sK7)
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45225])).

cnf(c_46168,plain,
    ( sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0
    | k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45218,c_37,c_38,c_36,c_32,c_118,c_121,c_8680,c_9636,c_9824,c_9968,c_15602,c_36875,c_39831,c_45185,c_45302])).

cnf(c_46169,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) = X0 ),
    inference(renaming,[status(thm)],[c_46168])).

cnf(c_9273,plain,
    ( sK2(X0,X1) != X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_46173,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | r2_hidden(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)),k5_partfun1(sK7,k1_tarski(sK8),sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46169,c_9273])).

cnf(c_46201,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(X0)
    | r2_hidden(X0,k5_partfun1(sK7,k1_tarski(sK8),sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46169,c_46173])).

cnf(c_52069,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK10) = k1_tarski(sK10)
    | v1_partfun1(sK10,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_15459,c_46201])).

cnf(c_36874,plain,
    ( sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != X0
    | k1_tarski(X0) = k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | r2_hidden(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36873])).

cnf(c_36876,plain,
    ( sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != sK10
    | k1_tarski(sK10) = k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36874])).

cnf(c_39830,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != X1
    | r2_hidden(X1,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top
    | r2_hidden(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39829])).

cnf(c_39832,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != sK10
    | r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39830])).

cnf(c_52559,plain,
    ( v1_partfun1(sK10,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52069,c_37,c_38,c_36,c_32,c_118,c_121,c_8680,c_9636,c_9824,c_9968,c_15601,c_36876,c_39832,c_45185])).

cnf(c_52564,plain,
    ( v1_xboole_0(k1_tarski(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15173,c_52559])).

cnf(c_21,plain,
    ( m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9257,plain,
    ( m1_subset_1(sK6(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_28,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9252,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9871,plain,
    ( r2_hidden(sK6(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9257,c_9252])).

cnf(c_14798,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK6(k5_partfun1(X1,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9871,c_9255])).

cnf(c_23174,plain,
    ( sK6(k5_partfun1(sK7,k1_tarski(sK8),X0)) = sK10
    | v1_funct_2(sK6(k5_partfun1(sK7,k1_tarski(sK8),X0)),sK7,k1_tarski(sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6(k5_partfun1(sK7,k1_tarski(sK8),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14798,c_10122])).

cnf(c_14800,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6(k5_partfun1(X1,X2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9871,c_9253])).

cnf(c_14799,plain,
    ( v1_funct_2(sK6(k5_partfun1(X0,X1,X2)),X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(k5_partfun1(X0,X1,X2)) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9871,c_9254])).

cnf(c_25924,plain,
    ( sK6(k5_partfun1(sK7,k1_tarski(sK8),X0)) = sK10
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23174,c_14800,c_14799])).

cnf(c_25931,plain,
    ( sK6(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10
    | v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9246,c_25924])).

cnf(c_26149,plain,
    ( v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | sK6(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25931,c_38])).

cnf(c_26150,plain,
    ( sK6(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10
    | v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top ),
    inference(renaming,[status(thm)],[c_26149])).

cnf(c_31,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_9250,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26163,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = X0
    | sK6(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26150,c_9250])).

cnf(c_52572,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(sK8)
    | sK6(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10 ),
    inference(superposition,[status(thm)],[c_52564,c_26163])).

cnf(c_54436,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(sK8)
    | m1_subset_1(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_52572,c_9257])).

cnf(c_15174,plain,
    ( v1_partfun1(sK10,sK7)
    | v1_xboole_0(k1_tarski(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15173])).

cnf(c_10168,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ v1_xboole_0(k1_tarski(X0))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_31849,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ v1_xboole_0(k1_tarski(sK8))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(sK8) ),
    inference(instantiation,[status(thm)],[c_10168])).

cnf(c_54435,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(sK8)
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_52572,c_9871])).

cnf(c_54459,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | v1_xboole_0(k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_54435])).

cnf(c_54707,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54436,c_37,c_38,c_36,c_32,c_118,c_121,c_8680,c_9636,c_9824,c_9968,c_15174,c_15602,c_31849,c_36875,c_39831,c_45185,c_54459])).

cnf(c_54913,plain,
    ( r2_hidden(X0,k1_tarski(sK8)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_54707,c_9253])).

cnf(c_39,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9827,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != k1_tarski(X0)
    | k1_tarski(sK10) = k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | k1_tarski(sK10) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_9574])).

cnf(c_9828,plain,
    ( k1_tarski(sK10) = k1_tarski(X0)
    | sK10 != X0 ),
    inference(instantiation,[status(thm)],[c_8669])).

cnf(c_10177,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != X0
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X1)
    | k1_tarski(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_8662])).

cnf(c_11343,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != k1_tarski(X0)
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X1)
    | k1_tarski(X1) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_10177])).

cnf(c_53024,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) != k1_tarski(sK8)
    | k1_tarski(X0) != k1_tarski(sK8) ),
    inference(instantiation,[status(thm)],[c_11343])).

cnf(c_45184,plain,
    ( ~ v1_funct_1(sK9)
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = X0
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45031])).

cnf(c_45577,plain,
    ( sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = X0
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45031,c_37,c_45184])).

cnf(c_45578,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = X0
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10 ),
    inference(renaming,[status(thm)],[c_45577])).

cnf(c_45588,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = X0
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_45578,c_9272])).

cnf(c_45661,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45588])).

cnf(c_46327,plain,
    ( sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = X0
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45588,c_37,c_38,c_36,c_32,c_118,c_121,c_8680,c_9636,c_9824,c_9968,c_36876,c_39832,c_45185])).

cnf(c_46328,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = X0 ),
    inference(renaming,[status(thm)],[c_46327])).

cnf(c_46332,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | r2_hidden(sK2(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46328,c_9273])).

cnf(c_46355,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k1_tarski(X0)
    | r2_hidden(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46328,c_46332])).

cnf(c_54713,plain,
    ( k1_tarski(X0) = k1_tarski(sK8)
    | r2_hidden(X0,k1_tarski(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54707,c_46355])).

cnf(c_54911,plain,
    ( r2_hidden(X0,k1_tarski(sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_54707,c_9255])).

cnf(c_54912,plain,
    ( v1_funct_2(X0,sK7,k1_tarski(sK8)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK8)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_54707,c_9254])).

cnf(c_56003,plain,
    ( r2_hidden(X0,k1_tarski(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_54913,c_37,c_38,c_36,c_39,c_32,c_118,c_121,c_8680,c_9636,c_9824,c_9827,c_9828,c_9968,c_10122,c_15174,c_15602,c_31849,c_36875,c_39831,c_45185,c_53024,c_54459,c_54713,c_54911,c_54912])).

cnf(c_56011,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9271,c_56003])).


%------------------------------------------------------------------------------
