%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:34 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 351 expanded)
%              Number of leaves         :   42 ( 156 expanded)
%              Depth                    :   11
%              Number of atoms          :  625 (2061 expanded)
%              Number of equality atoms :   91 ( 280 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f927,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f156,f182,f192,f203,f216,f239,f251,f259,f262,f265,f356,f503,f582,f585,f588,f591,f594,f688,f926])).

fof(f926,plain,
    ( ~ spl13_10
    | ~ spl13_24 ),
    inference(avatar_contradiction_clause,[],[f915])).

fof(f915,plain,
    ( $false
    | ~ spl13_10
    | ~ spl13_24 ),
    inference(resolution,[],[f909,f97])).

fof(f97,plain,(
    ! [X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP0(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP0(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( sP0(X6,X4,X3,X2,X1,X0)
    <=> ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f909,plain,
    ( ! [X0] : ~ sP0(X0,sK9,sK8,sK7,sK6,sK5)
    | ~ spl13_10
    | ~ spl13_24 ),
    inference(resolution,[],[f386,f757])).

fof(f757,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_enumset1(sK5,sK6,sK7,sK8,sK9))
    | ~ spl13_10
    | ~ spl13_24 ),
    inference(resolution,[],[f180,f357])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_24 ),
    inference(resolution,[],[f355,f95])).

fof(f95,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK11(X0,X1),X0)
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( r1_tarski(sK11(X0,X1),X0)
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK11(X0,X1),X0)
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( r1_tarski(sK11(X0,X1),X0)
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_zfmisc_1(sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl13_24
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X1,k1_zfmisc_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f180,plain,
    ( r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK2)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl13_10
  <=> r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f386,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,k3_enumset1(X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(resolution,[],[f80,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] : sP1(X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP1(X0,X1,X2,X3,X4,X5) )
      & ( sP1(X0,X1,X2,X3,X4,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(definition_folding,[],[f22,f24,f23])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP1(X0,X1,X2,X3,X4,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5)
      | ~ sP0(X7,X4,X3,X2,X1,X0)
      | r2_hidden(X7,X5) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ( ( ~ sP0(sK12(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK12(X0,X1,X2,X3,X4,X5),X5) )
          & ( sP0(sK12(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | r2_hidden(sK12(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f46,f47])).

fof(f47,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X6,X5) )
          & ( sP0(X6,X4,X3,X2,X1,X0)
            | r2_hidden(X6,X5) ) )
     => ( ( ~ sP0(sK12(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK12(X0,X1,X2,X3,X4,X5),X5) )
        & ( sP0(sK12(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | r2_hidden(sK12(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ~ sP0(X6,X4,X3,X2,X1,X0) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f688,plain,(
    ~ spl13_37 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | ~ spl13_37 ),
    inference(trivial_inequality_removal,[],[f686])).

fof(f686,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl13_37 ),
    inference(superposition,[],[f60,f502])).

fof(f502,plain,
    ( k1_xboole_0 = sK2
    | ~ spl13_37 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl13_37
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_37])])).

fof(f60,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK9,sK2)
    & m1_subset_1(sK8,sK2)
    & m1_subset_1(sK7,sK2)
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,sK2)
    & m1_subset_1(sK4,sK2)
    & m1_subset_1(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f15,f32,f31,f30,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                                & k1_xboole_0 != X0
                                & m1_subset_1(X7,X0) )
                            & m1_subset_1(X6,X0) )
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(sK3,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2))
                              & k1_xboole_0 != sK2
                              & m1_subset_1(X7,sK2) )
                          & m1_subset_1(X6,sK2) )
                      & m1_subset_1(X5,sK2) )
                  & m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,sK2) )
          & m1_subset_1(X2,sK2) )
      & m1_subset_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ~ m1_subset_1(k5_enumset1(sK3,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2))
                            & k1_xboole_0 != sK2
                            & m1_subset_1(X7,sK2) )
                        & m1_subset_1(X6,sK2) )
                    & m1_subset_1(X5,sK2) )
                & m1_subset_1(X4,sK2) )
            & m1_subset_1(X3,sK2) )
        & m1_subset_1(X2,sK2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ~ m1_subset_1(k5_enumset1(sK3,sK4,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2))
                          & k1_xboole_0 != sK2
                          & m1_subset_1(X7,sK2) )
                      & m1_subset_1(X6,sK2) )
                  & m1_subset_1(X5,sK2) )
              & m1_subset_1(X4,sK2) )
          & m1_subset_1(X3,sK2) )
      & m1_subset_1(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ~ m1_subset_1(k5_enumset1(sK3,sK4,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2))
                        & k1_xboole_0 != sK2
                        & m1_subset_1(X7,sK2) )
                    & m1_subset_1(X6,sK2) )
                & m1_subset_1(X5,sK2) )
            & m1_subset_1(X4,sK2) )
        & m1_subset_1(X3,sK2) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,X4,X5,X6,X7),k1_zfmisc_1(sK2))
                      & k1_xboole_0 != sK2
                      & m1_subset_1(X7,sK2) )
                  & m1_subset_1(X6,sK2) )
              & m1_subset_1(X5,sK2) )
          & m1_subset_1(X4,sK2) )
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,X4,X5,X6,X7),k1_zfmisc_1(sK2))
                    & k1_xboole_0 != sK2
                    & m1_subset_1(X7,sK2) )
                & m1_subset_1(X6,sK2) )
            & m1_subset_1(X5,sK2) )
        & m1_subset_1(X4,sK2) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,X5,X6,X7),k1_zfmisc_1(sK2))
                  & k1_xboole_0 != sK2
                  & m1_subset_1(X7,sK2) )
              & m1_subset_1(X6,sK2) )
          & m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,X5,X6,X7),k1_zfmisc_1(sK2))
                & k1_xboole_0 != sK2
                & m1_subset_1(X7,sK2) )
            & m1_subset_1(X6,sK2) )
        & m1_subset_1(X5,sK2) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,X6,X7),k1_zfmisc_1(sK2))
              & k1_xboole_0 != sK2
              & m1_subset_1(X7,sK2) )
          & m1_subset_1(X6,sK2) )
      & m1_subset_1(sK7,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,X6,X7),k1_zfmisc_1(sK2))
            & k1_xboole_0 != sK2
            & m1_subset_1(X7,sK2) )
        & m1_subset_1(X6,sK2) )
   => ( ? [X7] :
          ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,X7),k1_zfmisc_1(sK2))
          & k1_xboole_0 != sK2
          & m1_subset_1(X7,sK2) )
      & m1_subset_1(sK8,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X7] :
        ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,X7),k1_zfmisc_1(sK2))
        & k1_xboole_0 != sK2
        & m1_subset_1(X7,sK2) )
   => ( ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK9,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ! [X7] :
                                ( m1_subset_1(X7,X0)
                               => ( k1_xboole_0 != X0
                                 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ( k1_xboole_0 != X0
                               => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_subset_1)).

fof(f594,plain,(
    spl13_36 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | spl13_36 ),
    inference(resolution,[],[f498,f59])).

fof(f59,plain,(
    m1_subset_1(sK9,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f498,plain,
    ( ~ m1_subset_1(sK9,sK2)
    | spl13_36 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl13_36
  <=> m1_subset_1(sK9,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f591,plain,(
    spl13_35 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | spl13_35 ),
    inference(resolution,[],[f494,f58])).

fof(f58,plain,(
    m1_subset_1(sK8,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f494,plain,
    ( ~ m1_subset_1(sK8,sK2)
    | spl13_35 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl13_35
  <=> m1_subset_1(sK8,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f588,plain,(
    spl13_34 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | spl13_34 ),
    inference(resolution,[],[f490,f57])).

fof(f57,plain,(
    m1_subset_1(sK7,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f490,plain,
    ( ~ m1_subset_1(sK7,sK2)
    | spl13_34 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl13_34
  <=> m1_subset_1(sK7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f585,plain,(
    spl13_33 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | spl13_33 ),
    inference(resolution,[],[f486,f56])).

fof(f56,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f486,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | spl13_33 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl13_33
  <=> m1_subset_1(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f582,plain,(
    spl13_32 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | spl13_32 ),
    inference(resolution,[],[f482,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f482,plain,
    ( ~ m1_subset_1(sK5,sK2)
    | spl13_32 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl13_32
  <=> m1_subset_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f503,plain,
    ( ~ spl13_32
    | ~ spl13_33
    | ~ spl13_34
    | ~ spl13_35
    | ~ spl13_36
    | spl13_37
    | spl13_12 ),
    inference(avatar_split_clause,[],[f475,f200,f500,f496,f492,f488,f484,f480])).

fof(f200,plain,
    ( spl13_12
  <=> m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f475,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK9,sK2)
    | ~ m1_subset_1(sK8,sK2)
    | ~ m1_subset_1(sK7,sK2)
    | ~ m1_subset_1(sK6,sK2)
    | ~ m1_subset_1(sK5,sK2)
    | spl13_12 ),
    inference(resolution,[],[f69,f202])).

fof(f202,plain,
    ( ~ m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))
    | spl13_12 ),
    inference(avatar_component_clause,[],[f200])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      | k1_xboole_0 = X0
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      | k1_xboole_0 = X0
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ( k1_xboole_0 != X0
                       => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_subset_1)).

fof(f356,plain,
    ( spl13_1
    | spl13_24
    | ~ spl13_17 ),
    inference(avatar_split_clause,[],[f351,f244,f354,f105])).

fof(f105,plain,
    ( spl13_1
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f244,plain,
    ( spl13_17
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X1,k1_zfmisc_1(sK2))
        | v1_xboole_0(k1_zfmisc_1(sK2)) )
    | ~ spl13_17 ),
    inference(resolution,[],[f296,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f296,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_17 ),
    inference(resolution,[],[f289,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f289,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl13_17 ),
    inference(resolution,[],[f246,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK10(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f246,plain,
    ( v1_xboole_0(sK2)
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f244])).

fof(f265,plain,(
    spl13_19 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl13_19 ),
    inference(resolution,[],[f258,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f258,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | spl13_19 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl13_19
  <=> m1_subset_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f262,plain,(
    spl13_18 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl13_18 ),
    inference(resolution,[],[f250,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f250,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl13_18 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl13_18
  <=> m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f259,plain,
    ( spl13_17
    | ~ spl13_19
    | spl13_16 ),
    inference(avatar_split_clause,[],[f254,f236,f256,f244])).

fof(f236,plain,
    ( spl13_16
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f254,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | v1_xboole_0(sK2)
    | spl13_16 ),
    inference(resolution,[],[f238,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f238,plain,
    ( ~ r2_hidden(sK4,sK2)
    | spl13_16 ),
    inference(avatar_component_clause,[],[f236])).

fof(f251,plain,
    ( spl13_17
    | ~ spl13_18
    | spl13_15 ),
    inference(avatar_split_clause,[],[f242,f232,f248,f244])).

fof(f232,plain,
    ( spl13_15
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f242,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | spl13_15 ),
    inference(resolution,[],[f234,f65])).

fof(f234,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl13_15 ),
    inference(avatar_component_clause,[],[f232])).

fof(f239,plain,
    ( ~ spl13_15
    | ~ spl13_16
    | spl13_14 ),
    inference(avatar_split_clause,[],[f228,f213,f236,f232])).

fof(f213,plain,
    ( spl13_14
  <=> r2_hidden(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f228,plain,
    ( ~ r2_hidden(sK4,sK2)
    | ~ r2_hidden(sK3,sK2)
    | spl13_14 ),
    inference(resolution,[],[f223,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f223,plain,
    ( ~ r1_tarski(k2_tarski(sK3,sK4),sK2)
    | spl13_14 ),
    inference(resolution,[],[f215,f95])).

fof(f215,plain,
    ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2))
    | spl13_14 ),
    inference(avatar_component_clause,[],[f213])).

fof(f216,plain,
    ( spl13_1
    | ~ spl13_14
    | spl13_11 ),
    inference(avatar_split_clause,[],[f193,f189,f213,f105])).

fof(f189,plain,
    ( spl13_11
  <=> m1_subset_1(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f193,plain,
    ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | spl13_11 ),
    inference(resolution,[],[f191,f66])).

fof(f191,plain,
    ( ~ m1_subset_1(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2))
    | spl13_11 ),
    inference(avatar_component_clause,[],[f189])).

fof(f203,plain,
    ( spl13_1
    | ~ spl13_12
    | spl13_10 ),
    inference(avatar_split_clause,[],[f198,f179,f200,f105])).

fof(f198,plain,
    ( ~ m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | spl13_10 ),
    inference(resolution,[],[f194,f65])).

fof(f194,plain,
    ( ~ r2_hidden(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))
    | spl13_10 ),
    inference(resolution,[],[f181,f96])).

fof(f96,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f181,plain,
    ( ~ r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK2)
    | spl13_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f192,plain,
    ( spl13_1
    | ~ spl13_11
    | spl13_9 ),
    inference(avatar_split_clause,[],[f187,f175,f189,f105])).

fof(f175,plain,
    ( spl13_9
  <=> r1_tarski(k2_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f187,plain,
    ( ~ m1_subset_1(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | spl13_9 ),
    inference(resolution,[],[f183,f65])).

fof(f183,plain,
    ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2))
    | spl13_9 ),
    inference(resolution,[],[f177,f96])).

fof(f177,plain,
    ( ~ r1_tarski(k2_tarski(sK3,sK4),sK2)
    | spl13_9 ),
    inference(avatar_component_clause,[],[f175])).

fof(f182,plain,
    ( ~ spl13_9
    | ~ spl13_10
    | spl13_2 ),
    inference(avatar_split_clause,[],[f173,f109,f179,f175])).

fof(f109,plain,
    ( spl13_2
  <=> r2_hidden(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f173,plain,
    ( ~ r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK2)
    | ~ r1_tarski(k2_tarski(sK3,sK4),sK2)
    | spl13_2 ),
    inference(resolution,[],[f75,f113])).

fof(f113,plain,
    ( ~ r1_tarski(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),sK2)
    | spl13_2 ),
    inference(resolution,[],[f111,f95])).

fof(f111,plain,
    ( ~ r2_hidden(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f156,plain,(
    ~ spl13_1 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl13_1 ),
    inference(resolution,[],[f107,f62])).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f107,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f103,f109,f105])).

fof(f103,plain,
    ( ~ r2_hidden(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f66,f93])).

fof(f93,plain,(
    ~ m1_subset_1(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2)) ),
    inference(definition_unfolding,[],[f61,f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(f61,plain,(
    ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (29622)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (29630)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (29643)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (29635)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (29624)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.52  % (29639)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.20/0.52  % (29627)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.53  % (29620)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (29621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (29626)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.54  % (29621)Refutation not found, incomplete strategy% (29621)------------------------------
% 1.32/0.54  % (29621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (29621)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (29621)Memory used [KB]: 10746
% 1.32/0.54  % (29621)Time elapsed: 0.124 s
% 1.32/0.54  % (29621)------------------------------
% 1.32/0.54  % (29621)------------------------------
% 1.32/0.54  % (29619)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.54  % (29642)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.54  % (29625)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (29646)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.54  % (29637)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.54  % (29647)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.55  % (29641)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.55  % (29645)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.55  % (29649)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.55  % (29638)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.55  % (29640)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.55  % (29633)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.32/0.55  % (29629)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.56  % (29634)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.56  % (29631)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.56  % (29648)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.56  % (29632)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.56  % (29628)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.56  % (29642)Refutation not found, incomplete strategy% (29642)------------------------------
% 1.32/0.56  % (29642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (29642)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (29642)Memory used [KB]: 10874
% 1.32/0.56  % (29642)Time elapsed: 0.149 s
% 1.32/0.56  % (29642)------------------------------
% 1.32/0.56  % (29642)------------------------------
% 1.32/0.56  % (29628)Refutation not found, incomplete strategy% (29628)------------------------------
% 1.32/0.56  % (29628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (29628)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (29628)Memory used [KB]: 10746
% 1.32/0.56  % (29628)Time elapsed: 0.147 s
% 1.32/0.56  % (29628)------------------------------
% 1.32/0.56  % (29628)------------------------------
% 1.32/0.57  % (29644)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.57  % (29636)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.61  % (29632)Refutation found. Thanks to Tanya!
% 1.32/0.61  % SZS status Theorem for theBenchmark
% 1.32/0.61  % SZS output start Proof for theBenchmark
% 1.32/0.61  fof(f927,plain,(
% 1.32/0.61    $false),
% 1.32/0.61    inference(avatar_sat_refutation,[],[f112,f156,f182,f192,f203,f216,f239,f251,f259,f262,f265,f356,f503,f582,f585,f588,f591,f594,f688,f926])).
% 1.32/0.61  fof(f926,plain,(
% 1.32/0.61    ~spl13_10 | ~spl13_24),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f915])).
% 1.32/0.61  fof(f915,plain,(
% 1.32/0.61    $false | (~spl13_10 | ~spl13_24)),
% 1.32/0.61    inference(resolution,[],[f909,f97])).
% 1.32/0.61  fof(f97,plain,(
% 1.32/0.61    ( ! [X4,X2,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5)) )),
% 1.32/0.61    inference(equality_resolution,[],[f88])).
% 1.32/0.61  fof(f88,plain,(
% 1.32/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5) | X0 != X1) )),
% 1.32/0.61    inference(cnf_transformation,[],[f51])).
% 1.32/0.61  fof(f51,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 1.32/0.61    inference(rectify,[],[f50])).
% 1.32/0.61  fof(f50,plain,(
% 1.32/0.61    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 1.32/0.61    inference(flattening,[],[f49])).
% 1.32/0.61  fof(f49,plain,(
% 1.32/0.61    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 1.32/0.61    inference(nnf_transformation,[],[f23])).
% 1.32/0.61  fof(f23,plain,(
% 1.32/0.61    ! [X6,X4,X3,X2,X1,X0] : (sP0(X6,X4,X3,X2,X1,X0) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6))),
% 1.32/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.32/0.61  fof(f909,plain,(
% 1.32/0.61    ( ! [X0] : (~sP0(X0,sK9,sK8,sK7,sK6,sK5)) ) | (~spl13_10 | ~spl13_24)),
% 1.32/0.61    inference(resolution,[],[f386,f757])).
% 1.32/0.61  fof(f757,plain,(
% 1.32/0.61    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK5,sK6,sK7,sK8,sK9))) ) | (~spl13_10 | ~spl13_24)),
% 1.32/0.61    inference(resolution,[],[f180,f357])).
% 1.32/0.61  fof(f357,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~r1_tarski(X1,sK2) | ~r2_hidden(X0,X1)) ) | ~spl13_24),
% 1.32/0.61    inference(resolution,[],[f355,f95])).
% 1.32/0.61  fof(f95,plain,(
% 1.32/0.61    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.32/0.61    inference(equality_resolution,[],[f72])).
% 1.32/0.61  fof(f72,plain,(
% 1.32/0.61    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.32/0.61    inference(cnf_transformation,[],[f42])).
% 1.32/0.61  fof(f42,plain,(
% 1.32/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f40,f41])).
% 1.32/0.61  fof(f41,plain,(
% 1.32/0.61    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1))))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f40,plain,(
% 1.32/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.61    inference(rectify,[],[f39])).
% 1.32/0.61  fof(f39,plain,(
% 1.32/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.61    inference(nnf_transformation,[],[f5])).
% 1.32/0.61  fof(f5,axiom,(
% 1.32/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.32/0.61  fof(f355,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(sK2)) | ~r2_hidden(X0,X1)) ) | ~spl13_24),
% 1.32/0.61    inference(avatar_component_clause,[],[f354])).
% 1.32/0.61  fof(f354,plain,(
% 1.32/0.61    spl13_24 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,k1_zfmisc_1(sK2)))),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).
% 1.32/0.61  fof(f180,plain,(
% 1.32/0.61    r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK2) | ~spl13_10),
% 1.32/0.61    inference(avatar_component_clause,[],[f179])).
% 1.32/0.61  fof(f179,plain,(
% 1.32/0.61    spl13_10 <=> r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 1.32/0.61  fof(f386,plain,(
% 1.32/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X0,k3_enumset1(X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.61    inference(resolution,[],[f80,f102])).
% 1.32/0.61  fof(f102,plain,(
% 1.32/0.61    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.32/0.61    inference(equality_resolution,[],[f89])).
% 1.32/0.61  fof(f89,plain,(
% 1.32/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.32/0.61    inference(cnf_transformation,[],[f52])).
% 1.32/0.61  fof(f52,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP1(X0,X1,X2,X3,X4,X5)) & (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.32/0.61    inference(nnf_transformation,[],[f25])).
% 1.32/0.61  fof(f25,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP1(X0,X1,X2,X3,X4,X5))),
% 1.32/0.61    inference(definition_folding,[],[f22,f24,f23])).
% 1.32/0.61  fof(f24,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : (sP1(X0,X1,X2,X3,X4,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> sP0(X6,X4,X3,X2,X1,X0)))),
% 1.32/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.32/0.61  fof(f22,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.32/0.61    inference(ennf_transformation,[],[f8])).
% 1.32/0.61  fof(f8,axiom,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 1.32/0.61  fof(f80,plain,(
% 1.32/0.61    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5) | ~sP0(X7,X4,X3,X2,X1,X0) | r2_hidden(X7,X5)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f48])).
% 1.32/0.61  fof(f48,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ((~sP0(sK12(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK12(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK12(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK12(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.32/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f46,f47])).
% 1.32/0.61  fof(f47,plain,(
% 1.32/0.61    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5))) => ((~sP0(sK12(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK12(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK12(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK12(X0,X1,X2,X3,X4,X5),X5))))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f46,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.32/0.61    inference(rectify,[],[f45])).
% 1.32/0.61  fof(f45,plain,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | ~sP0(X6,X4,X3,X2,X1,X0)) & (sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.32/0.61    inference(nnf_transformation,[],[f24])).
% 1.32/0.61  fof(f688,plain,(
% 1.32/0.61    ~spl13_37),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f687])).
% 1.32/0.61  fof(f687,plain,(
% 1.32/0.61    $false | ~spl13_37),
% 1.32/0.61    inference(trivial_inequality_removal,[],[f686])).
% 1.32/0.61  fof(f686,plain,(
% 1.32/0.61    k1_xboole_0 != k1_xboole_0 | ~spl13_37),
% 1.32/0.61    inference(superposition,[],[f60,f502])).
% 1.32/0.61  fof(f502,plain,(
% 1.32/0.61    k1_xboole_0 = sK2 | ~spl13_37),
% 1.32/0.61    inference(avatar_component_clause,[],[f500])).
% 1.32/0.61  fof(f500,plain,(
% 1.32/0.61    spl13_37 <=> k1_xboole_0 = sK2),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_37])])).
% 1.32/0.61  fof(f60,plain,(
% 1.32/0.61    k1_xboole_0 != sK2),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  fof(f33,plain,(
% 1.32/0.61    ((((((~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK9,sK2)) & m1_subset_1(sK8,sK2)) & m1_subset_1(sK7,sK2)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,sK2)) & m1_subset_1(sK4,sK2)) & m1_subset_1(sK3,sK2)),
% 1.32/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f15,f32,f31,f30,f29,f28,f27,f26])).
% 1.32/0.61  fof(f26,plain,(
% 1.32/0.61    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(X2,sK2)) & m1_subset_1(sK3,sK2))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f27,plain,(
% 1.32/0.61    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(X2,sK2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(sK4,sK2))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f28,plain,(
% 1.32/0.61    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(sK5,sK2))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f29,plain,(
% 1.32/0.61    ? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) => (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(sK6,sK2))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f30,plain,(
% 1.32/0.61    ? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) => (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(sK7,sK2))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f31,plain,(
% 1.32/0.61    ? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) => (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(sK8,sK2))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f32,plain,(
% 1.32/0.61    ? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) => (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK9,sK2))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f15,plain,(
% 1.32/0.61    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.32/0.61    inference(flattening,[],[f14])).
% 1.32/0.61  fof(f14,plain,(
% 1.32/0.61    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.32/0.61    inference(ennf_transformation,[],[f13])).
% 1.32/0.61  fof(f13,negated_conjecture,(
% 1.32/0.61    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => (k1_xboole_0 != X0 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))))))))))),
% 1.32/0.61    inference(negated_conjecture,[],[f12])).
% 1.32/0.61  fof(f12,conjecture,(
% 1.32/0.61    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => (k1_xboole_0 != X0 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))))))))))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_subset_1)).
% 1.32/0.61  fof(f594,plain,(
% 1.32/0.61    spl13_36),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f592])).
% 1.32/0.61  fof(f592,plain,(
% 1.32/0.61    $false | spl13_36),
% 1.32/0.61    inference(resolution,[],[f498,f59])).
% 1.32/0.61  fof(f59,plain,(
% 1.32/0.61    m1_subset_1(sK9,sK2)),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  fof(f498,plain,(
% 1.32/0.61    ~m1_subset_1(sK9,sK2) | spl13_36),
% 1.32/0.61    inference(avatar_component_clause,[],[f496])).
% 1.32/0.61  fof(f496,plain,(
% 1.32/0.61    spl13_36 <=> m1_subset_1(sK9,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).
% 1.32/0.61  fof(f591,plain,(
% 1.32/0.61    spl13_35),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f589])).
% 1.32/0.61  fof(f589,plain,(
% 1.32/0.61    $false | spl13_35),
% 1.32/0.61    inference(resolution,[],[f494,f58])).
% 1.32/0.61  fof(f58,plain,(
% 1.32/0.61    m1_subset_1(sK8,sK2)),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  fof(f494,plain,(
% 1.32/0.61    ~m1_subset_1(sK8,sK2) | spl13_35),
% 1.32/0.61    inference(avatar_component_clause,[],[f492])).
% 1.32/0.61  fof(f492,plain,(
% 1.32/0.61    spl13_35 <=> m1_subset_1(sK8,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).
% 1.32/0.61  fof(f588,plain,(
% 1.32/0.61    spl13_34),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f586])).
% 1.32/0.61  fof(f586,plain,(
% 1.32/0.61    $false | spl13_34),
% 1.32/0.61    inference(resolution,[],[f490,f57])).
% 1.32/0.61  fof(f57,plain,(
% 1.32/0.61    m1_subset_1(sK7,sK2)),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  fof(f490,plain,(
% 1.32/0.61    ~m1_subset_1(sK7,sK2) | spl13_34),
% 1.32/0.61    inference(avatar_component_clause,[],[f488])).
% 1.32/0.61  fof(f488,plain,(
% 1.32/0.61    spl13_34 <=> m1_subset_1(sK7,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).
% 1.32/0.61  fof(f585,plain,(
% 1.32/0.61    spl13_33),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f583])).
% 1.32/0.61  fof(f583,plain,(
% 1.32/0.61    $false | spl13_33),
% 1.32/0.61    inference(resolution,[],[f486,f56])).
% 1.32/0.61  fof(f56,plain,(
% 1.32/0.61    m1_subset_1(sK6,sK2)),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  fof(f486,plain,(
% 1.32/0.61    ~m1_subset_1(sK6,sK2) | spl13_33),
% 1.32/0.61    inference(avatar_component_clause,[],[f484])).
% 1.32/0.61  fof(f484,plain,(
% 1.32/0.61    spl13_33 <=> m1_subset_1(sK6,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).
% 1.32/0.61  fof(f582,plain,(
% 1.32/0.61    spl13_32),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f580])).
% 1.32/0.61  fof(f580,plain,(
% 1.32/0.61    $false | spl13_32),
% 1.32/0.61    inference(resolution,[],[f482,f55])).
% 1.32/0.61  fof(f55,plain,(
% 1.32/0.61    m1_subset_1(sK5,sK2)),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  fof(f482,plain,(
% 1.32/0.61    ~m1_subset_1(sK5,sK2) | spl13_32),
% 1.32/0.61    inference(avatar_component_clause,[],[f480])).
% 1.32/0.61  fof(f480,plain,(
% 1.32/0.61    spl13_32 <=> m1_subset_1(sK5,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).
% 1.32/0.61  fof(f503,plain,(
% 1.32/0.61    ~spl13_32 | ~spl13_33 | ~spl13_34 | ~spl13_35 | ~spl13_36 | spl13_37 | spl13_12),
% 1.32/0.61    inference(avatar_split_clause,[],[f475,f200,f500,f496,f492,f488,f484,f480])).
% 1.32/0.61  fof(f200,plain,(
% 1.32/0.61    spl13_12 <=> m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 1.32/0.61  fof(f475,plain,(
% 1.32/0.61    k1_xboole_0 = sK2 | ~m1_subset_1(sK9,sK2) | ~m1_subset_1(sK8,sK2) | ~m1_subset_1(sK7,sK2) | ~m1_subset_1(sK6,sK2) | ~m1_subset_1(sK5,sK2) | spl13_12),
% 1.32/0.61    inference(resolution,[],[f69,f202])).
% 1.32/0.61  fof(f202,plain,(
% 1.32/0.61    ~m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) | spl13_12),
% 1.32/0.61    inference(avatar_component_clause,[],[f200])).
% 1.32/0.61  fof(f69,plain,(
% 1.32/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f18])).
% 1.32/0.61  fof(f18,plain,(
% 1.32/0.61    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.32/0.61    inference(flattening,[],[f17])).
% 1.32/0.61  fof(f17,plain,(
% 1.32/0.61    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.32/0.61    inference(ennf_transformation,[],[f11])).
% 1.32/0.61  fof(f11,axiom,(
% 1.32/0.61    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => (k1_xboole_0 != X0 => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))))))))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_subset_1)).
% 1.32/0.61  fof(f356,plain,(
% 1.32/0.61    spl13_1 | spl13_24 | ~spl13_17),
% 1.32/0.61    inference(avatar_split_clause,[],[f351,f244,f354,f105])).
% 1.32/0.61  fof(f105,plain,(
% 1.32/0.61    spl13_1 <=> v1_xboole_0(k1_zfmisc_1(sK2))),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.32/0.61  fof(f244,plain,(
% 1.32/0.61    spl13_17 <=> v1_xboole_0(sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 1.32/0.61  fof(f351,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2))) ) | ~spl13_17),
% 1.32/0.61    inference(resolution,[],[f296,f66])).
% 1.32/0.61  fof(f66,plain,(
% 1.32/0.61    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f38])).
% 1.32/0.61  fof(f38,plain,(
% 1.32/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.32/0.61    inference(nnf_transformation,[],[f16])).
% 1.32/0.61  fof(f16,plain,(
% 1.32/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.32/0.61    inference(ennf_transformation,[],[f7])).
% 1.32/0.61  fof(f7,axiom,(
% 1.32/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.32/0.61  fof(f296,plain,(
% 1.32/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK2)) | ~r2_hidden(X0,X1)) ) | ~spl13_17),
% 1.32/0.61    inference(resolution,[],[f289,f70])).
% 1.32/0.61  fof(f70,plain,(
% 1.32/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f19])).
% 1.32/0.61  fof(f19,plain,(
% 1.32/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.61    inference(ennf_transformation,[],[f10])).
% 1.32/0.61  fof(f10,axiom,(
% 1.32/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.32/0.61  fof(f289,plain,(
% 1.32/0.61    ( ! [X2] : (~r2_hidden(X2,sK2)) ) | ~spl13_17),
% 1.32/0.61    inference(resolution,[],[f246,f63])).
% 1.32/0.61  fof(f63,plain,(
% 1.32/0.61    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f37])).
% 1.32/0.61  fof(f37,plain,(
% 1.32/0.61    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK10(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f35,f36])).
% 1.32/0.61  fof(f36,plain,(
% 1.32/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK10(X0),X0))),
% 1.32/0.61    introduced(choice_axiom,[])).
% 1.32/0.61  fof(f35,plain,(
% 1.32/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.61    inference(rectify,[],[f34])).
% 1.32/0.61  fof(f34,plain,(
% 1.32/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.61    inference(nnf_transformation,[],[f1])).
% 1.32/0.61  fof(f1,axiom,(
% 1.32/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.32/0.61  fof(f246,plain,(
% 1.32/0.61    v1_xboole_0(sK2) | ~spl13_17),
% 1.32/0.61    inference(avatar_component_clause,[],[f244])).
% 1.32/0.61  fof(f265,plain,(
% 1.32/0.61    spl13_19),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f263])).
% 1.32/0.61  fof(f263,plain,(
% 1.32/0.61    $false | spl13_19),
% 1.32/0.61    inference(resolution,[],[f258,f54])).
% 1.32/0.61  fof(f54,plain,(
% 1.32/0.61    m1_subset_1(sK4,sK2)),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  fof(f258,plain,(
% 1.32/0.61    ~m1_subset_1(sK4,sK2) | spl13_19),
% 1.32/0.61    inference(avatar_component_clause,[],[f256])).
% 1.32/0.61  fof(f256,plain,(
% 1.32/0.61    spl13_19 <=> m1_subset_1(sK4,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 1.32/0.61  fof(f262,plain,(
% 1.32/0.61    spl13_18),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f260])).
% 1.32/0.61  fof(f260,plain,(
% 1.32/0.61    $false | spl13_18),
% 1.32/0.61    inference(resolution,[],[f250,f53])).
% 1.32/0.61  fof(f53,plain,(
% 1.32/0.61    m1_subset_1(sK3,sK2)),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  fof(f250,plain,(
% 1.32/0.61    ~m1_subset_1(sK3,sK2) | spl13_18),
% 1.32/0.61    inference(avatar_component_clause,[],[f248])).
% 1.32/0.61  fof(f248,plain,(
% 1.32/0.61    spl13_18 <=> m1_subset_1(sK3,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 1.32/0.61  fof(f259,plain,(
% 1.32/0.61    spl13_17 | ~spl13_19 | spl13_16),
% 1.32/0.61    inference(avatar_split_clause,[],[f254,f236,f256,f244])).
% 1.32/0.61  fof(f236,plain,(
% 1.32/0.61    spl13_16 <=> r2_hidden(sK4,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).
% 1.32/0.61  fof(f254,plain,(
% 1.32/0.61    ~m1_subset_1(sK4,sK2) | v1_xboole_0(sK2) | spl13_16),
% 1.32/0.61    inference(resolution,[],[f238,f65])).
% 1.32/0.61  fof(f65,plain,(
% 1.32/0.61    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f38])).
% 1.32/0.61  fof(f238,plain,(
% 1.32/0.61    ~r2_hidden(sK4,sK2) | spl13_16),
% 1.32/0.61    inference(avatar_component_clause,[],[f236])).
% 1.32/0.61  fof(f251,plain,(
% 1.32/0.61    spl13_17 | ~spl13_18 | spl13_15),
% 1.32/0.61    inference(avatar_split_clause,[],[f242,f232,f248,f244])).
% 1.32/0.61  fof(f232,plain,(
% 1.32/0.61    spl13_15 <=> r2_hidden(sK3,sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 1.32/0.61  fof(f242,plain,(
% 1.32/0.61    ~m1_subset_1(sK3,sK2) | v1_xboole_0(sK2) | spl13_15),
% 1.32/0.61    inference(resolution,[],[f234,f65])).
% 1.32/0.61  fof(f234,plain,(
% 1.32/0.61    ~r2_hidden(sK3,sK2) | spl13_15),
% 1.32/0.61    inference(avatar_component_clause,[],[f232])).
% 1.32/0.61  fof(f239,plain,(
% 1.32/0.61    ~spl13_15 | ~spl13_16 | spl13_14),
% 1.32/0.61    inference(avatar_split_clause,[],[f228,f213,f236,f232])).
% 1.32/0.61  fof(f213,plain,(
% 1.32/0.61    spl13_14 <=> r2_hidden(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2))),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 1.32/0.61  fof(f228,plain,(
% 1.32/0.61    ~r2_hidden(sK4,sK2) | ~r2_hidden(sK3,sK2) | spl13_14),
% 1.32/0.61    inference(resolution,[],[f223,f78])).
% 1.32/0.61  fof(f78,plain,(
% 1.32/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f44])).
% 1.32/0.61  fof(f44,plain,(
% 1.32/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.32/0.61    inference(flattening,[],[f43])).
% 1.32/0.61  fof(f43,plain,(
% 1.32/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.32/0.61    inference(nnf_transformation,[],[f6])).
% 1.32/0.61  fof(f6,axiom,(
% 1.32/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.32/0.61  fof(f223,plain,(
% 1.32/0.61    ~r1_tarski(k2_tarski(sK3,sK4),sK2) | spl13_14),
% 1.32/0.61    inference(resolution,[],[f215,f95])).
% 1.32/0.61  fof(f215,plain,(
% 1.32/0.61    ~r2_hidden(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2)) | spl13_14),
% 1.32/0.61    inference(avatar_component_clause,[],[f213])).
% 1.32/0.61  fof(f216,plain,(
% 1.32/0.61    spl13_1 | ~spl13_14 | spl13_11),
% 1.32/0.61    inference(avatar_split_clause,[],[f193,f189,f213,f105])).
% 1.32/0.61  fof(f189,plain,(
% 1.32/0.61    spl13_11 <=> m1_subset_1(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2))),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).
% 1.32/0.61  fof(f193,plain,(
% 1.32/0.61    ~r2_hidden(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2)) | spl13_11),
% 1.32/0.61    inference(resolution,[],[f191,f66])).
% 1.32/0.61  fof(f191,plain,(
% 1.32/0.61    ~m1_subset_1(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2)) | spl13_11),
% 1.32/0.61    inference(avatar_component_clause,[],[f189])).
% 1.32/0.61  fof(f203,plain,(
% 1.32/0.61    spl13_1 | ~spl13_12 | spl13_10),
% 1.32/0.61    inference(avatar_split_clause,[],[f198,f179,f200,f105])).
% 1.32/0.61  fof(f198,plain,(
% 1.32/0.61    ~m1_subset_1(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2)) | spl13_10),
% 1.32/0.61    inference(resolution,[],[f194,f65])).
% 1.32/0.61  fof(f194,plain,(
% 1.32/0.61    ~r2_hidden(k3_enumset1(sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) | spl13_10),
% 1.32/0.61    inference(resolution,[],[f181,f96])).
% 1.32/0.61  fof(f96,plain,(
% 1.32/0.61    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.32/0.61    inference(equality_resolution,[],[f71])).
% 1.32/0.61  fof(f71,plain,(
% 1.32/0.61    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.32/0.61    inference(cnf_transformation,[],[f42])).
% 1.32/0.61  fof(f181,plain,(
% 1.32/0.61    ~r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK2) | spl13_10),
% 1.32/0.61    inference(avatar_component_clause,[],[f179])).
% 1.32/0.61  fof(f192,plain,(
% 1.32/0.61    spl13_1 | ~spl13_11 | spl13_9),
% 1.32/0.61    inference(avatar_split_clause,[],[f187,f175,f189,f105])).
% 1.32/0.61  fof(f175,plain,(
% 1.32/0.61    spl13_9 <=> r1_tarski(k2_tarski(sK3,sK4),sK2)),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 1.32/0.61  fof(f187,plain,(
% 1.32/0.61    ~m1_subset_1(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2)) | spl13_9),
% 1.32/0.61    inference(resolution,[],[f183,f65])).
% 1.32/0.61  fof(f183,plain,(
% 1.32/0.61    ~r2_hidden(k2_tarski(sK3,sK4),k1_zfmisc_1(sK2)) | spl13_9),
% 1.32/0.61    inference(resolution,[],[f177,f96])).
% 1.32/0.61  fof(f177,plain,(
% 1.32/0.61    ~r1_tarski(k2_tarski(sK3,sK4),sK2) | spl13_9),
% 1.32/0.61    inference(avatar_component_clause,[],[f175])).
% 1.32/0.61  fof(f182,plain,(
% 1.32/0.61    ~spl13_9 | ~spl13_10 | spl13_2),
% 1.32/0.61    inference(avatar_split_clause,[],[f173,f109,f179,f175])).
% 1.32/0.61  fof(f109,plain,(
% 1.32/0.61    spl13_2 <=> r2_hidden(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2))),
% 1.32/0.61    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.32/0.61  fof(f173,plain,(
% 1.32/0.61    ~r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK2) | ~r1_tarski(k2_tarski(sK3,sK4),sK2) | spl13_2),
% 1.32/0.61    inference(resolution,[],[f75,f113])).
% 1.32/0.61  fof(f113,plain,(
% 1.32/0.61    ~r1_tarski(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),sK2) | spl13_2),
% 1.32/0.61    inference(resolution,[],[f111,f95])).
% 1.32/0.61  fof(f111,plain,(
% 1.32/0.61    ~r2_hidden(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2)) | spl13_2),
% 1.32/0.61    inference(avatar_component_clause,[],[f109])).
% 1.32/0.61  fof(f75,plain,(
% 1.32/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.32/0.61    inference(cnf_transformation,[],[f21])).
% 1.32/0.61  fof(f21,plain,(
% 1.32/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.32/0.61    inference(flattening,[],[f20])).
% 1.32/0.61  fof(f20,plain,(
% 1.32/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.32/0.61    inference(ennf_transformation,[],[f2])).
% 1.32/0.61  fof(f2,axiom,(
% 1.32/0.61    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.32/0.61  fof(f156,plain,(
% 1.32/0.61    ~spl13_1),
% 1.32/0.61    inference(avatar_contradiction_clause,[],[f152])).
% 1.32/0.61  fof(f152,plain,(
% 1.32/0.61    $false | ~spl13_1),
% 1.32/0.61    inference(resolution,[],[f107,f62])).
% 1.32/0.61  fof(f62,plain,(
% 1.32/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f9])).
% 1.32/0.61  fof(f9,axiom,(
% 1.32/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.32/0.61  fof(f107,plain,(
% 1.32/0.61    v1_xboole_0(k1_zfmisc_1(sK2)) | ~spl13_1),
% 1.32/0.61    inference(avatar_component_clause,[],[f105])).
% 1.32/0.61  fof(f112,plain,(
% 1.32/0.61    spl13_1 | ~spl13_2),
% 1.32/0.61    inference(avatar_split_clause,[],[f103,f109,f105])).
% 1.32/0.61  fof(f103,plain,(
% 1.32/0.61    ~r2_hidden(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2))),
% 1.32/0.61    inference(resolution,[],[f66,f93])).
% 1.32/0.61  fof(f93,plain,(
% 1.32/0.61    ~m1_subset_1(k2_xboole_0(k2_tarski(sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2))),
% 1.32/0.61    inference(definition_unfolding,[],[f61,f91])).
% 1.32/0.61  fof(f91,plain,(
% 1.32/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 1.32/0.61    inference(cnf_transformation,[],[f3])).
% 1.32/0.61  fof(f3,axiom,(
% 1.32/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 1.32/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
% 1.32/0.61  fof(f61,plain,(
% 1.32/0.61    ~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))),
% 1.32/0.61    inference(cnf_transformation,[],[f33])).
% 1.32/0.61  % SZS output end Proof for theBenchmark
% 1.32/0.61  % (29632)------------------------------
% 1.32/0.61  % (29632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.61  % (29632)Termination reason: Refutation
% 1.32/0.61  
% 1.32/0.61  % (29632)Memory used [KB]: 6652
% 1.32/0.61  % (29632)Time elapsed: 0.186 s
% 1.32/0.61  % (29632)------------------------------
% 1.32/0.61  % (29632)------------------------------
% 1.32/0.62  % (29616)Success in time 0.254 s
%------------------------------------------------------------------------------
