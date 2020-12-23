%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:34 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 293 expanded)
%              Number of leaves         :   37 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  582 (1825 expanded)
%              Number of equality atoms :  100 ( 274 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1000,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f188,f201,f204,f214,f481,f484,f487,f490,f493,f496,f499,f665,f717,f771,f999])).

fof(f999,plain,
    ( ~ spl13_12
    | ~ spl13_13 ),
    inference(avatar_contradiction_clause,[],[f986])).

fof(f986,plain,
    ( $false
    | ~ spl13_12
    | ~ spl13_13 ),
    inference(resolution,[],[f971,f96])).

fof(f96,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( sP0(X7,X5,X4,X3,X2,X1,X0)
    <=> ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f971,plain,
    ( ! [X0] : ~ sP0(X0,sK9,sK8,sK7,sK6,sK5,sK4)
    | ~ spl13_12
    | ~ spl13_13 ),
    inference(resolution,[],[f940,f357])).

fof(f357,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,k4_enumset1(X6,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(resolution,[],[f80,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(definition_folding,[],[f22,f24,f23])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6)
      | ~ sP0(X8,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X8,X6) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ~ sP0(sK12(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK12(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sP0(sK12(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK12(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f45,f46])).

fof(f46,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X7,X6) )
          & ( sP0(X7,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X7,X6) ) )
     => ( ( ~ sP0(sK12(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK12(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sP0(sK12(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK12(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ~ sP0(X7,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f940,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl13_12
    | ~ spl13_13 ),
    inference(resolution,[],[f825,f777])).

fof(f777,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl13_13 ),
    inference(resolution,[],[f196,f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f196,plain,
    ( v1_xboole_0(sK2)
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl13_13
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f825,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)) )
    | ~ spl13_12 ),
    inference(resolution,[],[f186,f440])).

fof(f440,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ r2_hidden(X2,X4)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f434,f94])).

fof(f94,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X1))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f146,f61])).

fof(f61,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f69,f65])).

fof(f65,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f186,plain,
    ( r1_tarski(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),sK2)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl13_12
  <=> r1_tarski(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f771,plain,(
    ~ spl13_1 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | ~ spl13_1 ),
    inference(resolution,[],[f109,f61])).

fof(f109,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl13_1
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f717,plain,
    ( spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f676,f111,f107])).

fof(f111,plain,
    ( spl13_2
  <=> r2_hidden(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f676,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f92,f65])).

fof(f92,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2)) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f60,plain,(
    ~ m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_subset_1)).

fof(f665,plain,(
    ~ spl13_45 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | ~ spl13_45 ),
    inference(trivial_inequality_removal,[],[f663])).

fof(f663,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl13_45 ),
    inference(superposition,[],[f59,f480])).

fof(f480,plain,
    ( k1_xboole_0 = sK2
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl13_45
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f59,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f499,plain,(
    spl13_44 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | spl13_44 ),
    inference(resolution,[],[f476,f58])).

fof(f58,plain,(
    m1_subset_1(sK9,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f476,plain,
    ( ~ m1_subset_1(sK9,sK2)
    | spl13_44 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl13_44
  <=> m1_subset_1(sK9,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f496,plain,(
    spl13_43 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | spl13_43 ),
    inference(resolution,[],[f472,f57])).

fof(f57,plain,(
    m1_subset_1(sK8,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f472,plain,
    ( ~ m1_subset_1(sK8,sK2)
    | spl13_43 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl13_43
  <=> m1_subset_1(sK8,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_43])])).

fof(f493,plain,(
    spl13_42 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | spl13_42 ),
    inference(resolution,[],[f468,f56])).

fof(f56,plain,(
    m1_subset_1(sK7,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f468,plain,
    ( ~ m1_subset_1(sK7,sK2)
    | spl13_42 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl13_42
  <=> m1_subset_1(sK7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f490,plain,(
    spl13_41 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | spl13_41 ),
    inference(resolution,[],[f464,f55])).

fof(f55,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f464,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | spl13_41 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl13_41
  <=> m1_subset_1(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).

fof(f487,plain,(
    spl13_40 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | spl13_40 ),
    inference(resolution,[],[f460,f54])).

fof(f54,plain,(
    m1_subset_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f460,plain,
    ( ~ m1_subset_1(sK5,sK2)
    | spl13_40 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl13_40
  <=> m1_subset_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f484,plain,(
    spl13_39 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | spl13_39 ),
    inference(resolution,[],[f456,f53])).

fof(f53,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f456,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | spl13_39 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl13_39
  <=> m1_subset_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).

fof(f481,plain,
    ( ~ spl13_39
    | ~ spl13_40
    | ~ spl13_41
    | ~ spl13_42
    | ~ spl13_43
    | ~ spl13_44
    | spl13_45
    | spl13_15 ),
    inference(avatar_split_clause,[],[f451,f211,f478,f474,f470,f466,f462,f458,f454])).

fof(f211,plain,
    ( spl13_15
  <=> m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f451,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK9,sK2)
    | ~ m1_subset_1(sK8,sK2)
    | ~ m1_subset_1(sK7,sK2)
    | ~ m1_subset_1(sK6,sK2)
    | ~ m1_subset_1(sK5,sK2)
    | ~ m1_subset_1(sK4,sK2)
    | spl13_15 ),
    inference(resolution,[],[f68,f213])).

fof(f213,plain,
    ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))
    | spl13_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X6,X0)
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
                      ( ! [X6] :
                          ( m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          | k1_xboole_0 = X0
                          | ~ m1_subset_1(X6,X0) )
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
                      ( ! [X6] :
                          ( m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          | k1_xboole_0 = X0
                          | ~ m1_subset_1(X6,X0) )
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
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).

fof(f214,plain,
    ( spl13_1
    | ~ spl13_15
    | spl13_12 ),
    inference(avatar_split_clause,[],[f209,f185,f211,f107])).

fof(f209,plain,
    ( ~ m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | spl13_12 ),
    inference(resolution,[],[f206,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f206,plain,
    ( ~ r2_hidden(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))
    | spl13_12 ),
    inference(resolution,[],[f187,f95])).

fof(f95,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f187,plain,
    ( ~ r1_tarski(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),sK2)
    | spl13_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f204,plain,(
    spl13_14 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl13_14 ),
    inference(resolution,[],[f200,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f200,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl13_14 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl13_14
  <=> m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f201,plain,
    ( spl13_13
    | ~ spl13_14
    | spl13_11 ),
    inference(avatar_split_clause,[],[f192,f181,f198,f194])).

fof(f181,plain,
    ( spl13_11
  <=> r1_tarski(k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f192,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | spl13_11 ),
    inference(resolution,[],[f189,f64])).

fof(f189,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl13_11 ),
    inference(resolution,[],[f183,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f183,plain,
    ( ~ r1_tarski(k1_tarski(sK3),sK2)
    | spl13_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f188,plain,
    ( ~ spl13_11
    | ~ spl13_12
    | spl13_2 ),
    inference(avatar_split_clause,[],[f179,f111,f185,f181])).

fof(f179,plain,
    ( ~ r1_tarski(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),sK2)
    | ~ r1_tarski(k1_tarski(sK3),sK2)
    | spl13_2 ),
    inference(resolution,[],[f76,f115])).

fof(f115,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),sK2)
    | spl13_2 ),
    inference(resolution,[],[f113,f94])).

fof(f113,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f76,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (23614)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (23623)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.50  % (23631)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (23632)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (23624)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (23620)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (23632)Refutation not found, incomplete strategy% (23632)------------------------------
% 0.22/0.53  % (23632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23632)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23632)Memory used [KB]: 10874
% 0.22/0.53  % (23632)Time elapsed: 0.044 s
% 0.22/0.53  % (23632)------------------------------
% 0.22/0.53  % (23632)------------------------------
% 0.22/0.53  % (23609)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (23625)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (23613)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.54  % (23611)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.55  % (23617)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (23617)Refutation not found, incomplete strategy% (23617)------------------------------
% 1.36/0.55  % (23617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (23617)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (23617)Memory used [KB]: 10746
% 1.36/0.55  % (23617)Time elapsed: 0.136 s
% 1.36/0.55  % (23617)------------------------------
% 1.36/0.55  % (23617)------------------------------
% 1.36/0.55  % (23619)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (23608)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.55  % (23638)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  % (23633)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (23626)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.55  % (23628)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.55  % (23636)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.56  % (23610)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.48/0.56  % (23610)Refutation not found, incomplete strategy% (23610)------------------------------
% 1.48/0.56  % (23610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (23610)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (23610)Memory used [KB]: 10746
% 1.48/0.56  % (23610)Time elapsed: 0.143 s
% 1.48/0.56  % (23610)------------------------------
% 1.48/0.56  % (23610)------------------------------
% 1.48/0.56  % (23635)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.56  % (23627)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.56  % (23637)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.57  % (23634)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.57  % (23621)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.57  % (23615)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.57  % (23616)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.57  % (23629)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.58  % (23622)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.58  % (23630)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.59  % (23639)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.02/0.63  % (23675)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.02/0.66  % (23622)Refutation found. Thanks to Tanya!
% 2.02/0.66  % SZS status Theorem for theBenchmark
% 2.02/0.66  % SZS output start Proof for theBenchmark
% 2.02/0.66  fof(f1000,plain,(
% 2.02/0.66    $false),
% 2.02/0.66    inference(avatar_sat_refutation,[],[f188,f201,f204,f214,f481,f484,f487,f490,f493,f496,f499,f665,f717,f771,f999])).
% 2.02/0.66  fof(f999,plain,(
% 2.02/0.66    ~spl13_12 | ~spl13_13),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f986])).
% 2.02/0.66  fof(f986,plain,(
% 2.02/0.66    $false | (~spl13_12 | ~spl13_13)),
% 2.02/0.66    inference(resolution,[],[f971,f96])).
% 2.02/0.66  fof(f96,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6)) )),
% 2.02/0.66    inference(equality_resolution,[],[f89])).
% 2.02/0.66  fof(f89,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6) | X0 != X1) )),
% 2.02/0.66    inference(cnf_transformation,[],[f50])).
% 2.02/0.66  fof(f50,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 2.02/0.66    inference(rectify,[],[f49])).
% 2.02/0.66  fof(f49,plain,(
% 2.02/0.66    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP0(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 2.02/0.66    inference(flattening,[],[f48])).
% 2.02/0.66  fof(f48,plain,(
% 2.02/0.66    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP0(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 2.02/0.66    inference(nnf_transformation,[],[f23])).
% 2.02/0.66  fof(f23,plain,(
% 2.02/0.66    ! [X7,X5,X4,X3,X2,X1,X0] : (sP0(X7,X5,X4,X3,X2,X1,X0) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7))),
% 2.02/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.02/0.66  fof(f971,plain,(
% 2.02/0.66    ( ! [X0] : (~sP0(X0,sK9,sK8,sK7,sK6,sK5,sK4)) ) | (~spl13_12 | ~spl13_13)),
% 2.02/0.66    inference(resolution,[],[f940,f357])).
% 2.02/0.66  fof(f357,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_hidden(X0,k4_enumset1(X6,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.02/0.66    inference(resolution,[],[f80,f102])).
% 2.02/0.66  fof(f102,plain,(
% 2.02/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 2.02/0.66    inference(equality_resolution,[],[f90])).
% 2.02/0.66  fof(f90,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.02/0.66    inference(cnf_transformation,[],[f51])).
% 2.02/0.66  fof(f51,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP1(X0,X1,X2,X3,X4,X5,X6)) & (sP1(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 2.02/0.66    inference(nnf_transformation,[],[f25])).
% 2.02/0.66  fof(f25,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP1(X0,X1,X2,X3,X4,X5,X6))),
% 2.02/0.66    inference(definition_folding,[],[f22,f24,f23])).
% 2.02/0.66  fof(f24,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : (sP1(X0,X1,X2,X3,X4,X5,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 2.02/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.02/0.66  fof(f22,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 2.02/0.66    inference(ennf_transformation,[],[f8])).
% 2.02/0.66  fof(f8,axiom,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
% 2.02/0.66  fof(f80,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X6)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f47])).
% 2.02/0.66  fof(f47,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ((~sP0(sK12(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK12(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP0(sK12(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK12(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f45,f46])).
% 2.02/0.66  fof(f46,plain,(
% 2.02/0.66    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6))) => ((~sP0(sK12(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK12(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP0(sK12(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK12(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f45,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 2.02/0.66    inference(rectify,[],[f44])).
% 2.02/0.66  fof(f44,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | ~sP0(X7,X5,X4,X3,X2,X1,X0)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 2.02/0.66    inference(nnf_transformation,[],[f24])).
% 2.02/0.66  fof(f940,plain,(
% 2.02/0.66    ( ! [X0] : (~r2_hidden(X0,k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9))) ) | (~spl13_12 | ~spl13_13)),
% 2.02/0.66    inference(resolution,[],[f825,f777])).
% 2.02/0.66  fof(f777,plain,(
% 2.02/0.66    ( ! [X2] : (~r2_hidden(X2,sK2)) ) | ~spl13_13),
% 2.02/0.66    inference(resolution,[],[f196,f62])).
% 2.02/0.66  fof(f62,plain,(
% 2.02/0.66    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f37])).
% 2.02/0.66  fof(f37,plain,(
% 2.02/0.66    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK10(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f35,f36])).
% 2.02/0.66  fof(f36,plain,(
% 2.02/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK10(X0),X0))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f35,plain,(
% 2.02/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.02/0.66    inference(rectify,[],[f34])).
% 2.02/0.66  fof(f34,plain,(
% 2.02/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.02/0.66    inference(nnf_transformation,[],[f1])).
% 2.02/0.66  fof(f1,axiom,(
% 2.02/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.02/0.66  fof(f196,plain,(
% 2.02/0.66    v1_xboole_0(sK2) | ~spl13_13),
% 2.02/0.66    inference(avatar_component_clause,[],[f194])).
% 2.02/0.66  fof(f194,plain,(
% 2.02/0.66    spl13_13 <=> v1_xboole_0(sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 2.02/0.66  fof(f825,plain,(
% 2.02/0.66    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9))) ) | ~spl13_12),
% 2.02/0.66    inference(resolution,[],[f186,f440])).
% 2.02/0.66  fof(f440,plain,(
% 2.02/0.66    ( ! [X4,X2,X3] : (~r1_tarski(X4,X3) | ~r2_hidden(X2,X4) | r2_hidden(X2,X3)) )),
% 2.02/0.66    inference(resolution,[],[f434,f94])).
% 2.02/0.66  fof(f94,plain,(
% 2.02/0.66    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.02/0.66    inference(equality_resolution,[],[f71])).
% 2.02/0.66  fof(f71,plain,(
% 2.02/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.02/0.66    inference(cnf_transformation,[],[f42])).
% 2.02/0.66  fof(f42,plain,(
% 2.02/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f40,f41])).
% 2.02/0.66  fof(f41,plain,(
% 2.02/0.66    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1))))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f40,plain,(
% 2.02/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.02/0.66    inference(rectify,[],[f39])).
% 2.02/0.66  fof(f39,plain,(
% 2.02/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.02/0.66    inference(nnf_transformation,[],[f5])).
% 2.02/0.66  fof(f5,axiom,(
% 2.02/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.02/0.66  fof(f434,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_zfmisc_1(X1)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.02/0.66    inference(resolution,[],[f146,f61])).
% 2.02/0.66  fof(f61,plain,(
% 2.02/0.66    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f9])).
% 2.02/0.66  fof(f9,axiom,(
% 2.02/0.66    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.02/0.66  fof(f146,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (v1_xboole_0(k1_zfmisc_1(X2)) | r2_hidden(X0,X2) | ~r2_hidden(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.02/0.66    inference(resolution,[],[f69,f65])).
% 2.02/0.66  fof(f65,plain,(
% 2.02/0.66    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f38])).
% 2.02/0.66  fof(f38,plain,(
% 2.02/0.66    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.02/0.66    inference(nnf_transformation,[],[f16])).
% 2.02/0.66  fof(f16,plain,(
% 2.02/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.02/0.66    inference(ennf_transformation,[],[f7])).
% 2.02/0.66  fof(f7,axiom,(
% 2.02/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.02/0.66  fof(f69,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f19])).
% 2.02/0.66  fof(f19,plain,(
% 2.02/0.66    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/0.66    inference(ennf_transformation,[],[f10])).
% 2.02/0.66  fof(f10,axiom,(
% 2.02/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 2.02/0.66  fof(f186,plain,(
% 2.02/0.66    r1_tarski(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),sK2) | ~spl13_12),
% 2.02/0.66    inference(avatar_component_clause,[],[f185])).
% 2.02/0.66  fof(f185,plain,(
% 2.02/0.66    spl13_12 <=> r1_tarski(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 2.02/0.66  fof(f771,plain,(
% 2.02/0.66    ~spl13_1),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f767])).
% 2.02/0.66  fof(f767,plain,(
% 2.02/0.66    $false | ~spl13_1),
% 2.02/0.66    inference(resolution,[],[f109,f61])).
% 2.02/0.66  fof(f109,plain,(
% 2.02/0.66    v1_xboole_0(k1_zfmisc_1(sK2)) | ~spl13_1),
% 2.02/0.66    inference(avatar_component_clause,[],[f107])).
% 2.02/0.66  fof(f107,plain,(
% 2.02/0.66    spl13_1 <=> v1_xboole_0(k1_zfmisc_1(sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 2.02/0.66  fof(f717,plain,(
% 2.02/0.66    spl13_1 | ~spl13_2),
% 2.02/0.66    inference(avatar_split_clause,[],[f676,f111,f107])).
% 2.02/0.66  fof(f111,plain,(
% 2.02/0.66    spl13_2 <=> r2_hidden(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 2.02/0.66  fof(f676,plain,(
% 2.02/0.66    ~r2_hidden(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2))),
% 2.02/0.66    inference(resolution,[],[f92,f65])).
% 2.02/0.66  fof(f92,plain,(
% 2.02/0.66    ~m1_subset_1(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2))),
% 2.02/0.66    inference(definition_unfolding,[],[f60,f77])).
% 2.02/0.66  fof(f77,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f3])).
% 2.02/0.66  fof(f3,axiom,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 2.02/0.66  fof(f60,plain,(
% 2.02/0.66    ~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f33,plain,(
% 2.02/0.66    ((((((~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK9,sK2)) & m1_subset_1(sK8,sK2)) & m1_subset_1(sK7,sK2)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,sK2)) & m1_subset_1(sK4,sK2)) & m1_subset_1(sK3,sK2)),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f15,f32,f31,f30,f29,f28,f27,f26])).
% 2.02/0.66  fof(f26,plain,(
% 2.02/0.66    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(X2,sK2)) & m1_subset_1(sK3,sK2))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f27,plain,(
% 2.02/0.66    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(X2,sK2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(sK4,sK2))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f28,plain,(
% 2.02/0.66    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,X3,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(sK5,sK2))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f29,plain,(
% 2.02/0.66    ? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,X4,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) => (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(sK6,sK2))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f30,plain,(
% 2.02/0.66    ? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,X5,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) => (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) & m1_subset_1(sK7,sK2))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f31,plain,(
% 2.02/0.66    ? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,X6,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(X6,sK2)) => (? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) & m1_subset_1(sK8,sK2))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f32,plain,(
% 2.02/0.66    ? [X7] : (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,X7),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X7,sK2)) => (~m1_subset_1(k5_enumset1(sK3,sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK9,sK2))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f15,plain,(
% 2.02/0.66    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 2.02/0.66    inference(flattening,[],[f14])).
% 2.02/0.66  fof(f14,plain,(
% 2.02/0.66    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 2.02/0.66    inference(ennf_transformation,[],[f13])).
% 2.02/0.66  fof(f13,negated_conjecture,(
% 2.02/0.66    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => (k1_xboole_0 != X0 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))))))))))),
% 2.02/0.66    inference(negated_conjecture,[],[f12])).
% 2.02/0.66  fof(f12,conjecture,(
% 2.02/0.66    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => (k1_xboole_0 != X0 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))))))))))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_subset_1)).
% 2.02/0.66  fof(f665,plain,(
% 2.02/0.66    ~spl13_45),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f664])).
% 2.02/0.66  fof(f664,plain,(
% 2.02/0.66    $false | ~spl13_45),
% 2.02/0.66    inference(trivial_inequality_removal,[],[f663])).
% 2.02/0.66  fof(f663,plain,(
% 2.02/0.66    k1_xboole_0 != k1_xboole_0 | ~spl13_45),
% 2.02/0.66    inference(superposition,[],[f59,f480])).
% 2.02/0.66  fof(f480,plain,(
% 2.02/0.66    k1_xboole_0 = sK2 | ~spl13_45),
% 2.02/0.66    inference(avatar_component_clause,[],[f478])).
% 2.02/0.66  fof(f478,plain,(
% 2.02/0.66    spl13_45 <=> k1_xboole_0 = sK2),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).
% 2.02/0.66  fof(f59,plain,(
% 2.02/0.66    k1_xboole_0 != sK2),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f499,plain,(
% 2.02/0.66    spl13_44),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f497])).
% 2.02/0.66  fof(f497,plain,(
% 2.02/0.66    $false | spl13_44),
% 2.02/0.66    inference(resolution,[],[f476,f58])).
% 2.02/0.66  fof(f58,plain,(
% 2.02/0.66    m1_subset_1(sK9,sK2)),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f476,plain,(
% 2.02/0.66    ~m1_subset_1(sK9,sK2) | spl13_44),
% 2.02/0.66    inference(avatar_component_clause,[],[f474])).
% 2.02/0.66  fof(f474,plain,(
% 2.02/0.66    spl13_44 <=> m1_subset_1(sK9,sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).
% 2.02/0.66  fof(f496,plain,(
% 2.02/0.66    spl13_43),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f494])).
% 2.02/0.66  fof(f494,plain,(
% 2.02/0.66    $false | spl13_43),
% 2.02/0.66    inference(resolution,[],[f472,f57])).
% 2.02/0.66  fof(f57,plain,(
% 2.02/0.66    m1_subset_1(sK8,sK2)),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f472,plain,(
% 2.02/0.66    ~m1_subset_1(sK8,sK2) | spl13_43),
% 2.02/0.66    inference(avatar_component_clause,[],[f470])).
% 2.02/0.66  fof(f470,plain,(
% 2.02/0.66    spl13_43 <=> m1_subset_1(sK8,sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_43])])).
% 2.02/0.66  fof(f493,plain,(
% 2.02/0.66    spl13_42),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f491])).
% 2.02/0.66  fof(f491,plain,(
% 2.02/0.66    $false | spl13_42),
% 2.02/0.66    inference(resolution,[],[f468,f56])).
% 2.02/0.66  fof(f56,plain,(
% 2.02/0.66    m1_subset_1(sK7,sK2)),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f468,plain,(
% 2.02/0.66    ~m1_subset_1(sK7,sK2) | spl13_42),
% 2.02/0.66    inference(avatar_component_clause,[],[f466])).
% 2.02/0.66  fof(f466,plain,(
% 2.02/0.66    spl13_42 <=> m1_subset_1(sK7,sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).
% 2.02/0.66  fof(f490,plain,(
% 2.02/0.66    spl13_41),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f488])).
% 2.02/0.66  fof(f488,plain,(
% 2.02/0.66    $false | spl13_41),
% 2.02/0.66    inference(resolution,[],[f464,f55])).
% 2.02/0.66  fof(f55,plain,(
% 2.02/0.66    m1_subset_1(sK6,sK2)),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f464,plain,(
% 2.02/0.66    ~m1_subset_1(sK6,sK2) | spl13_41),
% 2.02/0.66    inference(avatar_component_clause,[],[f462])).
% 2.02/0.66  fof(f462,plain,(
% 2.02/0.66    spl13_41 <=> m1_subset_1(sK6,sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).
% 2.02/0.66  fof(f487,plain,(
% 2.02/0.66    spl13_40),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f485])).
% 2.02/0.66  fof(f485,plain,(
% 2.02/0.66    $false | spl13_40),
% 2.02/0.66    inference(resolution,[],[f460,f54])).
% 2.02/0.66  fof(f54,plain,(
% 2.02/0.66    m1_subset_1(sK5,sK2)),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f460,plain,(
% 2.02/0.66    ~m1_subset_1(sK5,sK2) | spl13_40),
% 2.02/0.66    inference(avatar_component_clause,[],[f458])).
% 2.02/0.66  fof(f458,plain,(
% 2.02/0.66    spl13_40 <=> m1_subset_1(sK5,sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).
% 2.02/0.66  fof(f484,plain,(
% 2.02/0.66    spl13_39),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f482])).
% 2.02/0.66  fof(f482,plain,(
% 2.02/0.66    $false | spl13_39),
% 2.02/0.66    inference(resolution,[],[f456,f53])).
% 2.02/0.66  fof(f53,plain,(
% 2.02/0.66    m1_subset_1(sK4,sK2)),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f456,plain,(
% 2.02/0.66    ~m1_subset_1(sK4,sK2) | spl13_39),
% 2.02/0.66    inference(avatar_component_clause,[],[f454])).
% 2.02/0.66  fof(f454,plain,(
% 2.02/0.66    spl13_39 <=> m1_subset_1(sK4,sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).
% 2.02/0.66  fof(f481,plain,(
% 2.02/0.66    ~spl13_39 | ~spl13_40 | ~spl13_41 | ~spl13_42 | ~spl13_43 | ~spl13_44 | spl13_45 | spl13_15),
% 2.02/0.66    inference(avatar_split_clause,[],[f451,f211,f478,f474,f470,f466,f462,f458,f454])).
% 2.02/0.66  fof(f211,plain,(
% 2.02/0.66    spl13_15 <=> m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 2.02/0.66  fof(f451,plain,(
% 2.02/0.66    k1_xboole_0 = sK2 | ~m1_subset_1(sK9,sK2) | ~m1_subset_1(sK8,sK2) | ~m1_subset_1(sK7,sK2) | ~m1_subset_1(sK6,sK2) | ~m1_subset_1(sK5,sK2) | ~m1_subset_1(sK4,sK2) | spl13_15),
% 2.02/0.66    inference(resolution,[],[f68,f213])).
% 2.02/0.66  fof(f213,plain,(
% 2.02/0.66    ~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) | spl13_15),
% 2.02/0.66    inference(avatar_component_clause,[],[f211])).
% 2.02/0.66  fof(f68,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X6,X0) | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f18])).
% 2.02/0.66  fof(f18,plain,(
% 2.02/0.66    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 2.02/0.66    inference(flattening,[],[f17])).
% 2.02/0.66  fof(f17,plain,(
% 2.02/0.66    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 2.02/0.66    inference(ennf_transformation,[],[f11])).
% 2.02/0.66  fof(f11,axiom,(
% 2.02/0.66    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).
% 2.02/0.66  fof(f214,plain,(
% 2.02/0.66    spl13_1 | ~spl13_15 | spl13_12),
% 2.02/0.66    inference(avatar_split_clause,[],[f209,f185,f211,f107])).
% 2.02/0.66  fof(f209,plain,(
% 2.02/0.66    ~m1_subset_1(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2)) | spl13_12),
% 2.02/0.66    inference(resolution,[],[f206,f64])).
% 2.02/0.66  fof(f64,plain,(
% 2.02/0.66    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f38])).
% 2.02/0.66  fof(f206,plain,(
% 2.02/0.66    ~r2_hidden(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(sK2)) | spl13_12),
% 2.02/0.66    inference(resolution,[],[f187,f95])).
% 2.02/0.66  fof(f95,plain,(
% 2.02/0.66    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.02/0.66    inference(equality_resolution,[],[f70])).
% 2.02/0.66  fof(f70,plain,(
% 2.02/0.66    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.02/0.66    inference(cnf_transformation,[],[f42])).
% 2.02/0.66  fof(f187,plain,(
% 2.02/0.66    ~r1_tarski(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),sK2) | spl13_12),
% 2.02/0.66    inference(avatar_component_clause,[],[f185])).
% 2.02/0.66  fof(f204,plain,(
% 2.02/0.66    spl13_14),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f202])).
% 2.02/0.66  fof(f202,plain,(
% 2.02/0.66    $false | spl13_14),
% 2.02/0.66    inference(resolution,[],[f200,f52])).
% 2.02/0.66  fof(f52,plain,(
% 2.02/0.66    m1_subset_1(sK3,sK2)),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f200,plain,(
% 2.02/0.66    ~m1_subset_1(sK3,sK2) | spl13_14),
% 2.02/0.66    inference(avatar_component_clause,[],[f198])).
% 2.02/0.66  fof(f198,plain,(
% 2.02/0.66    spl13_14 <=> m1_subset_1(sK3,sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 2.02/0.66  fof(f201,plain,(
% 2.02/0.66    spl13_13 | ~spl13_14 | spl13_11),
% 2.02/0.66    inference(avatar_split_clause,[],[f192,f181,f198,f194])).
% 2.02/0.66  fof(f181,plain,(
% 2.02/0.66    spl13_11 <=> r1_tarski(k1_tarski(sK3),sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).
% 2.02/0.66  fof(f192,plain,(
% 2.02/0.66    ~m1_subset_1(sK3,sK2) | v1_xboole_0(sK2) | spl13_11),
% 2.02/0.66    inference(resolution,[],[f189,f64])).
% 2.02/0.66  fof(f189,plain,(
% 2.02/0.66    ~r2_hidden(sK3,sK2) | spl13_11),
% 2.02/0.66    inference(resolution,[],[f183,f75])).
% 2.02/0.66  fof(f75,plain,(
% 2.02/0.66    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f43])).
% 2.02/0.66  fof(f43,plain,(
% 2.02/0.66    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.02/0.66    inference(nnf_transformation,[],[f6])).
% 2.02/0.66  fof(f6,axiom,(
% 2.02/0.66    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.02/0.66  fof(f183,plain,(
% 2.02/0.66    ~r1_tarski(k1_tarski(sK3),sK2) | spl13_11),
% 2.02/0.66    inference(avatar_component_clause,[],[f181])).
% 2.02/0.66  fof(f188,plain,(
% 2.02/0.66    ~spl13_11 | ~spl13_12 | spl13_2),
% 2.02/0.66    inference(avatar_split_clause,[],[f179,f111,f185,f181])).
% 2.02/0.66  fof(f179,plain,(
% 2.02/0.66    ~r1_tarski(k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9),sK2) | ~r1_tarski(k1_tarski(sK3),sK2) | spl13_2),
% 2.02/0.66    inference(resolution,[],[f76,f115])).
% 2.02/0.66  fof(f115,plain,(
% 2.02/0.66    ~r1_tarski(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),sK2) | spl13_2),
% 2.02/0.66    inference(resolution,[],[f113,f94])).
% 2.02/0.66  fof(f113,plain,(
% 2.02/0.66    ~r2_hidden(k2_xboole_0(k1_tarski(sK3),k4_enumset1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(sK2)) | spl13_2),
% 2.02/0.66    inference(avatar_component_clause,[],[f111])).
% 2.02/0.66  fof(f76,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f21])).
% 2.02/0.66  fof(f21,plain,(
% 2.02/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.02/0.66    inference(flattening,[],[f20])).
% 2.02/0.66  fof(f20,plain,(
% 2.02/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.02/0.66    inference(ennf_transformation,[],[f2])).
% 2.02/0.66  fof(f2,axiom,(
% 2.02/0.66    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.02/0.66  % SZS output end Proof for theBenchmark
% 2.02/0.66  % (23622)------------------------------
% 2.02/0.66  % (23622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.66  % (23622)Termination reason: Refutation
% 2.02/0.66  
% 2.02/0.66  % (23622)Memory used [KB]: 6780
% 2.02/0.66  % (23622)Time elapsed: 0.249 s
% 2.02/0.66  % (23622)------------------------------
% 2.02/0.66  % (23622)------------------------------
% 2.02/0.67  % (23600)Success in time 0.301 s
%------------------------------------------------------------------------------
