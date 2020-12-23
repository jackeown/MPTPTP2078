%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0726+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:33 EST 2020

% Result     : Theorem 8.53s
% Output     : Refutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :  461 (3069 expanded)
%              Number of leaves         :  122 (1050 expanded)
%              Depth                    :   20
%              Number of atoms          : 1234 (14122 expanded)
%              Number of equality atoms :  214 (5269 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7575,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f116,f131,f136,f141,f146,f151,f174,f185,f190,f195,f207,f212,f217,f222,f227,f239,f244,f249,f254,f288,f293,f298,f303,f308,f313,f330,f335,f340,f345,f350,f355,f360,f365,f370,f375,f380,f385,f434,f439,f529,f534,f539,f544,f549,f561,f566,f571,f576,f581,f587,f592,f597,f602,f607,f612,f735,f749,f754,f759,f764,f769,f828,f833,f838,f843,f857,f862,f912,f917,f931,f936,f941,f946,f2322,f6769,f6782,f6921,f6933,f6944,f6956,f7095,f7107,f7118,f7130,f7141,f7153,f7290,f7304,f7313,f7327,f7336,f7350,f7359,f7373,f7406,f7572])).

fof(f7572,plain,
    ( ~ spl11_3
    | ~ spl11_106 ),
    inference(avatar_contradiction_clause,[],[f7571])).

fof(f7571,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_106 ),
    inference(subsumption_resolution,[],[f7449,f87])).

fof(f87,plain,
    ( r2_hidden(sK3,sK4)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl11_3
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f7449,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ spl11_106 ),
    inference(superposition,[],[f742,f7405])).

fof(f7405,plain,
    ( sK4 = sK9(k4_enumset1(sK4,sK5,sK6,sK7,sK2,sK3))
    | ~ spl11_106 ),
    inference(avatar_component_clause,[],[f7403])).

fof(f7403,plain,
    ( spl11_106
  <=> sK4 = sK9(k4_enumset1(sK4,sK5,sK6,sK7,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_106])])).

fof(f742,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X2,X3,X4,X5,X0))) ),
    inference(unit_resulting_resolution,[],[f518,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK9(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK9(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f19,f28])).

fof(f28,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f518,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X2,X3,X4,X5,X0)) ),
    inference(unit_resulting_resolution,[],[f66,f72,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6)
      | ~ sP0(X8,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X8,X6) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ~ sP0(sK10(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sP0(sK10(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f31,f32])).

fof(f32,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X7,X6) )
          & ( sP0(X7,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X7,X6) ) )
     => ( ( ~ sP0(sK10(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sP0(sK10(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(definition_folding,[],[f20,f22,f21])).

fof(f21,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( sP0(X7,X5,X4,X3,X2,X1,X0)
    <=> ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f66,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f7406,plain,
    ( spl11_106
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f7378,f105,f100,f95,f90,f80,f7403])).

fof(f80,plain,
    ( spl11_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f90,plain,
    ( spl11_4
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f95,plain,
    ( spl11_5
  <=> r2_hidden(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f100,plain,
    ( spl11_6
  <=> r2_hidden(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f105,plain,
    ( spl11_7
  <=> r2_hidden(sK7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f7378,plain,
    ( sK4 = sK9(k4_enumset1(sK4,sK5,sK6,sK7,sK2,sK3))
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f92,f7193])).

fof(f7193,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,sK5)
        | sK9(k4_enumset1(X10,sK5,sK6,sK7,sK2,sK3)) = X10 )
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f924,f7160])).

fof(f7160,plain,
    ( ! [X0] :
        ( sK5 = sK9(k4_enumset1(X0,sK5,sK6,sK7,sK2,sK3))
        | sK9(k4_enumset1(X0,sK5,sK6,sK7,sK2,sK3)) = X0 )
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(resolution,[],[f6993,f97])).

fof(f97,plain,
    ( r2_hidden(sK5,sK6)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f6993,plain,
    ( ! [X17,X16] :
        ( ~ r2_hidden(X17,sK6)
        | sK9(k4_enumset1(X16,X17,sK6,sK7,sK2,sK3)) = X16
        | sK9(k4_enumset1(X16,X17,sK6,sK7,sK2,sK3)) = X17 )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f887,f6963])).

fof(f6963,plain,
    ( ! [X0,X1] :
        ( sK6 = sK9(k4_enumset1(X0,X1,sK6,sK7,sK2,sK3))
        | sK9(k4_enumset1(X0,X1,sK6,sK7,sK2,sK3)) = X0
        | sK9(k4_enumset1(X0,X1,sK6,sK7,sK2,sK3)) = X1 )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(resolution,[],[f6813,f102])).

fof(f102,plain,
    ( r2_hidden(sK6,sK7)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f6813,plain,
    ( ! [X19,X20,X18] :
        ( ~ r2_hidden(X20,sK7)
        | sK9(k4_enumset1(X18,X19,X20,sK7,sK2,sK3)) = X20
        | sK9(k4_enumset1(X18,X19,X20,sK7,sK2,sK3)) = X18
        | sK9(k4_enumset1(X18,X19,X20,sK7,sK2,sK3)) = X19 )
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(superposition,[],[f850,f6786])).

fof(f6786,plain,
    ( ! [X2,X0,X1] :
        ( sK7 = sK9(k4_enumset1(X0,X1,X2,sK7,sK2,sK3))
        | sK9(k4_enumset1(X0,X1,X2,sK7,sK2,sK3)) = X2
        | sK9(k4_enumset1(X0,X1,X2,sK7,sK2,sK3)) = X0
        | sK9(k4_enumset1(X0,X1,X2,sK7,sK2,sK3)) = X1 )
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(resolution,[],[f6657,f107])).

fof(f107,plain,
    ( r2_hidden(sK7,sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f6657,plain,
    ( ! [X19,X17,X18,X16] :
        ( ~ r2_hidden(X19,sK2)
        | sK9(k4_enumset1(X16,X17,X18,X19,sK2,sK3)) = X16
        | sK9(k4_enumset1(X16,X17,X18,X19,sK2,sK3)) = X18
        | sK9(k4_enumset1(X16,X17,X18,X19,sK2,sK3)) = X19
        | sK9(k4_enumset1(X16,X17,X18,X19,sK2,sK3)) = X17 )
    | ~ spl11_2 ),
    inference(superposition,[],[f815,f4777])).

fof(f4777,plain,
    ( ! [X74,X72,X71,X73] :
        ( sK2 = sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3))
        | sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3)) = X71
        | sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3)) = X73
        | sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3)) = X74
        | sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3)) = X72 )
    | ~ spl11_2 ),
    inference(resolution,[],[f1708,f82])).

fof(f82,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1708,plain,(
    ! [X23,X21,X19,X22,X20,X18] :
      ( ~ r2_hidden(X22,X23)
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X19
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X18
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X20
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X21
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X22 ) ),
    inference(superposition,[],[f776,f1229])).

fof(f1229,plain,(
    ! [X54,X52,X50,X53,X51,X49] :
      ( sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X54
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X50
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X49
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X51
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X52
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X53 ) ),
    inference(resolution,[],[f992,f740])).

fof(f740,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(sK9(k4_enumset1(X0,X1,X2,X3,X4,X5)),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f518,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f992,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,k4_enumset1(X4,X3,X2,X1,X6,X5))
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X1
      | X0 = X6 ) ),
    inference(resolution,[],[f556,f72])).

fof(f556,plain,(
    ! [X39,X37,X43,X41,X38,X36,X42,X40] :
      ( ~ sP1(X41,X40,X39,X38,X37,X42,X43)
      | X36 = X38
      | X36 = X39
      | X36 = X40
      | X36 = X41
      | X36 = X42
      | ~ r2_hidden(X36,X43)
      | X36 = X37 ) ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( sP0(X8,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X8,X6)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f776,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X2,X3,X4,X0,X5))) ),
    inference(unit_resulting_resolution,[],[f519,f73])).

fof(f519,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X2,X3,X4,X0,X5)) ),
    inference(unit_resulting_resolution,[],[f67,f72,f54])).

fof(f67,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X2,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f815,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X2,X3,X0,X4,X5))) ),
    inference(unit_resulting_resolution,[],[f520,f73])).

fof(f520,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X2,X3,X0,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f68,f72,f54])).

fof(f68,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X3,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f850,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X2,X0,X3,X4,X5))) ),
    inference(unit_resulting_resolution,[],[f521,f73])).

fof(f521,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X2,X0,X3,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f69,f72,f54])).

fof(f69,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X4,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X4 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f887,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X0,X2,X3,X4,X5))) ),
    inference(unit_resulting_resolution,[],[f522,f73])).

fof(f522,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X0,X2,X3,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f70,f72,f54])).

fof(f70,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X5,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X5 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f924,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X0,X1,X2,X3,X4,X5))) ),
    inference(unit_resulting_resolution,[],[f523,f73])).

fof(f523,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f71,f72,f54])).

fof(f71,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X6,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X6 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f7373,plain,
    ( ~ spl11_105
    | spl11_11
    | spl11_104 ),
    inference(avatar_split_clause,[],[f7368,f7356,f138,f7370])).

fof(f7370,plain,
    ( spl11_105
  <=> m1_subset_1(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_105])])).

fof(f138,plain,
    ( spl11_11
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f7356,plain,
    ( spl11_104
  <=> r2_hidden(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_104])])).

fof(f7368,plain,
    ( ~ m1_subset_1(sK5,sK5)
    | spl11_11
    | spl11_104 ),
    inference(unit_resulting_resolution,[],[f140,f7358,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f7358,plain,
    ( ~ r2_hidden(sK5,sK5)
    | spl11_104 ),
    inference(avatar_component_clause,[],[f7356])).

fof(f140,plain,
    ( ~ v1_xboole_0(sK5)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f7359,plain,
    ( spl11_97
    | ~ spl11_104
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f7192,f105,f100,f95,f80,f7356,f7284])).

fof(f7284,plain,
    ( spl11_97
  <=> ! [X4] : sK9(k4_enumset1(X4,sK5,sK6,sK7,sK2,sK3)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_97])])).

fof(f7192,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK5,sK5)
        | sK9(k4_enumset1(X9,sK5,sK6,sK7,sK2,sK3)) = X9 )
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f887,f7160])).

fof(f7350,plain,
    ( ~ spl11_103
    | spl11_11
    | spl11_102 ),
    inference(avatar_split_clause,[],[f7345,f7333,f138,f7347])).

fof(f7347,plain,
    ( spl11_103
  <=> m1_subset_1(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).

fof(f7333,plain,
    ( spl11_102
  <=> r2_hidden(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_102])])).

fof(f7345,plain,
    ( ~ m1_subset_1(sK7,sK5)
    | spl11_11
    | spl11_102 ),
    inference(unit_resulting_resolution,[],[f140,f7335,f47])).

fof(f7335,plain,
    ( ~ r2_hidden(sK7,sK5)
    | spl11_102 ),
    inference(avatar_component_clause,[],[f7333])).

fof(f7336,plain,
    ( spl11_97
    | ~ spl11_102
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f7190,f105,f100,f95,f80,f7333,f7284])).

fof(f7190,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK7,sK5)
        | sK9(k4_enumset1(X7,sK5,sK6,sK7,sK2,sK3)) = X7 )
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f815,f7160])).

fof(f7327,plain,
    ( ~ spl11_101
    | spl11_11
    | spl11_100 ),
    inference(avatar_split_clause,[],[f7322,f7310,f138,f7324])).

fof(f7324,plain,
    ( spl11_101
  <=> m1_subset_1(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_101])])).

fof(f7310,plain,
    ( spl11_100
  <=> r2_hidden(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f7322,plain,
    ( ~ m1_subset_1(sK2,sK5)
    | spl11_11
    | spl11_100 ),
    inference(unit_resulting_resolution,[],[f140,f7312,f47])).

fof(f7312,plain,
    ( ~ r2_hidden(sK2,sK5)
    | spl11_100 ),
    inference(avatar_component_clause,[],[f7310])).

fof(f7313,plain,
    ( spl11_97
    | ~ spl11_100
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f7189,f105,f100,f95,f80,f7310,f7284])).

fof(f7189,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK2,sK5)
        | sK9(k4_enumset1(X6,sK5,sK6,sK7,sK2,sK3)) = X6 )
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f776,f7160])).

fof(f7304,plain,
    ( ~ spl11_99
    | spl11_11
    | spl11_98 ),
    inference(avatar_split_clause,[],[f7299,f7287,f138,f7301])).

fof(f7301,plain,
    ( spl11_99
  <=> m1_subset_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).

fof(f7287,plain,
    ( spl11_98
  <=> r2_hidden(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_98])])).

fof(f7299,plain,
    ( ~ m1_subset_1(sK3,sK5)
    | spl11_11
    | spl11_98 ),
    inference(unit_resulting_resolution,[],[f140,f7289,f47])).

fof(f7289,plain,
    ( ~ r2_hidden(sK3,sK5)
    | spl11_98 ),
    inference(avatar_component_clause,[],[f7287])).

fof(f7290,plain,
    ( spl11_97
    | ~ spl11_98
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f7187,f105,f100,f95,f80,f7287,f7284])).

fof(f7187,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK3,sK5)
        | sK9(k4_enumset1(X4,sK5,sK6,sK7,sK2,sK3)) = X4 )
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f742,f7160])).

fof(f7153,plain,
    ( ~ spl11_96
    | spl11_12
    | spl11_95 ),
    inference(avatar_split_clause,[],[f7148,f7138,f143,f7150])).

fof(f7150,plain,
    ( spl11_96
  <=> m1_subset_1(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_96])])).

fof(f143,plain,
    ( spl11_12
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f7138,plain,
    ( spl11_95
  <=> r2_hidden(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_95])])).

fof(f7148,plain,
    ( ~ m1_subset_1(sK6,sK6)
    | spl11_12
    | spl11_95 ),
    inference(unit_resulting_resolution,[],[f145,f7140,f47])).

fof(f7140,plain,
    ( ~ r2_hidden(sK6,sK6)
    | spl11_95 ),
    inference(avatar_component_clause,[],[f7138])).

fof(f145,plain,
    ( ~ v1_xboole_0(sK6)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f7141,plain,
    ( spl11_90
    | ~ spl11_95
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f6992,f105,f100,f80,f7138,f7089])).

fof(f7089,plain,
    ( spl11_90
  <=> ! [X7,X6] :
        ( sK9(k4_enumset1(X6,X7,sK6,sK7,sK2,sK3)) = X6
        | sK9(k4_enumset1(X6,X7,sK6,sK7,sK2,sK3)) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f6992,plain,
    ( ! [X14,X15] :
        ( ~ r2_hidden(sK6,sK6)
        | sK9(k4_enumset1(X14,X15,sK6,sK7,sK2,sK3)) = X14
        | sK9(k4_enumset1(X14,X15,sK6,sK7,sK2,sK3)) = X15 )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f850,f6963])).

fof(f7130,plain,
    ( ~ spl11_94
    | spl11_12
    | spl11_93 ),
    inference(avatar_split_clause,[],[f7125,f7115,f143,f7127])).

fof(f7127,plain,
    ( spl11_94
  <=> m1_subset_1(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f7115,plain,
    ( spl11_93
  <=> r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_93])])).

fof(f7125,plain,
    ( ~ m1_subset_1(sK2,sK6)
    | spl11_12
    | spl11_93 ),
    inference(unit_resulting_resolution,[],[f145,f7117,f47])).

fof(f7117,plain,
    ( ~ r2_hidden(sK2,sK6)
    | spl11_93 ),
    inference(avatar_component_clause,[],[f7115])).

fof(f7118,plain,
    ( spl11_90
    | ~ spl11_93
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f6990,f105,f100,f80,f7115,f7089])).

fof(f6990,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(sK2,sK6)
        | sK9(k4_enumset1(X10,X11,sK6,sK7,sK2,sK3)) = X10
        | sK9(k4_enumset1(X10,X11,sK6,sK7,sK2,sK3)) = X11 )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f776,f6963])).

fof(f7107,plain,
    ( ~ spl11_92
    | spl11_12
    | spl11_91 ),
    inference(avatar_split_clause,[],[f7102,f7092,f143,f7104])).

fof(f7104,plain,
    ( spl11_92
  <=> m1_subset_1(sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f7092,plain,
    ( spl11_91
  <=> r2_hidden(sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_91])])).

fof(f7102,plain,
    ( ~ m1_subset_1(sK3,sK6)
    | spl11_12
    | spl11_91 ),
    inference(unit_resulting_resolution,[],[f145,f7094,f47])).

fof(f7094,plain,
    ( ~ r2_hidden(sK3,sK6)
    | spl11_91 ),
    inference(avatar_component_clause,[],[f7092])).

fof(f7095,plain,
    ( spl11_90
    | ~ spl11_91
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f6988,f105,f100,f80,f7092,f7089])).

fof(f6988,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(sK3,sK6)
        | sK9(k4_enumset1(X6,X7,sK6,sK7,sK2,sK3)) = X6
        | sK9(k4_enumset1(X6,X7,sK6,sK7,sK2,sK3)) = X7 )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(superposition,[],[f742,f6963])).

fof(f6956,plain,
    ( ~ spl11_89
    | spl11_13
    | spl11_88 ),
    inference(avatar_split_clause,[],[f6951,f6941,f148,f6953])).

fof(f6953,plain,
    ( spl11_89
  <=> m1_subset_1(sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).

fof(f148,plain,
    ( spl11_13
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f6941,plain,
    ( spl11_88
  <=> r2_hidden(sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f6951,plain,
    ( ~ m1_subset_1(sK7,sK7)
    | spl11_13
    | spl11_88 ),
    inference(unit_resulting_resolution,[],[f150,f6943,f47])).

fof(f6943,plain,
    ( ~ r2_hidden(sK7,sK7)
    | spl11_88 ),
    inference(avatar_component_clause,[],[f6941])).

fof(f150,plain,
    ( ~ v1_xboole_0(sK7)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f6944,plain,
    ( spl11_85
    | ~ spl11_88
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f6812,f105,f80,f6941,f6915])).

fof(f6915,plain,
    ( spl11_85
  <=> ! [X7,X8,X6] :
        ( sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X8
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X7
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_85])])).

fof(f6812,plain,
    ( ! [X17,X15,X16] :
        ( ~ r2_hidden(sK7,sK7)
        | sK9(k4_enumset1(X15,X16,X17,sK7,sK2,sK3)) = X17
        | sK9(k4_enumset1(X15,X16,X17,sK7,sK2,sK3)) = X15
        | sK9(k4_enumset1(X15,X16,X17,sK7,sK2,sK3)) = X16 )
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(superposition,[],[f815,f6786])).

fof(f6933,plain,
    ( ~ spl11_87
    | spl11_13
    | spl11_86 ),
    inference(avatar_split_clause,[],[f6928,f6918,f148,f6930])).

fof(f6930,plain,
    ( spl11_87
  <=> m1_subset_1(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f6918,plain,
    ( spl11_86
  <=> r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f6928,plain,
    ( ~ m1_subset_1(sK3,sK7)
    | spl11_13
    | spl11_86 ),
    inference(unit_resulting_resolution,[],[f150,f6920,f47])).

fof(f6920,plain,
    ( ~ r2_hidden(sK3,sK7)
    | spl11_86 ),
    inference(avatar_component_clause,[],[f6918])).

fof(f6921,plain,
    ( spl11_85
    | ~ spl11_86
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f6809,f105,f80,f6918,f6915])).

fof(f6809,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(sK3,sK7)
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X8
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X6
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X7 )
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(superposition,[],[f742,f6786])).

fof(f6782,plain,
    ( ~ spl11_84
    | spl11_14
    | spl11_83 ),
    inference(avatar_split_clause,[],[f6776,f6766,f171,f6779])).

fof(f6779,plain,
    ( spl11_84
  <=> m1_subset_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f171,plain,
    ( spl11_14
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f6766,plain,
    ( spl11_83
  <=> r2_hidden(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_83])])).

fof(f6776,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | spl11_14
    | spl11_83 ),
    inference(unit_resulting_resolution,[],[f173,f6768,f47])).

fof(f6768,plain,
    ( ~ r2_hidden(sK2,sK2)
    | spl11_83 ),
    inference(avatar_component_clause,[],[f6766])).

fof(f173,plain,
    ( ~ v1_xboole_0(sK2)
    | spl11_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f6769,plain,
    ( spl11_82
    | ~ spl11_83
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f6656,f80,f6766,f6763])).

fof(f6763,plain,
    ( spl11_82
  <=> ! [X13,X15,X12,X14] :
        ( sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X12
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X13
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X15
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f6656,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ r2_hidden(sK2,sK2)
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X12
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X14
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X15
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X13 )
    | ~ spl11_2 ),
    inference(superposition,[],[f776,f4777])).

fof(f2322,plain,
    ( spl11_81
    | ~ spl11_1
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f2262,f113,f75,f2319])).

fof(f2319,plain,
    ( spl11_81
  <=> o_0_0_xboole_0 = sK10(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_81])])).

fof(f75,plain,
    ( spl11_1
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f113,plain,
    ( spl11_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f2262,plain,
    ( o_0_0_xboole_0 = sK10(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl11_1
    | ~ spl11_8 ),
    inference(forward_demodulation,[],[f2260,f115])).

fof(f115,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f2260,plain,
    ( k1_xboole_0 = sK10(k1_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl11_1
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f115,f2258])).

fof(f2258,plain,
    ( ! [X0,X1] :
        ( X0 != X1
        | sK10(X0,X1,X1,X1,X1,X1,o_0_0_xboole_0) = X0 )
    | ~ spl11_1 ),
    inference(equality_factoring,[],[f2218])).

fof(f2218,plain,
    ( ! [X0,X1] :
        ( sK10(X0,X1,X1,X1,X1,X1,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X1,X1,X1,X1,o_0_0_xboole_0) = X0 )
    | ~ spl11_1 ),
    inference(equality_resolution,[],[f2216])).

fof(f2216,plain,
    ( ! [X2,X0,X1] :
        ( X1 != X2
        | sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X0 )
    | ~ spl11_1 ),
    inference(equality_factoring,[],[f2176])).

fof(f2176,plain,
    ( ! [X2,X0,X1] :
        ( sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X2
        | sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X0 )
    | ~ spl11_1 ),
    inference(equality_resolution,[],[f2160])).

fof(f2160,plain,
    ( ! [X2,X0,X3,X1] :
        ( X2 != X3
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X2
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X0 )
    | ~ spl11_1 ),
    inference(equality_factoring,[],[f2121])).

fof(f2121,plain,
    ( ! [X2,X0,X3,X1] :
        ( sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X3
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X2
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X0 )
    | ~ spl11_1 ),
    inference(equality_resolution,[],[f2120])).

fof(f2120,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( X0 != X1
        | sK10(X2,X3,X4,X0,X0,X1,o_0_0_xboole_0) = X0
        | sK10(X2,X3,X4,X0,X0,X1,o_0_0_xboole_0) = X4
        | sK10(X2,X3,X4,X0,X0,X1,o_0_0_xboole_0) = X3
        | sK10(X2,X3,X4,X0,X0,X1,o_0_0_xboole_0) = X2 )
    | ~ spl11_1 ),
    inference(equality_resolution,[],[f1892])).

fof(f1892,plain,
    ( ! [X30,X28,X26,X31,X29,X27] :
        ( X26 != X27
        | X27 != X28
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X26
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X31
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X30
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X29 )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1883,f505])).

fof(f505,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : ~ sP1(X0,X1,X2,X3,X4,X5,o_0_0_xboole_0)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f123,f71,f54])).

fof(f123,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f77,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f77,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f1883,plain,
    ( ! [X30,X28,X26,X31,X29,X27] :
        ( X26 != X27
        | X27 != X28
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X26
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X31
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X30
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X29
        | sP1(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) )
    | ~ spl11_1 ),
    inference(resolution,[],[f1259,f123])).

fof(f1259,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6)
      | X3 != X4
      | X4 != X5
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X3
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X2
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X1
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X0
      | sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(equality_factoring,[],[f1001])).

fof(f1001,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sK10(X0,X1,X2,X3,X4,X5,X6) = X4
      | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6)
      | X4 != X5
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X3
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X2
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X1
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X0
      | sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(equality_factoring,[],[f582])).

fof(f582,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sK10(X0,X1,X2,X3,X4,X5,X6) = X5
      | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6)
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X4
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X3
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X2
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X1
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X0
      | sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(resolution,[],[f55,f57])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(sK10(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
      | sP1(X0,X1,X2,X3,X4,X5,X6)
      | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f946,plain,
    ( ~ spl11_80
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f663,f541,f943])).

fof(f943,plain,
    ( spl11_80
  <=> r2_hidden(sK8(sK7),sK9(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f541,plain,
    ( spl11_50
  <=> r2_hidden(sK8(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f663,plain,
    ( ~ r2_hidden(sK8(sK7),sK9(sK7))
    | ~ spl11_50 ),
    inference(unit_resulting_resolution,[],[f543,f73])).

fof(f543,plain,
    ( r2_hidden(sK8(sK7),sK7)
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f541])).

fof(f941,plain,
    ( ~ spl11_79
    | ~ spl11_49 ),
    inference(avatar_split_clause,[],[f656,f536,f938])).

fof(f938,plain,
    ( spl11_79
  <=> r2_hidden(sK8(sK6),sK9(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).

fof(f536,plain,
    ( spl11_49
  <=> r2_hidden(sK8(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f656,plain,
    ( ~ r2_hidden(sK8(sK6),sK9(sK6))
    | ~ spl11_49 ),
    inference(unit_resulting_resolution,[],[f538,f73])).

fof(f538,plain,
    ( r2_hidden(sK8(sK6),sK6)
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f536])).

fof(f936,plain,
    ( ~ spl11_78
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f639,f531,f933])).

fof(f933,plain,
    ( spl11_78
  <=> r2_hidden(sK8(sK5),sK9(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f531,plain,
    ( spl11_48
  <=> r2_hidden(sK8(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f639,plain,
    ( ~ r2_hidden(sK8(sK5),sK9(sK5))
    | ~ spl11_48 ),
    inference(unit_resulting_resolution,[],[f533,f73])).

fof(f533,plain,
    ( r2_hidden(sK8(sK5),sK5)
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f531])).

fof(f931,plain,
    ( ~ spl11_77
    | ~ spl11_47 ),
    inference(avatar_split_clause,[],[f632,f526,f928])).

fof(f928,plain,
    ( spl11_77
  <=> r2_hidden(sK8(sK4),sK9(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_77])])).

fof(f526,plain,
    ( spl11_47
  <=> r2_hidden(sK8(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f632,plain,
    ( ~ r2_hidden(sK8(sK4),sK9(sK4))
    | ~ spl11_47 ),
    inference(unit_resulting_resolution,[],[f528,f73])).

fof(f528,plain,
    ( r2_hidden(sK8(sK4),sK4)
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f526])).

fof(f917,plain,
    ( ~ spl11_76
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f625,f436,f914])).

fof(f914,plain,
    ( spl11_76
  <=> r2_hidden(sK8(sK3),sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f436,plain,
    ( spl11_46
  <=> r2_hidden(sK8(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f625,plain,
    ( ~ r2_hidden(sK8(sK3),sK9(sK3))
    | ~ spl11_46 ),
    inference(unit_resulting_resolution,[],[f438,f73])).

fof(f438,plain,
    ( r2_hidden(sK8(sK3),sK3)
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f436])).

fof(f912,plain,
    ( ~ spl11_75
    | ~ spl11_45 ),
    inference(avatar_split_clause,[],[f618,f431,f909])).

fof(f909,plain,
    ( spl11_75
  <=> r2_hidden(sK8(sK2),sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_75])])).

fof(f431,plain,
    ( spl11_45
  <=> r2_hidden(sK8(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f618,plain,
    ( ~ r2_hidden(sK8(sK2),sK9(sK2))
    | ~ spl11_45 ),
    inference(unit_resulting_resolution,[],[f433,f73])).

fof(f433,plain,
    ( r2_hidden(sK8(sK2),sK2)
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f431])).

fof(f862,plain,
    ( ~ spl11_74
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f423,f352,f859])).

fof(f859,plain,
    ( spl11_74
  <=> r2_hidden(sK9(sK2),sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f352,plain,
    ( spl11_38
  <=> r2_hidden(sK9(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f423,plain,
    ( ~ r2_hidden(sK9(sK2),sK9(sK2))
    | ~ spl11_38 ),
    inference(unit_resulting_resolution,[],[f354,f73])).

fof(f354,plain,
    ( r2_hidden(sK9(sK2),sK2)
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f352])).

fof(f857,plain,
    ( ~ spl11_73
    | ~ spl11_37 ),
    inference(avatar_split_clause,[],[f416,f347,f854])).

fof(f854,plain,
    ( spl11_73
  <=> r2_hidden(sK9(sK7),sK9(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_73])])).

fof(f347,plain,
    ( spl11_37
  <=> r2_hidden(sK9(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f416,plain,
    ( ~ r2_hidden(sK9(sK7),sK9(sK7))
    | ~ spl11_37 ),
    inference(unit_resulting_resolution,[],[f349,f73])).

fof(f349,plain,
    ( r2_hidden(sK9(sK7),sK7)
    | ~ spl11_37 ),
    inference(avatar_component_clause,[],[f347])).

fof(f843,plain,
    ( ~ spl11_72
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f407,f342,f840])).

fof(f840,plain,
    ( spl11_72
  <=> r2_hidden(sK9(sK6),sK9(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f342,plain,
    ( spl11_36
  <=> r2_hidden(sK9(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f407,plain,
    ( ~ r2_hidden(sK9(sK6),sK9(sK6))
    | ~ spl11_36 ),
    inference(unit_resulting_resolution,[],[f344,f73])).

fof(f344,plain,
    ( r2_hidden(sK9(sK6),sK6)
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f342])).

fof(f838,plain,
    ( ~ spl11_71
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f400,f337,f835])).

fof(f835,plain,
    ( spl11_71
  <=> r2_hidden(sK9(sK5),sK9(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_71])])).

fof(f337,plain,
    ( spl11_35
  <=> r2_hidden(sK9(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f400,plain,
    ( ~ r2_hidden(sK9(sK5),sK9(sK5))
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f339,f73])).

fof(f339,plain,
    ( r2_hidden(sK9(sK5),sK5)
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f337])).

fof(f833,plain,
    ( ~ spl11_70
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f393,f332,f830])).

fof(f830,plain,
    ( spl11_70
  <=> r2_hidden(sK9(sK4),sK9(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f332,plain,
    ( spl11_34
  <=> r2_hidden(sK9(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f393,plain,
    ( ~ r2_hidden(sK9(sK4),sK9(sK4))
    | ~ spl11_34 ),
    inference(unit_resulting_resolution,[],[f334,f73])).

fof(f334,plain,
    ( r2_hidden(sK9(sK4),sK4)
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f332])).

fof(f828,plain,
    ( ~ spl11_69
    | ~ spl11_33 ),
    inference(avatar_split_clause,[],[f386,f327,f825])).

fof(f825,plain,
    ( spl11_69
  <=> r2_hidden(sK9(sK3),sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_69])])).

fof(f327,plain,
    ( spl11_33
  <=> r2_hidden(sK9(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f386,plain,
    ( ~ r2_hidden(sK9(sK3),sK9(sK3))
    | ~ spl11_33 ),
    inference(unit_resulting_resolution,[],[f329,f73])).

fof(f329,plain,
    ( r2_hidden(sK9(sK3),sK3)
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f327])).

fof(f769,plain,
    ( ~ spl11_68
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f659,f541,f766])).

fof(f766,plain,
    ( spl11_68
  <=> r2_hidden(sK7,sK8(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f659,plain,
    ( ~ r2_hidden(sK7,sK8(sK7))
    | ~ spl11_50 ),
    inference(unit_resulting_resolution,[],[f543,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f764,plain,
    ( ~ spl11_67
    | ~ spl11_49 ),
    inference(avatar_split_clause,[],[f652,f536,f761])).

fof(f761,plain,
    ( spl11_67
  <=> r2_hidden(sK6,sK8(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_67])])).

fof(f652,plain,
    ( ~ r2_hidden(sK6,sK8(sK6))
    | ~ spl11_49 ),
    inference(unit_resulting_resolution,[],[f538,f48])).

fof(f759,plain,
    ( ~ spl11_66
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f635,f531,f756])).

fof(f756,plain,
    ( spl11_66
  <=> r2_hidden(sK5,sK8(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f635,plain,
    ( ~ r2_hidden(sK5,sK8(sK5))
    | ~ spl11_48 ),
    inference(unit_resulting_resolution,[],[f533,f48])).

fof(f754,plain,
    ( ~ spl11_65
    | ~ spl11_47 ),
    inference(avatar_split_clause,[],[f628,f526,f751])).

fof(f751,plain,
    ( spl11_65
  <=> r2_hidden(sK4,sK8(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).

fof(f628,plain,
    ( ~ r2_hidden(sK4,sK8(sK4))
    | ~ spl11_47 ),
    inference(unit_resulting_resolution,[],[f528,f48])).

fof(f749,plain,
    ( ~ spl11_64
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f621,f436,f746])).

fof(f746,plain,
    ( spl11_64
  <=> r2_hidden(sK3,sK8(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f621,plain,
    ( ~ r2_hidden(sK3,sK8(sK3))
    | ~ spl11_46 ),
    inference(unit_resulting_resolution,[],[f438,f48])).

fof(f735,plain,
    ( ~ spl11_63
    | ~ spl11_45 ),
    inference(avatar_split_clause,[],[f614,f431,f732])).

fof(f732,plain,
    ( spl11_63
  <=> r2_hidden(sK2,sK8(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f614,plain,
    ( ~ r2_hidden(sK2,sK8(sK2))
    | ~ spl11_45 ),
    inference(unit_resulting_resolution,[],[f433,f48])).

fof(f612,plain,
    ( ~ spl11_62
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f427,f352,f609])).

fof(f609,plain,
    ( spl11_62
  <=> r2_hidden(sK2,sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f427,plain,
    ( ~ r2_hidden(sK2,sK9(sK2))
    | ~ spl11_38 ),
    inference(unit_resulting_resolution,[],[f354,f48])).

fof(f607,plain,
    ( spl11_61
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f425,f352,f604])).

fof(f604,plain,
    ( spl11_61
  <=> m1_subset_1(sK9(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f425,plain,
    ( m1_subset_1(sK9(sK2),sK2)
    | ~ spl11_38 ),
    inference(unit_resulting_resolution,[],[f354,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f602,plain,
    ( ~ spl11_60
    | ~ spl11_37 ),
    inference(avatar_split_clause,[],[f420,f347,f599])).

fof(f599,plain,
    ( spl11_60
  <=> r2_hidden(sK7,sK9(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f420,plain,
    ( ~ r2_hidden(sK7,sK9(sK7))
    | ~ spl11_37 ),
    inference(unit_resulting_resolution,[],[f349,f48])).

fof(f597,plain,
    ( spl11_59
    | ~ spl11_37 ),
    inference(avatar_split_clause,[],[f418,f347,f594])).

fof(f594,plain,
    ( spl11_59
  <=> m1_subset_1(sK9(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f418,plain,
    ( m1_subset_1(sK9(sK7),sK7)
    | ~ spl11_37 ),
    inference(unit_resulting_resolution,[],[f349,f49])).

fof(f592,plain,
    ( ~ spl11_58
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f411,f342,f589])).

fof(f589,plain,
    ( spl11_58
  <=> r2_hidden(sK6,sK9(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f411,plain,
    ( ~ r2_hidden(sK6,sK9(sK6))
    | ~ spl11_36 ),
    inference(unit_resulting_resolution,[],[f344,f48])).

fof(f587,plain,
    ( spl11_57
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f409,f342,f584])).

fof(f584,plain,
    ( spl11_57
  <=> m1_subset_1(sK9(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f409,plain,
    ( m1_subset_1(sK9(sK6),sK6)
    | ~ spl11_36 ),
    inference(unit_resulting_resolution,[],[f344,f49])).

fof(f581,plain,
    ( ~ spl11_56
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f404,f337,f578])).

fof(f578,plain,
    ( spl11_56
  <=> r2_hidden(sK5,sK9(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f404,plain,
    ( ~ r2_hidden(sK5,sK9(sK5))
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f339,f48])).

fof(f576,plain,
    ( spl11_55
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f402,f337,f573])).

fof(f573,plain,
    ( spl11_55
  <=> m1_subset_1(sK9(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f402,plain,
    ( m1_subset_1(sK9(sK5),sK5)
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f339,f49])).

fof(f571,plain,
    ( ~ spl11_54
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f397,f332,f568])).

fof(f568,plain,
    ( spl11_54
  <=> r2_hidden(sK4,sK9(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f397,plain,
    ( ~ r2_hidden(sK4,sK9(sK4))
    | ~ spl11_34 ),
    inference(unit_resulting_resolution,[],[f334,f48])).

fof(f566,plain,
    ( spl11_53
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f395,f332,f563])).

fof(f563,plain,
    ( spl11_53
  <=> m1_subset_1(sK9(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f395,plain,
    ( m1_subset_1(sK9(sK4),sK4)
    | ~ spl11_34 ),
    inference(unit_resulting_resolution,[],[f334,f49])).

fof(f561,plain,
    ( ~ spl11_52
    | ~ spl11_33 ),
    inference(avatar_split_clause,[],[f390,f327,f558])).

fof(f558,plain,
    ( spl11_52
  <=> r2_hidden(sK3,sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f390,plain,
    ( ~ r2_hidden(sK3,sK9(sK3))
    | ~ spl11_33 ),
    inference(unit_resulting_resolution,[],[f329,f48])).

fof(f549,plain,
    ( spl11_51
    | ~ spl11_33 ),
    inference(avatar_split_clause,[],[f388,f327,f546])).

fof(f546,plain,
    ( spl11_51
  <=> m1_subset_1(sK9(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f388,plain,
    ( m1_subset_1(sK9(sK3),sK3)
    | ~ spl11_33 ),
    inference(unit_resulting_resolution,[],[f329,f49])).

fof(f544,plain,
    ( spl11_50
    | spl11_13 ),
    inference(avatar_split_clause,[],[f261,f148,f541])).

fof(f261,plain,
    ( r2_hidden(sK8(sK7),sK7)
    | spl11_13 ),
    inference(unit_resulting_resolution,[],[f150,f46,f47])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f4,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f539,plain,
    ( spl11_49
    | spl11_12 ),
    inference(avatar_split_clause,[],[f260,f143,f536])).

fof(f260,plain,
    ( r2_hidden(sK8(sK6),sK6)
    | spl11_12 ),
    inference(unit_resulting_resolution,[],[f145,f46,f47])).

fof(f534,plain,
    ( spl11_48
    | spl11_11 ),
    inference(avatar_split_clause,[],[f259,f138,f531])).

fof(f259,plain,
    ( r2_hidden(sK8(sK5),sK5)
    | spl11_11 ),
    inference(unit_resulting_resolution,[],[f140,f46,f47])).

fof(f529,plain,
    ( spl11_47
    | spl11_10 ),
    inference(avatar_split_clause,[],[f258,f133,f526])).

fof(f133,plain,
    ( spl11_10
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f258,plain,
    ( r2_hidden(sK8(sK4),sK4)
    | spl11_10 ),
    inference(unit_resulting_resolution,[],[f135,f46,f47])).

fof(f135,plain,
    ( ~ v1_xboole_0(sK4)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f439,plain,
    ( spl11_46
    | spl11_9 ),
    inference(avatar_split_clause,[],[f257,f128,f436])).

fof(f128,plain,
    ( spl11_9
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f257,plain,
    ( r2_hidden(sK8(sK3),sK3)
    | spl11_9 ),
    inference(unit_resulting_resolution,[],[f130,f46,f47])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK3)
    | spl11_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f434,plain,
    ( spl11_45
    | spl11_14 ),
    inference(avatar_split_clause,[],[f256,f171,f431])).

fof(f256,plain,
    ( r2_hidden(sK8(sK2),sK2)
    | spl11_14 ),
    inference(unit_resulting_resolution,[],[f173,f46,f47])).

fof(f385,plain,
    ( ~ spl11_44
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f233,f105,f382])).

fof(f382,plain,
    ( spl11_44
  <=> r2_hidden(sK7,sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f233,plain,
    ( ~ r2_hidden(sK7,sK9(sK2))
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f107,f73])).

fof(f380,plain,
    ( ~ spl11_43
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f232,f100,f377])).

fof(f377,plain,
    ( spl11_43
  <=> r2_hidden(sK6,sK9(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f232,plain,
    ( ~ r2_hidden(sK6,sK9(sK7))
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f102,f73])).

fof(f375,plain,
    ( ~ spl11_42
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f231,f95,f372])).

fof(f372,plain,
    ( spl11_42
  <=> r2_hidden(sK5,sK9(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f231,plain,
    ( ~ r2_hidden(sK5,sK9(sK6))
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f97,f73])).

fof(f370,plain,
    ( ~ spl11_41
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f230,f90,f367])).

fof(f367,plain,
    ( spl11_41
  <=> r2_hidden(sK4,sK9(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f230,plain,
    ( ~ r2_hidden(sK4,sK9(sK5))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f92,f73])).

fof(f365,plain,
    ( ~ spl11_40
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f229,f85,f362])).

fof(f362,plain,
    ( spl11_40
  <=> r2_hidden(sK3,sK9(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f229,plain,
    ( ~ r2_hidden(sK3,sK9(sK4))
    | ~ spl11_3 ),
    inference(unit_resulting_resolution,[],[f87,f73])).

fof(f360,plain,
    ( ~ spl11_39
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f228,f80,f357])).

fof(f357,plain,
    ( spl11_39
  <=> r2_hidden(sK2,sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f228,plain,
    ( ~ r2_hidden(sK2,sK9(sK3))
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f82,f73])).

fof(f355,plain,
    ( spl11_38
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f201,f105,f352])).

fof(f201,plain,
    ( r2_hidden(sK9(sK2),sK2)
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f107,f51])).

fof(f350,plain,
    ( spl11_37
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f200,f100,f347])).

fof(f200,plain,
    ( r2_hidden(sK9(sK7),sK7)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f102,f51])).

fof(f345,plain,
    ( spl11_36
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f199,f95,f342])).

fof(f199,plain,
    ( r2_hidden(sK9(sK6),sK6)
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f97,f51])).

fof(f340,plain,
    ( spl11_35
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f198,f90,f337])).

fof(f198,plain,
    ( r2_hidden(sK9(sK5),sK5)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f92,f51])).

fof(f335,plain,
    ( spl11_34
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f197,f85,f332])).

fof(f197,plain,
    ( r2_hidden(sK9(sK4),sK4)
    | ~ spl11_3 ),
    inference(unit_resulting_resolution,[],[f87,f51])).

fof(f330,plain,
    ( spl11_33
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f196,f80,f327])).

fof(f196,plain,
    ( r2_hidden(sK9(sK3),sK3)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f82,f51])).

fof(f313,plain,
    ( ~ spl11_32
    | spl11_13
    | spl11_20 ),
    inference(avatar_split_clause,[],[f268,f214,f148,f310])).

fof(f310,plain,
    ( spl11_32
  <=> m1_subset_1(sK2,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f214,plain,
    ( spl11_20
  <=> r2_hidden(sK2,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f268,plain,
    ( ~ m1_subset_1(sK2,sK7)
    | spl11_13
    | spl11_20 ),
    inference(unit_resulting_resolution,[],[f150,f216,f47])).

fof(f216,plain,
    ( ~ r2_hidden(sK2,sK7)
    | spl11_20 ),
    inference(avatar_component_clause,[],[f214])).

fof(f308,plain,
    ( ~ spl11_31
    | spl11_12
    | spl11_19 ),
    inference(avatar_split_clause,[],[f267,f209,f143,f305])).

fof(f305,plain,
    ( spl11_31
  <=> m1_subset_1(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f209,plain,
    ( spl11_19
  <=> r2_hidden(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f267,plain,
    ( ~ m1_subset_1(sK7,sK6)
    | spl11_12
    | spl11_19 ),
    inference(unit_resulting_resolution,[],[f145,f211,f47])).

fof(f211,plain,
    ( ~ r2_hidden(sK7,sK6)
    | spl11_19 ),
    inference(avatar_component_clause,[],[f209])).

fof(f303,plain,
    ( ~ spl11_30
    | spl11_11
    | spl11_18 ),
    inference(avatar_split_clause,[],[f266,f204,f138,f300])).

fof(f300,plain,
    ( spl11_30
  <=> m1_subset_1(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f204,plain,
    ( spl11_18
  <=> r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f266,plain,
    ( ~ m1_subset_1(sK6,sK5)
    | spl11_11
    | spl11_18 ),
    inference(unit_resulting_resolution,[],[f140,f206,f47])).

fof(f206,plain,
    ( ~ r2_hidden(sK6,sK5)
    | spl11_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f298,plain,
    ( ~ spl11_29
    | spl11_10
    | spl11_17 ),
    inference(avatar_split_clause,[],[f265,f192,f133,f295])).

fof(f295,plain,
    ( spl11_29
  <=> m1_subset_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f192,plain,
    ( spl11_17
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f265,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | spl11_10
    | spl11_17 ),
    inference(unit_resulting_resolution,[],[f135,f194,f47])).

fof(f194,plain,
    ( ~ r2_hidden(sK5,sK4)
    | spl11_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f293,plain,
    ( ~ spl11_28
    | spl11_9
    | spl11_16 ),
    inference(avatar_split_clause,[],[f264,f187,f128,f290])).

fof(f290,plain,
    ( spl11_28
  <=> m1_subset_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f187,plain,
    ( spl11_16
  <=> r2_hidden(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f264,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | spl11_9
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f130,f189,f47])).

fof(f189,plain,
    ( ~ r2_hidden(sK4,sK3)
    | spl11_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f288,plain,
    ( ~ spl11_27
    | spl11_14
    | spl11_15 ),
    inference(avatar_split_clause,[],[f255,f182,f171,f285])).

fof(f285,plain,
    ( spl11_27
  <=> m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f182,plain,
    ( spl11_15
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f255,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl11_14
    | spl11_15 ),
    inference(unit_resulting_resolution,[],[f184,f173,f47])).

fof(f184,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl11_15 ),
    inference(avatar_component_clause,[],[f182])).

fof(f254,plain,
    ( spl11_26
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f180,f105,f251])).

fof(f251,plain,
    ( spl11_26
  <=> m1_subset_1(sK7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f180,plain,
    ( m1_subset_1(sK7,sK2)
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f107,f49])).

fof(f249,plain,
    ( spl11_25
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f179,f100,f246])).

fof(f246,plain,
    ( spl11_25
  <=> m1_subset_1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f179,plain,
    ( m1_subset_1(sK6,sK7)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f102,f49])).

fof(f244,plain,
    ( spl11_24
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f178,f95,f241])).

fof(f241,plain,
    ( spl11_24
  <=> m1_subset_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f178,plain,
    ( m1_subset_1(sK5,sK6)
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f97,f49])).

fof(f239,plain,
    ( spl11_23
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f177,f90,f236])).

fof(f236,plain,
    ( spl11_23
  <=> m1_subset_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f177,plain,
    ( m1_subset_1(sK4,sK5)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f92,f49])).

fof(f227,plain,
    ( spl11_22
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f176,f85,f224])).

fof(f224,plain,
    ( spl11_22
  <=> m1_subset_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f176,plain,
    ( m1_subset_1(sK3,sK4)
    | ~ spl11_3 ),
    inference(unit_resulting_resolution,[],[f87,f49])).

fof(f222,plain,
    ( spl11_21
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f175,f80,f219])).

fof(f219,plain,
    ( spl11_21
  <=> m1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f175,plain,
    ( m1_subset_1(sK2,sK3)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f82,f49])).

fof(f217,plain,
    ( ~ spl11_20
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f163,f105,f214])).

fof(f163,plain,
    ( ~ r2_hidden(sK2,sK7)
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f107,f48])).

fof(f212,plain,
    ( ~ spl11_19
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f162,f100,f209])).

fof(f162,plain,
    ( ~ r2_hidden(sK7,sK6)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f102,f48])).

fof(f207,plain,
    ( ~ spl11_18
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f161,f95,f204])).

fof(f161,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f97,f48])).

fof(f195,plain,
    ( ~ spl11_17
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f160,f90,f192])).

fof(f160,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f92,f48])).

fof(f190,plain,
    ( ~ spl11_16
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f159,f85,f187])).

fof(f159,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl11_3 ),
    inference(unit_resulting_resolution,[],[f87,f48])).

fof(f185,plain,
    ( ~ spl11_15
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f158,f80,f182])).

fof(f158,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f82,f48])).

fof(f174,plain,
    ( ~ spl11_14
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f122,f105,f171])).

fof(f122,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f107,f50])).

fof(f151,plain,
    ( ~ spl11_13
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f121,f100,f148])).

fof(f121,plain,
    ( ~ v1_xboole_0(sK7)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f102,f50])).

fof(f146,plain,
    ( ~ spl11_12
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f120,f95,f143])).

fof(f120,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f97,f50])).

fof(f141,plain,
    ( ~ spl11_11
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f119,f90,f138])).

fof(f119,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f92,f50])).

fof(f136,plain,
    ( ~ spl11_10
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f118,f85,f133])).

fof(f118,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl11_3 ),
    inference(unit_resulting_resolution,[],[f87,f50])).

fof(f131,plain,
    ( ~ spl11_9
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f117,f80,f128])).

fof(f117,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f82,f50])).

fof(f116,plain,
    ( spl11_8
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f109,f75,f113])).

fof(f109,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f77,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f108,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f43,f105])).

fof(f43,plain,(
    r2_hidden(sK7,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( r2_hidden(sK7,sK2)
    & r2_hidden(sK6,sK7)
    & r2_hidden(sK5,sK6)
    & r2_hidden(sK4,sK5)
    & r2_hidden(sK3,sK4)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( r2_hidden(X5,X0)
        & r2_hidden(X4,X5)
        & r2_hidden(X3,X4)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) )
   => ( r2_hidden(sK7,sK2)
      & r2_hidden(sK6,sK7)
      & r2_hidden(sK5,sK6)
      & r2_hidden(sK4,sK5)
      & r2_hidden(sK3,sK4)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(X5,X0)
      & r2_hidden(X4,X5)
      & r2_hidden(X3,X4)
      & r2_hidden(X2,X3)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X5,X0)
          & r2_hidden(X4,X5)
          & r2_hidden(X3,X4)
          & r2_hidden(X2,X3)
          & r2_hidden(X1,X2)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X5,X0)
        & r2_hidden(X4,X5)
        & r2_hidden(X3,X4)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_ordinal1)).

fof(f103,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    r2_hidden(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f41,f95])).

fof(f41,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f40,f90])).

fof(f40,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f38,f80])).

fof(f38,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f44,f75])).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

%------------------------------------------------------------------------------
