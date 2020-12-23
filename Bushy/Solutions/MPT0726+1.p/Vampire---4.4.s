%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t6_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:28 EDT 2019

% Result     : Theorem 9.69s
% Output     : Refutation 9.80s
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
fof(f11934,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f93,f100,f107,f114,f121,f128,f138,f155,f162,f169,f176,f183,f208,f221,f228,f235,f244,f251,f258,f265,f272,f286,f293,f300,f307,f350,f357,f364,f371,f378,f385,f404,f411,f418,f425,f432,f439,f446,f453,f460,f467,f474,f481,f532,f539,f546,f553,f560,f567,f574,f666,f673,f680,f687,f694,f708,f715,f722,f729,f736,f744,f869,f876,f883,f890,f897,f904,f965,f972,f979,f986,f1002,f1009,f1061,f1068,f1084,f1091,f1098,f1105,f2570,f11039,f11053,f11195,f11211,f11222,f11238,f11380,f11394,f11407,f11421,f11434,f11448,f11590,f11606,f11617,f11633,f11644,f11660,f11671,f11687,f11718,f11909])).

fof(f11909,plain,
    ( ~ spl11_4
    | ~ spl11_210 ),
    inference(avatar_contradiction_clause,[],[f11908])).

fof(f11908,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_210 ),
    inference(subsumption_resolution,[],[f11775,f99])).

fof(f99,plain,
    ( r2_hidden(sK3,sK4)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl11_4
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f11775,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ spl11_210 ),
    inference(superposition,[],[f911,f11717])).

fof(f11717,plain,
    ( sK4 = sK9(k4_enumset1(sK4,sK5,sK6,sK7,sK2,sK3))
    | ~ spl11_210 ),
    inference(avatar_component_clause,[],[f11716])).

fof(f11716,plain,
    ( spl11_210
  <=> sK4 = sK9(k4_enumset1(sK4,sK5,sK6,sK7,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_210])])).

fof(f911,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X2,X3,X4,X5,X0))) ),
    inference(unit_resulting_resolution,[],[f653,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK9(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK9(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f33])).

fof(f33,plain,(
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

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',t7_tarski)).

fof(f653,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X2,X3,X4,X5,X0)) ),
    inference(unit_resulting_resolution,[],[f72,f78,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6)
      | ~ sP0(X8,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X8,X6) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f36,f37])).

fof(f37,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(definition_folding,[],[f25,f27,f26])).

fof(f26,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( sP0(X7,X5,X4,X3,X2,X1,X0)
    <=> ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',d4_enumset1)).

fof(f72,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f11718,plain,
    ( spl11_210
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11692,f126,f119,f112,f105,f91,f11716])).

fof(f91,plain,
    ( spl11_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f105,plain,
    ( spl11_6
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f112,plain,
    ( spl11_8
  <=> r2_hidden(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f119,plain,
    ( spl11_10
  <=> r2_hidden(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f126,plain,
    ( spl11_12
  <=> r2_hidden(sK7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f11692,plain,
    ( sK4 = sK9(k4_enumset1(sK4,sK5,sK6,sK7,sK2,sK3))
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f106,f11486])).

fof(f11486,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,sK5)
        | sK9(k4_enumset1(X10,sK5,sK6,sK7,sK2,sK3)) = X10 )
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f1118,f11455])).

fof(f11455,plain,
    ( ! [X0] :
        ( sK5 = sK9(k4_enumset1(X0,sK5,sK6,sK7,sK2,sK3))
        | sK9(k4_enumset1(X0,sK5,sK6,sK7,sK2,sK3)) = X0 )
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(resolution,[],[f11273,f113])).

fof(f113,plain,
    ( r2_hidden(sK5,sK6)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f11273,plain,
    ( ! [X17,X16] :
        ( ~ r2_hidden(X17,sK6)
        | sK9(k4_enumset1(X16,X17,sK6,sK7,sK2,sK3)) = X16
        | sK9(k4_enumset1(X16,X17,sK6,sK7,sK2,sK3)) = X17 )
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f1075,f11243])).

fof(f11243,plain,
    ( ! [X0,X1] :
        ( sK6 = sK9(k4_enumset1(X0,X1,sK6,sK7,sK2,sK3))
        | sK9(k4_enumset1(X0,X1,sK6,sK7,sK2,sK3)) = X0
        | sK9(k4_enumset1(X0,X1,sK6,sK7,sK2,sK3)) = X1 )
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(resolution,[],[f11085,f120])).

fof(f120,plain,
    ( r2_hidden(sK6,sK7)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f11085,plain,
    ( ! [X19,X20,X18] :
        ( ~ r2_hidden(X20,sK7)
        | sK9(k4_enumset1(X18,X19,X20,sK7,sK2,sK3)) = X20
        | sK9(k4_enumset1(X18,X19,X20,sK7,sK2,sK3)) = X18
        | sK9(k4_enumset1(X18,X19,X20,sK7,sK2,sK3)) = X19 )
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(superposition,[],[f1034,f11060])).

fof(f11060,plain,
    ( ! [X2,X0,X1] :
        ( sK7 = sK9(k4_enumset1(X0,X1,X2,sK7,sK2,sK3))
        | sK9(k4_enumset1(X0,X1,X2,sK7,sK2,sK3)) = X2
        | sK9(k4_enumset1(X0,X1,X2,sK7,sK2,sK3)) = X0
        | sK9(k4_enumset1(X0,X1,X2,sK7,sK2,sK3)) = X1 )
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(resolution,[],[f10926,f127])).

fof(f127,plain,
    ( r2_hidden(sK7,sK2)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f10926,plain,
    ( ! [X19,X17,X18,X16] :
        ( ~ r2_hidden(X19,sK2)
        | sK9(k4_enumset1(X16,X17,X18,X19,sK2,sK3)) = X16
        | sK9(k4_enumset1(X16,X17,X18,X19,sK2,sK3)) = X18
        | sK9(k4_enumset1(X16,X17,X18,X19,sK2,sK3)) = X19
        | sK9(k4_enumset1(X16,X17,X18,X19,sK2,sK3)) = X17 )
    | ~ spl11_2 ),
    inference(superposition,[],[f993,f7018])).

fof(f7018,plain,
    ( ! [X74,X72,X71,X73] :
        ( sK2 = sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3))
        | sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3)) = X71
        | sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3)) = X73
        | sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3)) = X74
        | sK9(k4_enumset1(X71,X72,X73,X74,sK2,sK3)) = X72 )
    | ~ spl11_2 ),
    inference(resolution,[],[f1893,f92])).

fof(f92,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f1893,plain,(
    ! [X23,X21,X19,X22,X20,X18] :
      ( ~ r2_hidden(X22,X23)
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X19
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X18
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X20
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X21
      | sK9(k4_enumset1(X18,X19,X20,X21,X22,X23)) = X22 ) ),
    inference(superposition,[],[f950,f1407])).

fof(f1407,plain,(
    ! [X54,X52,X50,X53,X51,X49] :
      ( sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X54
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X50
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X49
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X51
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X52
      | sK9(k4_enumset1(X49,X50,X51,X52,X53,X54)) = X53 ) ),
    inference(resolution,[],[f1166,f909])).

fof(f909,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(sK9(k4_enumset1(X0,X1,X2,X3,X4,X5)),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f653,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1166,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,k4_enumset1(X4,X3,X2,X1,X6,X5))
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X1
      | X0 = X6 ) ),
    inference(resolution,[],[f701,f78])).

fof(f701,plain,(
    ! [X39,X37,X43,X41,X38,X36,X42,X40] :
      ( ~ sP1(X41,X40,X39,X38,X37,X42,X43)
      | X36 = X38
      | X36 = X39
      | X36 = X40
      | X36 = X41
      | X36 = X42
      | ~ r2_hidden(X36,X43)
      | X36 = X37 ) ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( sP0(X8,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X8,X6)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f950,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X2,X3,X4,X0,X5))) ),
    inference(unit_resulting_resolution,[],[f654,f79])).

fof(f654,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X2,X3,X4,X0,X5)) ),
    inference(unit_resulting_resolution,[],[f73,f78,f60])).

fof(f73,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X2,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f993,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X2,X3,X0,X4,X5))) ),
    inference(unit_resulting_resolution,[],[f655,f79])).

fof(f655,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X2,X3,X0,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f74,f78,f60])).

fof(f74,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X3,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1034,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X2,X0,X3,X4,X5))) ),
    inference(unit_resulting_resolution,[],[f656,f79])).

fof(f656,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X2,X0,X3,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f75,f78,f60])).

fof(f75,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X4,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X4 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1075,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X1,X0,X2,X3,X4,X5))) ),
    inference(unit_resulting_resolution,[],[f657,f79])).

fof(f657,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X1,X0,X2,X3,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f76,f78,f60])).

fof(f76,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X5,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X5 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1118,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ r2_hidden(X0,sK9(k4_enumset1(X0,X1,X2,X3,X4,X5))) ),
    inference(unit_resulting_resolution,[],[f658,f79])).

fof(f658,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X0,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(unit_resulting_resolution,[],[f77,f78,f60])).

fof(f77,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X6,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X6 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f11687,plain,
    ( ~ spl11_209
    | spl11_21
    | spl11_207 ),
    inference(avatar_split_clause,[],[f11678,f11669,f167,f11685])).

fof(f11685,plain,
    ( spl11_209
  <=> ~ m1_subset_1(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_209])])).

fof(f167,plain,
    ( spl11_21
  <=> ~ v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f11669,plain,
    ( spl11_207
  <=> ~ r2_hidden(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_207])])).

fof(f11678,plain,
    ( ~ m1_subset_1(sK5,sK5)
    | ~ spl11_21
    | ~ spl11_207 ),
    inference(unit_resulting_resolution,[],[f168,f11670,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',t2_subset)).

fof(f11670,plain,
    ( ~ r2_hidden(sK5,sK5)
    | ~ spl11_207 ),
    inference(avatar_component_clause,[],[f11669])).

fof(f168,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f167])).

fof(f11671,plain,
    ( spl11_192
    | ~ spl11_207
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11485,f126,f119,f112,f91,f11669,f11582])).

fof(f11582,plain,
    ( spl11_192
  <=> ! [X4] : sK9(k4_enumset1(X4,sK5,sK6,sK7,sK2,sK3)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_192])])).

fof(f11485,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK5,sK5)
        | sK9(k4_enumset1(X9,sK5,sK6,sK7,sK2,sK3)) = X9 )
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f1075,f11455])).

fof(f11660,plain,
    ( ~ spl11_205
    | spl11_21
    | spl11_203 ),
    inference(avatar_split_clause,[],[f11651,f11642,f167,f11658])).

fof(f11658,plain,
    ( spl11_205
  <=> ~ m1_subset_1(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_205])])).

fof(f11642,plain,
    ( spl11_203
  <=> ~ r2_hidden(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_203])])).

fof(f11651,plain,
    ( ~ m1_subset_1(sK7,sK5)
    | ~ spl11_21
    | ~ spl11_203 ),
    inference(unit_resulting_resolution,[],[f168,f11643,f52])).

fof(f11643,plain,
    ( ~ r2_hidden(sK7,sK5)
    | ~ spl11_203 ),
    inference(avatar_component_clause,[],[f11642])).

fof(f11644,plain,
    ( spl11_192
    | ~ spl11_203
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11483,f126,f119,f112,f91,f11642,f11582])).

fof(f11483,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK7,sK5)
        | sK9(k4_enumset1(X7,sK5,sK6,sK7,sK2,sK3)) = X7 )
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f993,f11455])).

fof(f11633,plain,
    ( ~ spl11_201
    | spl11_21
    | spl11_199 ),
    inference(avatar_split_clause,[],[f11624,f11615,f167,f11631])).

fof(f11631,plain,
    ( spl11_201
  <=> ~ m1_subset_1(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_201])])).

fof(f11615,plain,
    ( spl11_199
  <=> ~ r2_hidden(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_199])])).

fof(f11624,plain,
    ( ~ m1_subset_1(sK2,sK5)
    | ~ spl11_21
    | ~ spl11_199 ),
    inference(unit_resulting_resolution,[],[f168,f11616,f52])).

fof(f11616,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ spl11_199 ),
    inference(avatar_component_clause,[],[f11615])).

fof(f11617,plain,
    ( spl11_192
    | ~ spl11_199
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11482,f126,f119,f112,f91,f11615,f11582])).

fof(f11482,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK2,sK5)
        | sK9(k4_enumset1(X6,sK5,sK6,sK7,sK2,sK3)) = X6 )
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f950,f11455])).

fof(f11606,plain,
    ( ~ spl11_197
    | spl11_21
    | spl11_195 ),
    inference(avatar_split_clause,[],[f11597,f11588,f167,f11604])).

fof(f11604,plain,
    ( spl11_197
  <=> ~ m1_subset_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_197])])).

fof(f11588,plain,
    ( spl11_195
  <=> ~ r2_hidden(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_195])])).

fof(f11597,plain,
    ( ~ m1_subset_1(sK3,sK5)
    | ~ spl11_21
    | ~ spl11_195 ),
    inference(unit_resulting_resolution,[],[f168,f11589,f52])).

fof(f11589,plain,
    ( ~ r2_hidden(sK3,sK5)
    | ~ spl11_195 ),
    inference(avatar_component_clause,[],[f11588])).

fof(f11590,plain,
    ( spl11_192
    | ~ spl11_195
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11480,f126,f119,f112,f91,f11588,f11582])).

fof(f11480,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK3,sK5)
        | sK9(k4_enumset1(X4,sK5,sK6,sK7,sK2,sK3)) = X4 )
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f911,f11455])).

fof(f11448,plain,
    ( ~ spl11_191
    | spl11_23
    | spl11_189 ),
    inference(avatar_split_clause,[],[f11441,f11432,f174,f11446])).

fof(f11446,plain,
    ( spl11_191
  <=> ~ m1_subset_1(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_191])])).

fof(f174,plain,
    ( spl11_23
  <=> ~ v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f11432,plain,
    ( spl11_189
  <=> ~ r2_hidden(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_189])])).

fof(f11441,plain,
    ( ~ m1_subset_1(sK6,sK6)
    | ~ spl11_23
    | ~ spl11_189 ),
    inference(unit_resulting_resolution,[],[f175,f11433,f52])).

fof(f11433,plain,
    ( ~ r2_hidden(sK6,sK6)
    | ~ spl11_189 ),
    inference(avatar_component_clause,[],[f11432])).

fof(f175,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f174])).

fof(f11434,plain,
    ( spl11_178
    | ~ spl11_189
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11272,f126,f119,f91,f11432,f11372])).

fof(f11372,plain,
    ( spl11_178
  <=> ! [X7,X6] :
        ( sK9(k4_enumset1(X6,X7,sK6,sK7,sK2,sK3)) = X6
        | sK9(k4_enumset1(X6,X7,sK6,sK7,sK2,sK3)) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_178])])).

fof(f11272,plain,
    ( ! [X14,X15] :
        ( ~ r2_hidden(sK6,sK6)
        | sK9(k4_enumset1(X14,X15,sK6,sK7,sK2,sK3)) = X14
        | sK9(k4_enumset1(X14,X15,sK6,sK7,sK2,sK3)) = X15 )
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f1034,f11243])).

fof(f11421,plain,
    ( ~ spl11_187
    | spl11_23
    | spl11_185 ),
    inference(avatar_split_clause,[],[f11414,f11405,f174,f11419])).

fof(f11419,plain,
    ( spl11_187
  <=> ~ m1_subset_1(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_187])])).

fof(f11405,plain,
    ( spl11_185
  <=> ~ r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_185])])).

fof(f11414,plain,
    ( ~ m1_subset_1(sK2,sK6)
    | ~ spl11_23
    | ~ spl11_185 ),
    inference(unit_resulting_resolution,[],[f175,f11406,f52])).

fof(f11406,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ spl11_185 ),
    inference(avatar_component_clause,[],[f11405])).

fof(f11407,plain,
    ( spl11_178
    | ~ spl11_185
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11270,f126,f119,f91,f11405,f11372])).

fof(f11270,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(sK2,sK6)
        | sK9(k4_enumset1(X10,X11,sK6,sK7,sK2,sK3)) = X10
        | sK9(k4_enumset1(X10,X11,sK6,sK7,sK2,sK3)) = X11 )
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f950,f11243])).

fof(f11394,plain,
    ( ~ spl11_183
    | spl11_23
    | spl11_181 ),
    inference(avatar_split_clause,[],[f11387,f11378,f174,f11392])).

fof(f11392,plain,
    ( spl11_183
  <=> ~ m1_subset_1(sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_183])])).

fof(f11378,plain,
    ( spl11_181
  <=> ~ r2_hidden(sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_181])])).

fof(f11387,plain,
    ( ~ m1_subset_1(sK3,sK6)
    | ~ spl11_23
    | ~ spl11_181 ),
    inference(unit_resulting_resolution,[],[f175,f11379,f52])).

fof(f11379,plain,
    ( ~ r2_hidden(sK3,sK6)
    | ~ spl11_181 ),
    inference(avatar_component_clause,[],[f11378])).

fof(f11380,plain,
    ( spl11_178
    | ~ spl11_181
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11268,f126,f119,f91,f11378,f11372])).

fof(f11268,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(sK3,sK6)
        | sK9(k4_enumset1(X6,X7,sK6,sK7,sK2,sK3)) = X6
        | sK9(k4_enumset1(X6,X7,sK6,sK7,sK2,sK3)) = X7 )
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(superposition,[],[f911,f11243])).

fof(f11238,plain,
    ( ~ spl11_177
    | spl11_25
    | spl11_175 ),
    inference(avatar_split_clause,[],[f11231,f11220,f181,f11236])).

fof(f11236,plain,
    ( spl11_177
  <=> ~ m1_subset_1(sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_177])])).

fof(f181,plain,
    ( spl11_25
  <=> ~ v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f11220,plain,
    ( spl11_175
  <=> ~ r2_hidden(sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_175])])).

fof(f11231,plain,
    ( ~ m1_subset_1(sK7,sK7)
    | ~ spl11_25
    | ~ spl11_175 ),
    inference(unit_resulting_resolution,[],[f182,f11221,f52])).

fof(f11221,plain,
    ( ~ r2_hidden(sK7,sK7)
    | ~ spl11_175 ),
    inference(avatar_component_clause,[],[f11220])).

fof(f182,plain,
    ( ~ v1_xboole_0(sK7)
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f11222,plain,
    ( spl11_168
    | ~ spl11_175
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11084,f126,f91,f11220,f11187])).

fof(f11187,plain,
    ( spl11_168
  <=> ! [X7,X8,X6] :
        ( sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X8
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X7
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_168])])).

fof(f11084,plain,
    ( ! [X17,X15,X16] :
        ( ~ r2_hidden(sK7,sK7)
        | sK9(k4_enumset1(X15,X16,X17,sK7,sK2,sK3)) = X17
        | sK9(k4_enumset1(X15,X16,X17,sK7,sK2,sK3)) = X15
        | sK9(k4_enumset1(X15,X16,X17,sK7,sK2,sK3)) = X16 )
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(superposition,[],[f993,f11060])).

fof(f11211,plain,
    ( ~ spl11_173
    | spl11_25
    | spl11_171 ),
    inference(avatar_split_clause,[],[f11204,f11193,f181,f11209])).

fof(f11209,plain,
    ( spl11_173
  <=> ~ m1_subset_1(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_173])])).

fof(f11193,plain,
    ( spl11_171
  <=> ~ r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_171])])).

fof(f11204,plain,
    ( ~ m1_subset_1(sK3,sK7)
    | ~ spl11_25
    | ~ spl11_171 ),
    inference(unit_resulting_resolution,[],[f182,f11194,f52])).

fof(f11194,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ spl11_171 ),
    inference(avatar_component_clause,[],[f11193])).

fof(f11195,plain,
    ( spl11_168
    | ~ spl11_171
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11081,f126,f91,f11193,f11187])).

fof(f11081,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(sK3,sK7)
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X8
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X6
        | sK9(k4_enumset1(X6,X7,X8,sK7,sK2,sK3)) = X7 )
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(superposition,[],[f911,f11060])).

fof(f11053,plain,
    ( ~ spl11_167
    | spl11_27
    | spl11_165 ),
    inference(avatar_split_clause,[],[f11046,f11037,f206,f11051])).

fof(f11051,plain,
    ( spl11_167
  <=> ~ m1_subset_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_167])])).

fof(f206,plain,
    ( spl11_27
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f11037,plain,
    ( spl11_165
  <=> ~ r2_hidden(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_165])])).

fof(f11046,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | ~ spl11_27
    | ~ spl11_165 ),
    inference(unit_resulting_resolution,[],[f207,f11038,f52])).

fof(f11038,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ spl11_165 ),
    inference(avatar_component_clause,[],[f11037])).

fof(f207,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f206])).

fof(f11039,plain,
    ( spl11_162
    | ~ spl11_165
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f10925,f91,f11037,f11031])).

fof(f11031,plain,
    ( spl11_162
  <=> ! [X13,X15,X12,X14] :
        ( sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X12
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X13
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X15
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_162])])).

fof(f10925,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ r2_hidden(sK2,sK2)
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X12
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X14
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X15
        | sK9(k4_enumset1(X12,X13,X14,X15,sK2,sK3)) = X13 )
    | ~ spl11_2 ),
    inference(superposition,[],[f950,f7018])).

fof(f2570,plain,
    ( spl11_160
    | ~ spl11_0
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f2476,f136,f84,f2568])).

fof(f2568,plain,
    ( spl11_160
  <=> o_0_0_xboole_0 = sK10(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_160])])).

fof(f84,plain,
    ( spl11_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f136,plain,
    ( spl11_14
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f2476,plain,
    ( o_0_0_xboole_0 = sK10(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl11_0
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f2474,f137])).

fof(f137,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f2474,plain,
    ( k1_xboole_0 = sK10(k1_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl11_0
    | ~ spl11_14 ),
    inference(unit_resulting_resolution,[],[f137,f2450])).

fof(f2450,plain,
    ( ! [X0,X1] :
        ( X0 != X1
        | sK10(X0,X1,X1,X1,X1,X1,o_0_0_xboole_0) = X0 )
    | ~ spl11_0 ),
    inference(equality_factoring,[],[f2412])).

fof(f2412,plain,
    ( ! [X0,X1] :
        ( sK10(X0,X1,X1,X1,X1,X1,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X1,X1,X1,X1,o_0_0_xboole_0) = X0 )
    | ~ spl11_0 ),
    inference(equality_resolution,[],[f2389])).

fof(f2389,plain,
    ( ! [X2,X0,X1] :
        ( X1 != X2
        | sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X0 )
    | ~ spl11_0 ),
    inference(equality_factoring,[],[f2351])).

fof(f2351,plain,
    ( ! [X2,X0,X1] :
        ( sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X2
        | sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X2,X2,X2,X2,o_0_0_xboole_0) = X0 )
    | ~ spl11_0 ),
    inference(equality_resolution,[],[f2323])).

fof(f2323,plain,
    ( ! [X2,X0,X3,X1] :
        ( X2 != X3
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X2
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X0 )
    | ~ spl11_0 ),
    inference(equality_factoring,[],[f2285])).

fof(f2285,plain,
    ( ! [X2,X0,X3,X1] :
        ( sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X3
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X2
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X1
        | sK10(X0,X1,X2,X3,X3,X3,o_0_0_xboole_0) = X0 )
    | ~ spl11_0 ),
    inference(equality_resolution,[],[f2284])).

fof(f2284,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( X0 != X1
        | sK10(X2,X3,X4,X0,X0,X1,o_0_0_xboole_0) = X0
        | sK10(X2,X3,X4,X0,X0,X1,o_0_0_xboole_0) = X4
        | sK10(X2,X3,X4,X0,X0,X1,o_0_0_xboole_0) = X3
        | sK10(X2,X3,X4,X0,X0,X1,o_0_0_xboole_0) = X2 )
    | ~ spl11_0 ),
    inference(equality_resolution,[],[f2105])).

fof(f2105,plain,
    ( ! [X30,X28,X26,X31,X29,X27] :
        ( X26 != X27
        | X27 != X28
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X26
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X31
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X30
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X29 )
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f2096,f640])).

fof(f640,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : ~ sP1(X0,X1,X2,X3,X4,X5,o_0_0_xboole_0)
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f145,f77,f60])).

fof(f145,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f85,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',t7_boole)).

fof(f85,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f84])).

fof(f2096,plain,
    ( ! [X30,X28,X26,X31,X29,X27] :
        ( X26 != X27
        | X27 != X28
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X26
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X31
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X30
        | sK10(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) = X29
        | sP1(X29,X30,X31,X26,X27,X28,o_0_0_xboole_0) )
    | ~ spl11_0 ),
    inference(resolution,[],[f1437,f145])).

fof(f1437,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6)
      | X3 != X4
      | X4 != X5
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X3
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X2
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X1
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X0
      | sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(equality_factoring,[],[f1169])).

fof(f1169,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sK10(X0,X1,X2,X3,X4,X5,X6) = X4
      | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6)
      | X4 != X5
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X3
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X2
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X1
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X0
      | sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(equality_factoring,[],[f737])).

fof(f737,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sK10(X0,X1,X2,X3,X4,X5,X6) = X5
      | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6)
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X4
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X3
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X2
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X1
      | sK10(X0,X1,X2,X3,X4,X5,X6) = X0
      | sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(resolution,[],[f61,f63])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(sK10(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
      | sP1(X0,X1,X2,X3,X4,X5,X6)
      | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6),X6) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1105,plain,
    ( ~ spl11_159
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f785,f565,f1103])).

fof(f1103,plain,
    ( spl11_159
  <=> ~ r2_hidden(sK8(sK7),sK9(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_159])])).

fof(f565,plain,
    ( spl11_98
  <=> r2_hidden(sK8(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_98])])).

fof(f785,plain,
    ( ~ r2_hidden(sK8(sK7),sK9(sK7))
    | ~ spl11_98 ),
    inference(unit_resulting_resolution,[],[f566,f79])).

fof(f566,plain,
    ( r2_hidden(sK8(sK7),sK7)
    | ~ spl11_98 ),
    inference(avatar_component_clause,[],[f565])).

fof(f1098,plain,
    ( ~ spl11_157
    | ~ spl11_96 ),
    inference(avatar_split_clause,[],[f778,f558,f1096])).

fof(f1096,plain,
    ( spl11_157
  <=> ~ r2_hidden(sK8(sK6),sK9(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_157])])).

fof(f558,plain,
    ( spl11_96
  <=> r2_hidden(sK8(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_96])])).

fof(f778,plain,
    ( ~ r2_hidden(sK8(sK6),sK9(sK6))
    | ~ spl11_96 ),
    inference(unit_resulting_resolution,[],[f559,f79])).

fof(f559,plain,
    ( r2_hidden(sK8(sK6),sK6)
    | ~ spl11_96 ),
    inference(avatar_component_clause,[],[f558])).

fof(f1091,plain,
    ( ~ spl11_155
    | ~ spl11_94 ),
    inference(avatar_split_clause,[],[f771,f551,f1089])).

fof(f1089,plain,
    ( spl11_155
  <=> ~ r2_hidden(sK8(sK5),sK9(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_155])])).

fof(f551,plain,
    ( spl11_94
  <=> r2_hidden(sK8(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f771,plain,
    ( ~ r2_hidden(sK8(sK5),sK9(sK5))
    | ~ spl11_94 ),
    inference(unit_resulting_resolution,[],[f552,f79])).

fof(f552,plain,
    ( r2_hidden(sK8(sK5),sK5)
    | ~ spl11_94 ),
    inference(avatar_component_clause,[],[f551])).

fof(f1084,plain,
    ( ~ spl11_153
    | ~ spl11_92 ),
    inference(avatar_split_clause,[],[f764,f544,f1082])).

fof(f1082,plain,
    ( spl11_153
  <=> ~ r2_hidden(sK8(sK4),sK9(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_153])])).

fof(f544,plain,
    ( spl11_92
  <=> r2_hidden(sK8(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f764,plain,
    ( ~ r2_hidden(sK8(sK4),sK9(sK4))
    | ~ spl11_92 ),
    inference(unit_resulting_resolution,[],[f545,f79])).

fof(f545,plain,
    ( r2_hidden(sK8(sK4),sK4)
    | ~ spl11_92 ),
    inference(avatar_component_clause,[],[f544])).

fof(f1068,plain,
    ( ~ spl11_151
    | ~ spl11_90 ),
    inference(avatar_split_clause,[],[f757,f537,f1066])).

fof(f1066,plain,
    ( spl11_151
  <=> ~ r2_hidden(sK8(sK3),sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_151])])).

fof(f537,plain,
    ( spl11_90
  <=> r2_hidden(sK8(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f757,plain,
    ( ~ r2_hidden(sK8(sK3),sK9(sK3))
    | ~ spl11_90 ),
    inference(unit_resulting_resolution,[],[f538,f79])).

fof(f538,plain,
    ( r2_hidden(sK8(sK3),sK3)
    | ~ spl11_90 ),
    inference(avatar_component_clause,[],[f537])).

fof(f1061,plain,
    ( ~ spl11_149
    | ~ spl11_88 ),
    inference(avatar_split_clause,[],[f750,f530,f1059])).

fof(f1059,plain,
    ( spl11_149
  <=> ~ r2_hidden(sK8(sK2),sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_149])])).

fof(f530,plain,
    ( spl11_88
  <=> r2_hidden(sK8(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f750,plain,
    ( ~ r2_hidden(sK8(sK2),sK9(sK2))
    | ~ spl11_88 ),
    inference(unit_resulting_resolution,[],[f531,f79])).

fof(f531,plain,
    ( r2_hidden(sK8(sK2),sK2)
    | ~ spl11_88 ),
    inference(avatar_component_clause,[],[f530])).

fof(f1009,plain,
    ( ~ spl11_147
    | ~ spl11_74 ),
    inference(avatar_split_clause,[],[f517,f437,f1007])).

fof(f1007,plain,
    ( spl11_147
  <=> ~ r2_hidden(sK9(sK2),sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_147])])).

fof(f437,plain,
    ( spl11_74
  <=> r2_hidden(sK9(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f517,plain,
    ( ~ r2_hidden(sK9(sK2),sK9(sK2))
    | ~ spl11_74 ),
    inference(unit_resulting_resolution,[],[f438,f79])).

fof(f438,plain,
    ( r2_hidden(sK9(sK2),sK2)
    | ~ spl11_74 ),
    inference(avatar_component_clause,[],[f437])).

fof(f1002,plain,
    ( ~ spl11_145
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f510,f430,f1000])).

fof(f1000,plain,
    ( spl11_145
  <=> ~ r2_hidden(sK9(sK7),sK9(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_145])])).

fof(f430,plain,
    ( spl11_72
  <=> r2_hidden(sK9(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f510,plain,
    ( ~ r2_hidden(sK9(sK7),sK9(sK7))
    | ~ spl11_72 ),
    inference(unit_resulting_resolution,[],[f431,f79])).

fof(f431,plain,
    ( r2_hidden(sK9(sK7),sK7)
    | ~ spl11_72 ),
    inference(avatar_component_clause,[],[f430])).

fof(f986,plain,
    ( ~ spl11_143
    | ~ spl11_70 ),
    inference(avatar_split_clause,[],[f503,f423,f984])).

fof(f984,plain,
    ( spl11_143
  <=> ~ r2_hidden(sK9(sK6),sK9(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_143])])).

fof(f423,plain,
    ( spl11_70
  <=> r2_hidden(sK9(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f503,plain,
    ( ~ r2_hidden(sK9(sK6),sK9(sK6))
    | ~ spl11_70 ),
    inference(unit_resulting_resolution,[],[f424,f79])).

fof(f424,plain,
    ( r2_hidden(sK9(sK6),sK6)
    | ~ spl11_70 ),
    inference(avatar_component_clause,[],[f423])).

fof(f979,plain,
    ( ~ spl11_141
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f496,f416,f977])).

fof(f977,plain,
    ( spl11_141
  <=> ~ r2_hidden(sK9(sK5),sK9(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_141])])).

fof(f416,plain,
    ( spl11_68
  <=> r2_hidden(sK9(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f496,plain,
    ( ~ r2_hidden(sK9(sK5),sK9(sK5))
    | ~ spl11_68 ),
    inference(unit_resulting_resolution,[],[f417,f79])).

fof(f417,plain,
    ( r2_hidden(sK9(sK5),sK5)
    | ~ spl11_68 ),
    inference(avatar_component_clause,[],[f416])).

fof(f972,plain,
    ( ~ spl11_139
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f489,f409,f970])).

fof(f970,plain,
    ( spl11_139
  <=> ~ r2_hidden(sK9(sK4),sK9(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_139])])).

fof(f409,plain,
    ( spl11_66
  <=> r2_hidden(sK9(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f489,plain,
    ( ~ r2_hidden(sK9(sK4),sK9(sK4))
    | ~ spl11_66 ),
    inference(unit_resulting_resolution,[],[f410,f79])).

fof(f410,plain,
    ( r2_hidden(sK9(sK4),sK4)
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f409])).

fof(f965,plain,
    ( ~ spl11_137
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f482,f402,f963])).

fof(f963,plain,
    ( spl11_137
  <=> ~ r2_hidden(sK9(sK3),sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_137])])).

fof(f402,plain,
    ( spl11_64
  <=> r2_hidden(sK9(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f482,plain,
    ( ~ r2_hidden(sK9(sK3),sK9(sK3))
    | ~ spl11_64 ),
    inference(unit_resulting_resolution,[],[f403,f79])).

fof(f403,plain,
    ( r2_hidden(sK9(sK3),sK3)
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f402])).

fof(f904,plain,
    ( ~ spl11_135
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f781,f565,f902])).

fof(f902,plain,
    ( spl11_135
  <=> ~ r2_hidden(sK7,sK8(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_135])])).

fof(f781,plain,
    ( ~ r2_hidden(sK7,sK8(sK7))
    | ~ spl11_98 ),
    inference(unit_resulting_resolution,[],[f566,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',antisymmetry_r2_hidden)).

fof(f897,plain,
    ( ~ spl11_133
    | ~ spl11_96 ),
    inference(avatar_split_clause,[],[f774,f558,f895])).

fof(f895,plain,
    ( spl11_133
  <=> ~ r2_hidden(sK6,sK8(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_133])])).

fof(f774,plain,
    ( ~ r2_hidden(sK6,sK8(sK6))
    | ~ spl11_96 ),
    inference(unit_resulting_resolution,[],[f559,f53])).

fof(f890,plain,
    ( ~ spl11_131
    | ~ spl11_94 ),
    inference(avatar_split_clause,[],[f767,f551,f888])).

fof(f888,plain,
    ( spl11_131
  <=> ~ r2_hidden(sK5,sK8(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_131])])).

fof(f767,plain,
    ( ~ r2_hidden(sK5,sK8(sK5))
    | ~ spl11_94 ),
    inference(unit_resulting_resolution,[],[f552,f53])).

fof(f883,plain,
    ( ~ spl11_129
    | ~ spl11_92 ),
    inference(avatar_split_clause,[],[f760,f544,f881])).

fof(f881,plain,
    ( spl11_129
  <=> ~ r2_hidden(sK4,sK8(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_129])])).

fof(f760,plain,
    ( ~ r2_hidden(sK4,sK8(sK4))
    | ~ spl11_92 ),
    inference(unit_resulting_resolution,[],[f545,f53])).

fof(f876,plain,
    ( ~ spl11_127
    | ~ spl11_90 ),
    inference(avatar_split_clause,[],[f753,f537,f874])).

fof(f874,plain,
    ( spl11_127
  <=> ~ r2_hidden(sK3,sK8(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_127])])).

fof(f753,plain,
    ( ~ r2_hidden(sK3,sK8(sK3))
    | ~ spl11_90 ),
    inference(unit_resulting_resolution,[],[f538,f53])).

fof(f869,plain,
    ( ~ spl11_125
    | ~ spl11_88 ),
    inference(avatar_split_clause,[],[f746,f530,f867])).

fof(f867,plain,
    ( spl11_125
  <=> ~ r2_hidden(sK2,sK8(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_125])])).

fof(f746,plain,
    ( ~ r2_hidden(sK2,sK8(sK2))
    | ~ spl11_88 ),
    inference(unit_resulting_resolution,[],[f531,f53])).

fof(f744,plain,
    ( ~ spl11_123
    | ~ spl11_74 ),
    inference(avatar_split_clause,[],[f521,f437,f742])).

fof(f742,plain,
    ( spl11_123
  <=> ~ r2_hidden(sK2,sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_123])])).

fof(f521,plain,
    ( ~ r2_hidden(sK2,sK9(sK2))
    | ~ spl11_74 ),
    inference(unit_resulting_resolution,[],[f438,f53])).

fof(f736,plain,
    ( spl11_120
    | ~ spl11_74 ),
    inference(avatar_split_clause,[],[f519,f437,f734])).

fof(f734,plain,
    ( spl11_120
  <=> m1_subset_1(sK9(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_120])])).

fof(f519,plain,
    ( m1_subset_1(sK9(sK2),sK2)
    | ~ spl11_74 ),
    inference(unit_resulting_resolution,[],[f438,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',t1_subset)).

fof(f729,plain,
    ( ~ spl11_119
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f514,f430,f727])).

fof(f727,plain,
    ( spl11_119
  <=> ~ r2_hidden(sK7,sK9(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_119])])).

fof(f514,plain,
    ( ~ r2_hidden(sK7,sK9(sK7))
    | ~ spl11_72 ),
    inference(unit_resulting_resolution,[],[f431,f53])).

fof(f722,plain,
    ( spl11_116
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f512,f430,f720])).

fof(f720,plain,
    ( spl11_116
  <=> m1_subset_1(sK9(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_116])])).

fof(f512,plain,
    ( m1_subset_1(sK9(sK7),sK7)
    | ~ spl11_72 ),
    inference(unit_resulting_resolution,[],[f431,f54])).

fof(f715,plain,
    ( ~ spl11_115
    | ~ spl11_70 ),
    inference(avatar_split_clause,[],[f507,f423,f713])).

fof(f713,plain,
    ( spl11_115
  <=> ~ r2_hidden(sK6,sK9(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_115])])).

fof(f507,plain,
    ( ~ r2_hidden(sK6,sK9(sK6))
    | ~ spl11_70 ),
    inference(unit_resulting_resolution,[],[f424,f53])).

fof(f708,plain,
    ( spl11_112
    | ~ spl11_70 ),
    inference(avatar_split_clause,[],[f505,f423,f706])).

fof(f706,plain,
    ( spl11_112
  <=> m1_subset_1(sK9(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_112])])).

fof(f505,plain,
    ( m1_subset_1(sK9(sK6),sK6)
    | ~ spl11_70 ),
    inference(unit_resulting_resolution,[],[f424,f54])).

fof(f694,plain,
    ( ~ spl11_111
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f500,f416,f692])).

fof(f692,plain,
    ( spl11_111
  <=> ~ r2_hidden(sK5,sK9(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_111])])).

fof(f500,plain,
    ( ~ r2_hidden(sK5,sK9(sK5))
    | ~ spl11_68 ),
    inference(unit_resulting_resolution,[],[f417,f53])).

fof(f687,plain,
    ( spl11_108
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f498,f416,f685])).

fof(f685,plain,
    ( spl11_108
  <=> m1_subset_1(sK9(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_108])])).

fof(f498,plain,
    ( m1_subset_1(sK9(sK5),sK5)
    | ~ spl11_68 ),
    inference(unit_resulting_resolution,[],[f417,f54])).

fof(f680,plain,
    ( ~ spl11_107
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f493,f409,f678])).

fof(f678,plain,
    ( spl11_107
  <=> ~ r2_hidden(sK4,sK9(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).

fof(f493,plain,
    ( ~ r2_hidden(sK4,sK9(sK4))
    | ~ spl11_66 ),
    inference(unit_resulting_resolution,[],[f410,f53])).

fof(f673,plain,
    ( spl11_104
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f491,f409,f671])).

fof(f671,plain,
    ( spl11_104
  <=> m1_subset_1(sK9(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_104])])).

fof(f491,plain,
    ( m1_subset_1(sK9(sK4),sK4)
    | ~ spl11_66 ),
    inference(unit_resulting_resolution,[],[f410,f54])).

fof(f666,plain,
    ( ~ spl11_103
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f486,f402,f664])).

fof(f664,plain,
    ( spl11_103
  <=> ~ r2_hidden(sK3,sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).

fof(f486,plain,
    ( ~ r2_hidden(sK3,sK9(sK3))
    | ~ spl11_64 ),
    inference(unit_resulting_resolution,[],[f403,f53])).

fof(f574,plain,
    ( spl11_100
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f484,f402,f572])).

fof(f572,plain,
    ( spl11_100
  <=> m1_subset_1(sK9(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f484,plain,
    ( m1_subset_1(sK9(sK3),sK3)
    | ~ spl11_64 ),
    inference(unit_resulting_resolution,[],[f403,f54])).

fof(f567,plain,
    ( spl11_98
    | spl11_25 ),
    inference(avatar_split_clause,[],[f326,f181,f565])).

fof(f326,plain,
    ( r2_hidden(sK8(sK7),sK7)
    | ~ spl11_25 ),
    inference(unit_resulting_resolution,[],[f182,f51,f52])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f9,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',existence_m1_subset_1)).

fof(f560,plain,
    ( spl11_96
    | spl11_23 ),
    inference(avatar_split_clause,[],[f325,f174,f558])).

fof(f325,plain,
    ( r2_hidden(sK8(sK6),sK6)
    | ~ spl11_23 ),
    inference(unit_resulting_resolution,[],[f175,f51,f52])).

fof(f553,plain,
    ( spl11_94
    | spl11_21 ),
    inference(avatar_split_clause,[],[f324,f167,f551])).

fof(f324,plain,
    ( r2_hidden(sK8(sK5),sK5)
    | ~ spl11_21 ),
    inference(unit_resulting_resolution,[],[f168,f51,f52])).

fof(f546,plain,
    ( spl11_92
    | spl11_19 ),
    inference(avatar_split_clause,[],[f323,f160,f544])).

fof(f160,plain,
    ( spl11_19
  <=> ~ v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f323,plain,
    ( r2_hidden(sK8(sK4),sK4)
    | ~ spl11_19 ),
    inference(unit_resulting_resolution,[],[f161,f51,f52])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f539,plain,
    ( spl11_90
    | spl11_17 ),
    inference(avatar_split_clause,[],[f322,f153,f537])).

fof(f153,plain,
    ( spl11_17
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f322,plain,
    ( r2_hidden(sK8(sK3),sK3)
    | ~ spl11_17 ),
    inference(unit_resulting_resolution,[],[f154,f51,f52])).

fof(f154,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f532,plain,
    ( spl11_88
    | spl11_27 ),
    inference(avatar_split_clause,[],[f321,f206,f530])).

fof(f321,plain,
    ( r2_hidden(sK8(sK2),sK2)
    | ~ spl11_27 ),
    inference(unit_resulting_resolution,[],[f207,f51,f52])).

fof(f481,plain,
    ( ~ spl11_87
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f313,f126,f479])).

fof(f479,plain,
    ( spl11_87
  <=> ~ r2_hidden(sK7,sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f313,plain,
    ( ~ r2_hidden(sK7,sK9(sK2))
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f127,f79])).

fof(f474,plain,
    ( ~ spl11_85
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f312,f119,f472])).

fof(f472,plain,
    ( spl11_85
  <=> ~ r2_hidden(sK6,sK9(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_85])])).

fof(f312,plain,
    ( ~ r2_hidden(sK6,sK9(sK7))
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f120,f79])).

fof(f467,plain,
    ( ~ spl11_83
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f311,f112,f465])).

fof(f465,plain,
    ( spl11_83
  <=> ~ r2_hidden(sK5,sK9(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_83])])).

fof(f311,plain,
    ( ~ r2_hidden(sK5,sK9(sK6))
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f113,f79])).

fof(f460,plain,
    ( ~ spl11_81
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f310,f105,f458])).

fof(f458,plain,
    ( spl11_81
  <=> ~ r2_hidden(sK4,sK9(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_81])])).

fof(f310,plain,
    ( ~ r2_hidden(sK4,sK9(sK5))
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f106,f79])).

fof(f453,plain,
    ( ~ spl11_79
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f309,f98,f451])).

fof(f451,plain,
    ( spl11_79
  <=> ~ r2_hidden(sK3,sK9(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).

fof(f309,plain,
    ( ~ r2_hidden(sK3,sK9(sK4))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f99,f79])).

fof(f446,plain,
    ( ~ spl11_77
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f308,f91,f444])).

fof(f444,plain,
    ( spl11_77
  <=> ~ r2_hidden(sK2,sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_77])])).

fof(f308,plain,
    ( ~ r2_hidden(sK2,sK9(sK3))
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f92,f79])).

fof(f439,plain,
    ( spl11_74
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f278,f126,f437])).

fof(f278,plain,
    ( r2_hidden(sK9(sK2),sK2)
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f127,f57])).

fof(f432,plain,
    ( spl11_72
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f277,f119,f430])).

fof(f277,plain,
    ( r2_hidden(sK9(sK7),sK7)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f120,f57])).

fof(f425,plain,
    ( spl11_70
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f276,f112,f423])).

fof(f276,plain,
    ( r2_hidden(sK9(sK6),sK6)
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f113,f57])).

fof(f418,plain,
    ( spl11_68
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f275,f105,f416])).

fof(f275,plain,
    ( r2_hidden(sK9(sK5),sK5)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f106,f57])).

fof(f411,plain,
    ( spl11_66
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f274,f98,f409])).

fof(f274,plain,
    ( r2_hidden(sK9(sK4),sK4)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f99,f57])).

fof(f404,plain,
    ( spl11_64
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f273,f91,f402])).

fof(f273,plain,
    ( r2_hidden(sK9(sK3),sK3)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f92,f57])).

fof(f385,plain,
    ( ~ spl11_63
    | spl11_25
    | spl11_39 ),
    inference(avatar_split_clause,[],[f320,f256,f181,f383])).

fof(f383,plain,
    ( spl11_63
  <=> ~ m1_subset_1(sK2,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f256,plain,
    ( spl11_39
  <=> ~ r2_hidden(sK2,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f320,plain,
    ( ~ m1_subset_1(sK2,sK7)
    | ~ spl11_25
    | ~ spl11_39 ),
    inference(unit_resulting_resolution,[],[f257,f182,f52])).

fof(f257,plain,
    ( ~ r2_hidden(sK2,sK7)
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f256])).

fof(f378,plain,
    ( ~ spl11_61
    | spl11_23
    | spl11_37 ),
    inference(avatar_split_clause,[],[f319,f249,f174,f376])).

fof(f376,plain,
    ( spl11_61
  <=> ~ m1_subset_1(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f249,plain,
    ( spl11_37
  <=> ~ r2_hidden(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f319,plain,
    ( ~ m1_subset_1(sK7,sK6)
    | ~ spl11_23
    | ~ spl11_37 ),
    inference(unit_resulting_resolution,[],[f250,f175,f52])).

fof(f250,plain,
    ( ~ r2_hidden(sK7,sK6)
    | ~ spl11_37 ),
    inference(avatar_component_clause,[],[f249])).

fof(f371,plain,
    ( ~ spl11_59
    | spl11_21
    | spl11_35 ),
    inference(avatar_split_clause,[],[f318,f242,f167,f369])).

fof(f369,plain,
    ( spl11_59
  <=> ~ m1_subset_1(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f242,plain,
    ( spl11_35
  <=> ~ r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f318,plain,
    ( ~ m1_subset_1(sK6,sK5)
    | ~ spl11_21
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f243,f168,f52])).

fof(f243,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f242])).

fof(f364,plain,
    ( ~ spl11_57
    | spl11_19
    | spl11_33 ),
    inference(avatar_split_clause,[],[f317,f233,f160,f362])).

fof(f362,plain,
    ( spl11_57
  <=> ~ m1_subset_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f233,plain,
    ( spl11_33
  <=> ~ r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f317,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | ~ spl11_19
    | ~ spl11_33 ),
    inference(unit_resulting_resolution,[],[f234,f161,f52])).

fof(f234,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f233])).

fof(f357,plain,
    ( ~ spl11_55
    | spl11_17
    | spl11_31 ),
    inference(avatar_split_clause,[],[f316,f226,f153,f355])).

fof(f355,plain,
    ( spl11_55
  <=> ~ m1_subset_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f226,plain,
    ( spl11_31
  <=> ~ r2_hidden(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f316,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | ~ spl11_17
    | ~ spl11_31 ),
    inference(unit_resulting_resolution,[],[f227,f154,f52])).

fof(f227,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f226])).

fof(f350,plain,
    ( ~ spl11_53
    | spl11_27
    | spl11_29 ),
    inference(avatar_split_clause,[],[f315,f219,f206,f348])).

fof(f348,plain,
    ( spl11_53
  <=> ~ m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f219,plain,
    ( spl11_29
  <=> ~ r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f315,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | ~ spl11_27
    | ~ spl11_29 ),
    inference(unit_resulting_resolution,[],[f220,f207,f52])).

fof(f220,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f219])).

fof(f307,plain,
    ( spl11_50
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f214,f126,f305])).

fof(f305,plain,
    ( spl11_50
  <=> m1_subset_1(sK7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f214,plain,
    ( m1_subset_1(sK7,sK2)
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f127,f54])).

fof(f300,plain,
    ( spl11_48
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f213,f119,f298])).

fof(f298,plain,
    ( spl11_48
  <=> m1_subset_1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f213,plain,
    ( m1_subset_1(sK6,sK7)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f120,f54])).

fof(f293,plain,
    ( spl11_46
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f212,f112,f291])).

fof(f291,plain,
    ( spl11_46
  <=> m1_subset_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f212,plain,
    ( m1_subset_1(sK5,sK6)
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f113,f54])).

fof(f286,plain,
    ( spl11_44
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f211,f105,f284])).

fof(f284,plain,
    ( spl11_44
  <=> m1_subset_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f211,plain,
    ( m1_subset_1(sK4,sK5)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f106,f54])).

fof(f272,plain,
    ( spl11_42
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f210,f98,f270])).

fof(f270,plain,
    ( spl11_42
  <=> m1_subset_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f210,plain,
    ( m1_subset_1(sK3,sK4)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f99,f54])).

fof(f265,plain,
    ( spl11_40
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f209,f91,f263])).

fof(f263,plain,
    ( spl11_40
  <=> m1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f209,plain,
    ( m1_subset_1(sK2,sK3)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f92,f54])).

fof(f258,plain,
    ( ~ spl11_39
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f195,f126,f256])).

fof(f195,plain,
    ( ~ r2_hidden(sK2,sK7)
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f127,f53])).

fof(f251,plain,
    ( ~ spl11_37
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f194,f119,f249])).

fof(f194,plain,
    ( ~ r2_hidden(sK7,sK6)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f120,f53])).

fof(f244,plain,
    ( ~ spl11_35
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f193,f112,f242])).

fof(f193,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f113,f53])).

fof(f235,plain,
    ( ~ spl11_33
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f192,f105,f233])).

fof(f192,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f106,f53])).

fof(f228,plain,
    ( ~ spl11_31
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f191,f98,f226])).

fof(f191,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f99,f53])).

fof(f221,plain,
    ( ~ spl11_29
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f190,f91,f219])).

fof(f190,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f92,f53])).

fof(f208,plain,
    ( ~ spl11_27
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f144,f126,f206])).

fof(f144,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f127,f56])).

fof(f183,plain,
    ( ~ spl11_25
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f143,f119,f181])).

fof(f143,plain,
    ( ~ v1_xboole_0(sK7)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f120,f56])).

fof(f176,plain,
    ( ~ spl11_23
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f142,f112,f174])).

fof(f142,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f113,f56])).

fof(f169,plain,
    ( ~ spl11_21
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f141,f105,f167])).

fof(f141,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f106,f56])).

fof(f162,plain,
    ( ~ spl11_19
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f140,f98,f160])).

fof(f140,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f99,f56])).

fof(f155,plain,
    ( ~ spl11_17
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f139,f91,f153])).

fof(f139,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f92,f56])).

fof(f138,plain,
    ( spl11_14
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f129,f84,f136])).

fof(f129,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f85,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',t6_boole)).

fof(f128,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f48,f126])).

fof(f48,plain,(
    r2_hidden(sK7,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( r2_hidden(sK7,sK2)
    & r2_hidden(sK6,sK7)
    & r2_hidden(sK5,sK6)
    & r2_hidden(sK4,sK5)
    & r2_hidden(sK3,sK4)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f29])).

fof(f29,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(X5,X0)
      & r2_hidden(X4,X5)
      & r2_hidden(X3,X4)
      & r2_hidden(X2,X3)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X5,X0)
          & r2_hidden(X4,X5)
          & r2_hidden(X3,X4)
          & r2_hidden(X2,X3)
          & r2_hidden(X1,X2)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X5,X0)
        & r2_hidden(X4,X5)
        & r2_hidden(X3,X4)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',t6_ordinal1)).

fof(f121,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f47,f119])).

fof(f47,plain,(
    r2_hidden(sK6,sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f46,f112])).

fof(f46,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f45,f105])).

fof(f45,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f44,f98])).

fof(f44,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f43,f91])).

fof(f43,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f49,f84])).

fof(f49,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t6_ordinal1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
