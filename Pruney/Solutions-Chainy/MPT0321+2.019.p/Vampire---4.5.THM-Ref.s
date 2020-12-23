%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:31 EST 2020

% Result     : Theorem 47.47s
% Output     : Refutation 47.47s
% Verified   : 
% Statistics : Number of formulae       :  931 (7927 expanded)
%              Number of leaves         :  172 (2417 expanded)
%              Depth                    :   31
%              Number of atoms          : 2423 (31693 expanded)
%              Number of equality atoms :  680 (7137 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193565,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f99,f104,f174,f1429,f1454,f1508,f1962,f1989,f2119,f2239,f2362,f2468,f3870,f3906,f3969,f4034,f4318,f4684,f4722,f4785,f4856,f5202,f5434,f5483,f5490,f5552,f5599,f6744,f6786,f6850,f7947,f8641,f8756,f8781,f8846,f8906,f9157,f9212,f9276,f9957,f10045,f12010,f12173,f12585,f13062,f33016,f33023,f33028,f33038,f34049,f34059,f35012,f35019,f35024,f35720,f37002,f42509,f42535,f42537,f43850,f43883,f44386,f44390,f44402,f44930,f44939,f44943,f45356,f45742,f46164,f46558,f48686,f50028,f50435,f50887,f51617,f51999,f53775,f55967,f56163,f56282,f71580,f73319,f73505,f73851,f74818,f75024,f92907,f100245,f100346,f100450,f112761,f113740,f114022,f126713,f127665,f128129,f142807,f143766,f144049,f158509,f159468,f163057,f163070,f163092,f163105,f163507,f163520,f163543,f163556,f177354,f177361,f177369,f178027,f178182,f178188,f180825,f180938,f180946,f181257,f181264,f181981,f182131,f182132,f182169,f182170,f182175,f182180,f182227,f182264,f182281,f182356,f182357,f182358,f182359,f182363,f182377,f182394,f182411,f182779,f182783,f184286,f187007,f187447,f187452,f187503,f187508,f187516,f187521,f188083,f188292,f188304,f188305,f188306,f188307,f188328,f188342,f188359,f188376,f188766,f188770,f193564])).

fof(f193564,plain,
    ( spl8_140
    | spl8_146
    | ~ spl8_16
    | ~ spl8_141 ),
    inference(avatar_split_clause,[],[f193560,f187449,f3903,f188080,f187444])).

fof(f187444,plain,
    ( spl8_140
  <=> r2_hidden(sK5(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).

fof(f188080,plain,
    ( spl8_146
  <=> r2_hidden(sK5(sK2,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).

fof(f3903,plain,
    ( spl8_16
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f187449,plain,
    ( spl8_141
  <=> r2_hidden(sK5(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f193560,plain,
    ( r2_hidden(sK5(sK2,sK0),k1_xboole_0)
    | r2_hidden(sK5(sK2,sK0),sK2)
    | ~ spl8_16
    | ~ spl8_141 ),
    inference(superposition,[],[f187454,f3905])).

fof(f3905,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f3903])).

fof(f187454,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,sK0),k4_xboole_0(sK0,X1))
        | r2_hidden(sK5(sK2,sK0),X1) )
    | ~ spl8_141 ),
    inference(resolution,[],[f187451,f75])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f187451,plain,
    ( r2_hidden(sK5(sK2,sK0),sK0)
    | ~ spl8_141 ),
    inference(avatar_component_clause,[],[f187449])).

fof(f188770,plain,
    ( spl8_7
    | spl8_154
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177413,f177358,f188768,f167])).

fof(f167,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f188768,plain,
    ( spl8_154
  <=> ! [X18] : ~ r2_hidden(sK5(k1_xboole_0,sK2),k4_xboole_0(X18,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f177358,plain,
    ( spl8_116
  <=> sK2 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f177413,plain,
    ( ! [X18] :
        ( ~ r2_hidden(sK5(k1_xboole_0,sK2),k4_xboole_0(X18,sK0))
        | k1_xboole_0 = sK2 )
    | ~ spl8_116 ),
    inference(superposition,[],[f449,f177360])).

fof(f177360,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl8_116 ),
    inference(avatar_component_clause,[],[f177358])).

fof(f449,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK5(k1_xboole_0,k3_xboole_0(X6,X7)),k4_xboole_0(X8,X7))
      | k1_xboole_0 = k3_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f146,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f146,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(k1_xboole_0,k3_xboole_0(X4,X5)),X5)
      | k1_xboole_0 = k3_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f143,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f143,plain,(
    ! [X1] :
      ( r2_hidden(sK5(k1_xboole_0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f141,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f141,plain,(
    ! [X1] :
      ( r2_xboole_0(k1_xboole_0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f52,f138])).

fof(f138,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f125,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k1_xboole_0,X0),X1)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f124,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f124,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X11,k1_xboole_0)
      | r2_hidden(X11,X10) ) ),
    inference(superposition,[],[f79,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f188766,plain,
    ( spl8_3
    | spl8_153
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177410,f177358,f188764,f92])).

fof(f92,plain,
    ( spl8_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f188764,plain,
    ( spl8_153
  <=> ! [X15] : ~ r2_hidden(sK5(sK2,sK0),k4_xboole_0(X15,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_153])])).

fof(f177410,plain,
    ( ! [X15] :
        ( ~ r2_hidden(sK5(sK2,sK0),k4_xboole_0(X15,sK0))
        | sK0 = sK2 )
    | ~ spl8_116 ),
    inference(superposition,[],[f393,f177360])).

fof(f393,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK5(k3_xboole_0(X6,X7),X7),k4_xboole_0(X8,X7))
      | k3_xboole_0(X6,X7) = X7 ) ),
    inference(resolution,[],[f334,f76])).

fof(f334,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(k3_xboole_0(X2,X3),X3),X3)
      | k3_xboole_0(X2,X3) = X3 ) ),
    inference(resolution,[],[f235,f58])).

fof(f235,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(k3_xboole_0(X0,X1),X1)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f232,f52])).

fof(f232,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f119,f54])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f79,f53])).

fof(f188376,plain,
    ( spl8_7
    | spl8_152
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177475,f177358,f188374,f167])).

fof(f188374,plain,
    ( spl8_152
  <=> ! [X118] : r2_hidden(sK7(X118,k1_xboole_0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_152])])).

fof(f177475,plain,
    ( ! [X118] :
        ( r2_hidden(sK7(X118,k1_xboole_0,sK2),sK0)
        | k1_xboole_0 = sK2 )
    | ~ spl8_116 ),
    inference(superposition,[],[f29246,f177360])).

fof(f29246,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(sK7(X14,k1_xboole_0,k3_xboole_0(X12,X13)),X13)
      | k1_xboole_0 = k3_xboole_0(X12,X13) ) ),
    inference(resolution,[],[f29241,f79])).

fof(f29241,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,k1_xboole_0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f29237,f48])).

fof(f29237,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,k1_xboole_0,X1),X1)
      | k3_xboole_0(X0,k1_xboole_0) = X1 ) ),
    inference(condensation,[],[f29198])).

fof(f29198,plain,(
    ! [X35,X33,X34] :
      ( r2_hidden(sK7(X33,k1_xboole_0,X34),X34)
      | k3_xboole_0(X33,k1_xboole_0) = X34
      | r2_hidden(sK7(X33,k1_xboole_0,X34),X35) ) ),
    inference(resolution,[],[f70,f124])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f188359,plain,
    ( spl8_7
    | spl8_151
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177445,f177358,f188357,f167])).

fof(f188357,plain,
    ( spl8_151
  <=> ! [X68] : r2_hidden(sK7(k1_xboole_0,X68,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f177445,plain,
    ( ! [X68] :
        ( r2_hidden(sK7(k1_xboole_0,X68,sK2),sK0)
        | k1_xboole_0 = sK2 )
    | ~ spl8_116 ),
    inference(superposition,[],[f12061,f177360])).

fof(f12061,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(sK7(k1_xboole_0,X14,k3_xboole_0(X12,X13)),X13)
      | k1_xboole_0 = k3_xboole_0(X12,X13) ) ),
    inference(resolution,[],[f12056,f79])).

fof(f12056,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(k1_xboole_0,X0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f12055,f105])).

fof(f12055,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(k1_xboole_0,X0,X1),X1)
      | k3_xboole_0(k1_xboole_0,X0) = X1 ) ),
    inference(condensation,[],[f12017])).

fof(f12017,plain,(
    ! [X26,X24,X25] :
      ( r2_hidden(sK7(k1_xboole_0,X24,X25),X25)
      | k3_xboole_0(k1_xboole_0,X24) = X25
      | r2_hidden(sK7(k1_xboole_0,X24,X25),X26) ) ),
    inference(resolution,[],[f69,f124])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f188342,plain,
    ( spl8_7
    | spl8_150
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177443,f177358,f188340,f167])).

fof(f188340,plain,
    ( spl8_150
  <=> ! [X66] : r2_hidden(sK6(X66,X66,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f177443,plain,
    ( ! [X66] :
        ( r2_hidden(sK6(X66,X66,sK2),sK0)
        | k1_xboole_0 = sK2 )
    | ~ spl8_116 ),
    inference(superposition,[],[f6323,f177360])).

fof(f6323,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK6(X15,X15,k3_xboole_0(X13,X14)),X14)
      | k1_xboole_0 = k3_xboole_0(X13,X14) ) ),
    inference(resolution,[],[f6317,f79])).

fof(f6317,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f6316,f490])).

fof(f490,plain,(
    ! [X14] : k1_xboole_0 = k4_xboole_0(X14,X14) ),
    inference(superposition,[],[f482,f48])).

fof(f482,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X2) = k3_xboole_0(k4_xboole_0(X2,X2),X3) ),
    inference(resolution,[],[f480,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f480,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X0),X1)
      | r1_tarski(k4_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f184,f53])).

fof(f184,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X10,X11),X12),k4_xboole_0(X13,X10))
      | r1_tarski(k4_xboole_0(X10,X11),X12) ) ),
    inference(resolution,[],[f117,f76])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6316,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK6(X0,X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f6308])).

fof(f6308,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK6(X0,X0,X1),X1)
      | r2_hidden(sK6(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f188328,plain,
    ( spl8_7
    | spl8_149
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177429,f177358,f188326,f167])).

fof(f188326,plain,
    ( spl8_149
  <=> ! [X42] : r2_hidden(sK6(k1_xboole_0,X42,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f177429,plain,
    ( ! [X42] :
        ( r2_hidden(sK6(k1_xboole_0,X42,sK2),sK0)
        | k1_xboole_0 = sK2 )
    | ~ spl8_116 ),
    inference(superposition,[],[f2428,f177360])).

fof(f2428,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(sK6(k1_xboole_0,X14,k3_xboole_0(X12,X13)),X13)
      | k1_xboole_0 = k3_xboole_0(X12,X13) ) ),
    inference(resolution,[],[f2344,f79])).

fof(f2344,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k1_xboole_0,X0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f2343,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f2343,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k1_xboole_0,X0,X1),X1)
      | k4_xboole_0(k1_xboole_0,X0) = X1 ) ),
    inference(condensation,[],[f2327])).

fof(f2327,plain,(
    ! [X26,X24,X25] :
      ( r2_hidden(sK6(k1_xboole_0,X24,X25),X25)
      | k4_xboole_0(k1_xboole_0,X24) = X25
      | r2_hidden(sK6(k1_xboole_0,X24,X25),X26) ) ),
    inference(resolution,[],[f63,f124])).

fof(f188307,plain,
    ( spl8_3
    | ~ spl8_146
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177414,f177358,f188080,f92])).

fof(f177414,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),k1_xboole_0)
    | sK0 = sK2
    | ~ spl8_116 ),
    inference(superposition,[],[f717,f177360])).

fof(f717,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(k3_xboole_0(X1,X0),X0),k1_xboole_0)
      | k3_xboole_0(X1,X0) = X0 ) ),
    inference(superposition,[],[f393,f47])).

fof(f188306,plain,
    ( spl8_3
    | spl8_141
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177406,f177358,f187449,f92])).

fof(f177406,plain,
    ( r2_hidden(sK5(sK2,sK0),sK0)
    | sK0 = sK2
    | ~ spl8_116 ),
    inference(superposition,[],[f334,f177360])).

fof(f188305,plain,
    ( spl8_3
    | ~ spl8_140
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177405,f177358,f187444,f92])).

fof(f177405,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),sK2)
    | sK0 = sK2
    | ~ spl8_116 ),
    inference(superposition,[],[f333,f177360])).

fof(f333,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(k3_xboole_0(X0,X1),X1),k3_xboole_0(X0,X1))
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f235,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f188304,plain,
    ( ~ spl8_148
    | ~ spl8_21
    | ~ spl8_147 ),
    inference(avatar_split_clause,[],[f188296,f188289,f4719,f188301])).

fof(f188301,plain,
    ( spl8_148
  <=> r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).

fof(f4719,plain,
    ( spl8_21
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f188289,plain,
    ( spl8_147
  <=> r2_hidden(sK5(k1_xboole_0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f188296,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl8_21
    | ~ spl8_147 ),
    inference(superposition,[],[f188295,f4721])).

fof(f4721,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f4719])).

fof(f188295,plain,
    ( ! [X2] : ~ r2_hidden(sK5(k1_xboole_0,sK2),k4_xboole_0(X2,sK0))
    | ~ spl8_147 ),
    inference(resolution,[],[f188291,f76])).

fof(f188291,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK2),sK0)
    | ~ spl8_147 ),
    inference(avatar_component_clause,[],[f188289])).

fof(f188292,plain,
    ( spl8_7
    | spl8_147
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177395,f177358,f188289,f167])).

fof(f177395,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK2),sK0)
    | k1_xboole_0 = sK2
    | ~ spl8_116 ),
    inference(superposition,[],[f146,f177360])).

fof(f188083,plain,
    ( ~ spl8_146
    | ~ spl8_21
    | ~ spl8_141 ),
    inference(avatar_split_clause,[],[f188075,f187449,f4719,f188080])).

fof(f188075,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),k1_xboole_0)
    | ~ spl8_21
    | ~ spl8_141 ),
    inference(superposition,[],[f187455,f4721])).

fof(f187455,plain,
    ( ! [X2] : ~ r2_hidden(sK5(sK2,sK0),k4_xboole_0(X2,sK0))
    | ~ spl8_141 ),
    inference(resolution,[],[f187451,f76])).

fof(f187521,plain,
    ( ~ spl8_145
    | ~ spl8_4
    | spl8_132 ),
    inference(avatar_split_clause,[],[f185875,f182353,f96,f187518])).

fof(f187518,plain,
    ( spl8_145
  <=> r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).

fof(f96,plain,
    ( spl8_4
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f182353,plain,
    ( spl8_132
  <=> r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).

fof(f185875,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl8_4
    | spl8_132 ),
    inference(backward_demodulation,[],[f182355,f97])).

fof(f97,plain,
    ( sK1 = sK3
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f182355,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0)
    | spl8_132 ),
    inference(avatar_component_clause,[],[f182353])).

fof(f187516,plain,
    ( ~ spl8_144
    | ~ spl8_4
    | spl8_130 ),
    inference(avatar_split_clause,[],[f185866,f182261,f96,f187513])).

fof(f187513,plain,
    ( spl8_144
  <=> r2_hidden(sK5(sK1,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).

fof(f182261,plain,
    ( spl8_130
  <=> r2_hidden(sK5(sK3,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_130])])).

fof(f185866,plain,
    ( ~ r2_hidden(sK5(sK1,sK1),k1_xboole_0)
    | ~ spl8_4
    | spl8_130 ),
    inference(backward_demodulation,[],[f182263,f97])).

fof(f182263,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),k1_xboole_0)
    | spl8_130 ),
    inference(avatar_component_clause,[],[f182261])).

fof(f187508,plain,
    ( spl8_143
    | ~ spl8_4
    | ~ spl8_131 ),
    inference(avatar_split_clause,[],[f185869,f182278,f96,f187505])).

fof(f187505,plain,
    ( spl8_143
  <=> r2_hidden(sK5(k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).

fof(f182278,plain,
    ( spl8_131
  <=> r2_hidden(sK5(k1_xboole_0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).

fof(f185869,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_131 ),
    inference(backward_demodulation,[],[f182280,f97])).

fof(f182280,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK3),sK1)
    | ~ spl8_131 ),
    inference(avatar_component_clause,[],[f182278])).

fof(f187503,plain,
    ( ~ spl8_142
    | ~ spl8_4
    | spl8_128 ),
    inference(avatar_split_clause,[],[f185826,f182172,f96,f187500])).

fof(f187500,plain,
    ( spl8_142
  <=> r2_hidden(sK5(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f182172,plain,
    ( spl8_128
  <=> r2_hidden(sK5(sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).

fof(f185826,plain,
    ( ~ r2_hidden(sK5(sK1,sK1),sK1)
    | ~ spl8_4
    | spl8_128 ),
    inference(backward_demodulation,[],[f182174,f97])).

fof(f182174,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),sK3)
    | spl8_128 ),
    inference(avatar_component_clause,[],[f182172])).

fof(f187452,plain,
    ( spl8_141
    | ~ spl8_119 ),
    inference(avatar_split_clause,[],[f187002,f178185,f187449])).

fof(f178185,plain,
    ( spl8_119
  <=> r2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f187002,plain,
    ( r2_hidden(sK5(sK2,sK0),sK0)
    | ~ spl8_119 ),
    inference(resolution,[],[f178187,f58])).

fof(f178187,plain,
    ( r2_xboole_0(sK2,sK0)
    | ~ spl8_119 ),
    inference(avatar_component_clause,[],[f178185])).

fof(f187447,plain,
    ( ~ spl8_140
    | ~ spl8_119 ),
    inference(avatar_split_clause,[],[f187001,f178185,f187444])).

fof(f187001,plain,
    ( ~ r2_hidden(sK5(sK2,sK0),sK2)
    | ~ spl8_119 ),
    inference(resolution,[],[f178187,f59])).

fof(f187007,plain,
    ( ~ spl8_139
    | ~ spl8_4
    | spl8_127 ),
    inference(avatar_split_clause,[],[f185825,f182128,f96,f187004])).

fof(f187004,plain,
    ( spl8_139
  <=> r2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_139])])).

fof(f182128,plain,
    ( spl8_127
  <=> r2_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).

fof(f185825,plain,
    ( ~ r2_xboole_0(sK1,sK1)
    | ~ spl8_4
    | spl8_127 ),
    inference(backward_demodulation,[],[f182129,f97])).

fof(f182129,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | spl8_127 ),
    inference(avatar_component_clause,[],[f182128])).

fof(f184286,plain,
    ( spl8_128
    | spl8_130
    | ~ spl8_10
    | ~ spl8_129 ),
    inference(avatar_split_clause,[],[f184282,f182177,f1451,f182261,f182172])).

fof(f1451,plain,
    ( spl8_10
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f182177,plain,
    ( spl8_129
  <=> r2_hidden(sK5(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).

fof(f184282,plain,
    ( r2_hidden(sK5(sK3,sK1),k1_xboole_0)
    | r2_hidden(sK5(sK3,sK1),sK3)
    | ~ spl8_10
    | ~ spl8_129 ),
    inference(superposition,[],[f182182,f1453])).

fof(f1453,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f1451])).

fof(f182182,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK3,sK1),k4_xboole_0(sK1,X1))
        | r2_hidden(sK5(sK3,sK1),X1) )
    | ~ spl8_129 ),
    inference(resolution,[],[f182179,f75])).

fof(f182179,plain,
    ( r2_hidden(sK5(sK3,sK1),sK1)
    | ~ spl8_129 ),
    inference(avatar_component_clause,[],[f182177])).

fof(f182783,plain,
    ( spl8_6
    | spl8_138
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181304,f181261,f182781,f163])).

fof(f163,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f182781,plain,
    ( spl8_138
  <=> ! [X19] : ~ r2_hidden(sK5(k1_xboole_0,sK3),k4_xboole_0(X19,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f181261,plain,
    ( spl8_125
  <=> sK3 = k3_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_125])])).

fof(f181304,plain,
    ( ! [X19] :
        ( ~ r2_hidden(sK5(k1_xboole_0,sK3),k4_xboole_0(X19,sK1))
        | k1_xboole_0 = sK3 )
    | ~ spl8_125 ),
    inference(superposition,[],[f449,f181263])).

fof(f181263,plain,
    ( sK3 = k3_xboole_0(sK3,sK1)
    | ~ spl8_125 ),
    inference(avatar_component_clause,[],[f181261])).

fof(f182779,plain,
    ( spl8_4
    | spl8_137
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181301,f181261,f182777,f96])).

fof(f182777,plain,
    ( spl8_137
  <=> ! [X16] : ~ r2_hidden(sK5(sK3,sK1),k4_xboole_0(X16,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f181301,plain,
    ( ! [X16] :
        ( ~ r2_hidden(sK5(sK3,sK1),k4_xboole_0(X16,sK1))
        | sK1 = sK3 )
    | ~ spl8_125 ),
    inference(superposition,[],[f393,f181263])).

fof(f182411,plain,
    ( spl8_6
    | spl8_136
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181366,f181261,f182409,f163])).

fof(f182409,plain,
    ( spl8_136
  <=> ! [X119] : r2_hidden(sK7(X119,k1_xboole_0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_136])])).

fof(f181366,plain,
    ( ! [X119] :
        ( r2_hidden(sK7(X119,k1_xboole_0,sK3),sK1)
        | k1_xboole_0 = sK3 )
    | ~ spl8_125 ),
    inference(superposition,[],[f29246,f181263])).

fof(f182394,plain,
    ( spl8_6
    | spl8_135
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181336,f181261,f182392,f163])).

fof(f182392,plain,
    ( spl8_135
  <=> ! [X69] : r2_hidden(sK7(k1_xboole_0,X69,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_135])])).

fof(f181336,plain,
    ( ! [X69] :
        ( r2_hidden(sK7(k1_xboole_0,X69,sK3),sK1)
        | k1_xboole_0 = sK3 )
    | ~ spl8_125 ),
    inference(superposition,[],[f12061,f181263])).

fof(f182377,plain,
    ( spl8_6
    | spl8_134
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181334,f181261,f182375,f163])).

fof(f182375,plain,
    ( spl8_134
  <=> ! [X67] : r2_hidden(sK6(X67,X67,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f181334,plain,
    ( ! [X67] :
        ( r2_hidden(sK6(X67,X67,sK3),sK1)
        | k1_xboole_0 = sK3 )
    | ~ spl8_125 ),
    inference(superposition,[],[f6323,f181263])).

fof(f182363,plain,
    ( spl8_6
    | spl8_133
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181320,f181261,f182361,f163])).

fof(f182361,plain,
    ( spl8_133
  <=> ! [X43] : r2_hidden(sK6(k1_xboole_0,X43,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).

fof(f181320,plain,
    ( ! [X43] :
        ( r2_hidden(sK6(k1_xboole_0,X43,sK3),sK1)
        | k1_xboole_0 = sK3 )
    | ~ spl8_125 ),
    inference(superposition,[],[f2428,f181263])).

fof(f182359,plain,
    ( spl8_4
    | ~ spl8_130
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181305,f181261,f182261,f96])).

fof(f181305,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),k1_xboole_0)
    | sK1 = sK3
    | ~ spl8_125 ),
    inference(superposition,[],[f717,f181263])).

fof(f182358,plain,
    ( spl8_4
    | spl8_129
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181297,f181261,f182177,f96])).

fof(f181297,plain,
    ( r2_hidden(sK5(sK3,sK1),sK1)
    | sK1 = sK3
    | ~ spl8_125 ),
    inference(superposition,[],[f334,f181263])).

fof(f182357,plain,
    ( spl8_4
    | ~ spl8_128
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181296,f181261,f182172,f96])).

fof(f181296,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),sK3)
    | sK1 = sK3
    | ~ spl8_125 ),
    inference(superposition,[],[f333,f181263])).

fof(f182356,plain,
    ( ~ spl8_132
    | ~ spl8_13
    | ~ spl8_131 ),
    inference(avatar_split_clause,[],[f182348,f182278,f1986,f182353])).

fof(f1986,plain,
    ( spl8_13
  <=> k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f182348,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl8_13
    | ~ spl8_131 ),
    inference(superposition,[],[f182284,f1988])).

fof(f1988,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f1986])).

fof(f182284,plain,
    ( ! [X2] : ~ r2_hidden(sK5(k1_xboole_0,sK3),k4_xboole_0(X2,sK1))
    | ~ spl8_131 ),
    inference(resolution,[],[f182280,f76])).

fof(f182281,plain,
    ( spl8_6
    | spl8_131
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181286,f181261,f182278,f163])).

fof(f181286,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK3),sK1)
    | k1_xboole_0 = sK3
    | ~ spl8_125 ),
    inference(superposition,[],[f146,f181263])).

fof(f182264,plain,
    ( ~ spl8_130
    | ~ spl8_13
    | ~ spl8_129 ),
    inference(avatar_split_clause,[],[f182256,f182177,f1986,f182261])).

fof(f182256,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),k1_xboole_0)
    | ~ spl8_13
    | ~ spl8_129 ),
    inference(superposition,[],[f182183,f1988])).

fof(f182183,plain,
    ( ! [X2] : ~ r2_hidden(sK5(sK3,sK1),k4_xboole_0(X2,sK1))
    | ~ spl8_129 ),
    inference(resolution,[],[f182179,f76])).

fof(f182227,plain,
    ( spl8_4
    | spl8_127
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f182005,f181978,f182128,f96])).

fof(f181978,plain,
    ( spl8_126
  <=> sK3 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f182005,plain,
    ( r2_xboole_0(sK3,sK1)
    | sK1 = sK3
    | ~ spl8_126 ),
    inference(superposition,[],[f244,f181980])).

fof(f181980,plain,
    ( sK3 = k3_xboole_0(sK1,sK3)
    | ~ spl8_126 ),
    inference(avatar_component_clause,[],[f181978])).

fof(f244,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(k3_xboole_0(X0,X1),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f238,f52])).

fof(f238,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f232,f50])).

fof(f182180,plain,
    ( spl8_129
    | ~ spl8_127 ),
    inference(avatar_split_clause,[],[f182136,f182128,f182177])).

fof(f182136,plain,
    ( r2_hidden(sK5(sK3,sK1),sK1)
    | ~ spl8_127 ),
    inference(resolution,[],[f182130,f58])).

fof(f182130,plain,
    ( r2_xboole_0(sK3,sK1)
    | ~ spl8_127 ),
    inference(avatar_component_clause,[],[f182128])).

fof(f182175,plain,
    ( ~ spl8_128
    | ~ spl8_127 ),
    inference(avatar_split_clause,[],[f182135,f182128,f182172])).

fof(f182135,plain,
    ( ~ r2_hidden(sK5(sK3,sK1),sK3)
    | ~ spl8_127 ),
    inference(resolution,[],[f182130,f59])).

fof(f182170,plain,(
    ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f182164])).

fof(f182164,plain,
    ( $false
    | ~ spl8_124 ),
    inference(resolution,[],[f182143,f182138])).

fof(f182138,plain,
    ( ! [X0] : r2_hidden(sK4(sK3,sK1),X0)
    | ~ spl8_124 ),
    inference(resolution,[],[f181256,f124])).

fof(f181256,plain,
    ( r2_hidden(sK4(sK3,sK1),k1_xboole_0)
    | ~ spl8_124 ),
    inference(avatar_component_clause,[],[f181254])).

fof(f181254,plain,
    ( spl8_124
  <=> r2_hidden(sK4(sK3,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f182143,plain,
    ( ! [X3] : ~ r2_hidden(sK4(sK3,sK1),X3)
    | ~ spl8_124 ),
    inference(forward_demodulation,[],[f182141,f99909])).

fof(f99909,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f99875,f200])).

fof(f200,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f196,f50])).

fof(f196,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f192,f51])).

fof(f192,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f117,f54])).

fof(f99875,plain,(
    ! [X1] : k3_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(resolution,[],[f99869,f51])).

fof(f99869,plain,(
    ! [X29] : r1_tarski(X29,k4_xboole_0(X29,k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f99841])).

fof(f99841,plain,(
    ! [X29] :
      ( r1_tarski(X29,k4_xboole_0(X29,k1_xboole_0))
      | r1_tarski(X29,k4_xboole_0(X29,k1_xboole_0)) ) ),
    inference(resolution,[],[f84569,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f116,f47])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f76,f53])).

fof(f84569,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK4(X14,k4_xboole_0(X14,X15)),X15)
      | r1_tarski(X14,k4_xboole_0(X14,X15)) ) ),
    inference(duplicate_literal_removal,[],[f84542])).

fof(f84542,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK4(X14,k4_xboole_0(X14,X15)),X15)
      | r1_tarski(X14,k4_xboole_0(X14,X15))
      | r1_tarski(X14,k4_xboole_0(X14,X15)) ) ),
    inference(resolution,[],[f175,f54])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,X2))
      | r2_hidden(sK4(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f75,f53])).

fof(f182141,plain,
    ( ! [X3] : ~ r2_hidden(sK4(sK3,sK1),k4_xboole_0(X3,k1_xboole_0))
    | ~ spl8_124 ),
    inference(resolution,[],[f181256,f76])).

fof(f182169,plain,(
    ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f182167])).

fof(f182167,plain,
    ( $false
    | ~ spl8_124 ),
    inference(resolution,[],[f182143,f181256])).

fof(f182132,plain,
    ( spl8_123
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f182004,f181978,f181250])).

fof(f181250,plain,
    ( spl8_123
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).

fof(f182004,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl8_126 ),
    inference(superposition,[],[f238,f181980])).

fof(f182131,plain,
    ( spl8_127
    | spl8_4
    | ~ spl8_123 ),
    inference(avatar_split_clause,[],[f181258,f181250,f96,f182128])).

fof(f181258,plain,
    ( sK1 = sK3
    | r2_xboole_0(sK3,sK1)
    | ~ spl8_123 ),
    inference(resolution,[],[f181252,f52])).

fof(f181252,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl8_123 ),
    inference(avatar_component_clause,[],[f181250])).

fof(f181981,plain,
    ( spl8_126
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f181265,f181261,f181978])).

fof(f181265,plain,
    ( sK3 = k3_xboole_0(sK1,sK3)
    | ~ spl8_125 ),
    inference(superposition,[],[f181263,f50])).

fof(f181264,plain,
    ( spl8_125
    | ~ spl8_123 ),
    inference(avatar_split_clause,[],[f181259,f181250,f181261])).

fof(f181259,plain,
    ( sK3 = k3_xboole_0(sK3,sK1)
    | ~ spl8_123 ),
    inference(resolution,[],[f181252,f51])).

fof(f181257,plain,
    ( spl8_123
    | spl8_124
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f181247,f1986,f181254,f181250])).

fof(f181247,plain,
    ( r2_hidden(sK4(sK3,sK1),k1_xboole_0)
    | r1_tarski(sK3,sK1)
    | ~ spl8_13 ),
    inference(duplicate_literal_removal,[],[f181241])).

fof(f181241,plain,
    ( r2_hidden(sK4(sK3,sK1),k1_xboole_0)
    | r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl8_13 ),
    inference(resolution,[],[f84559,f54])).

fof(f84559,plain,
    ( ! [X22] :
        ( r2_hidden(sK4(sK3,X22),sK1)
        | r2_hidden(sK4(sK3,X22),k1_xboole_0)
        | r1_tarski(sK3,X22) )
    | ~ spl8_13 ),
    inference(superposition,[],[f175,f1988])).

fof(f180946,plain,
    ( ~ spl8_122
    | ~ spl8_49
    | spl8_52 ),
    inference(avatar_split_clause,[],[f178248,f33035,f33013,f180943])).

fof(f180943,plain,
    ( spl8_122
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f33013,plain,
    ( spl8_49
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f33035,plain,
    ( spl8_52
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f178248,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k1_xboole_0)
    | ~ spl8_49
    | spl8_52 ),
    inference(backward_demodulation,[],[f33037,f33015])).

fof(f33015,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f33013])).

fof(f33037,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k1_xboole_0)
    | spl8_52 ),
    inference(avatar_component_clause,[],[f33035])).

fof(f180938,plain,
    ( spl8_121
    | ~ spl8_49
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f178249,f34046,f33013,f180935])).

fof(f180935,plain,
    ( spl8_121
  <=> r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_121])])).

fof(f34046,plain,
    ( spl8_53
  <=> r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f178249,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_49
    | ~ spl8_53 ),
    inference(backward_demodulation,[],[f34048,f33015])).

fof(f34048,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f34046])).

fof(f180825,plain,
    ( ~ spl8_120
    | ~ spl8_3
    | spl8_65 ),
    inference(avatar_split_clause,[],[f179426,f43880,f92,f180822])).

fof(f180822,plain,
    ( spl8_120
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f43880,plain,
    ( spl8_65
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f179426,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK3)
    | ~ spl8_3
    | spl8_65 ),
    inference(backward_demodulation,[],[f43882,f93])).

fof(f93,plain,
    ( sK0 = sK2
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f43882,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    | spl8_65 ),
    inference(avatar_component_clause,[],[f43880])).

fof(f178188,plain,
    ( spl8_119
    | spl8_3
    | ~ spl8_114 ),
    inference(avatar_split_clause,[],[f177370,f177347,f92,f178185])).

fof(f177347,plain,
    ( spl8_114
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f177370,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK2,sK0)
    | ~ spl8_114 ),
    inference(resolution,[],[f177349,f52])).

fof(f177349,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl8_114 ),
    inference(avatar_component_clause,[],[f177347])).

fof(f178182,plain,
    ( ~ spl8_118
    | spl8_69
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177668,f177358,f44927,f178179])).

fof(f178179,plain,
    ( spl8_118
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f44927,plain,
    ( spl8_69
  <=> k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f177668,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK1)
    | spl8_69
    | ~ spl8_116 ),
    inference(backward_demodulation,[],[f44929,f177372])).

fof(f177372,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl8_116 ),
    inference(superposition,[],[f177360,f50])).

fof(f44929,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | spl8_69 ),
    inference(avatar_component_clause,[],[f44927])).

fof(f178027,plain,
    ( spl8_117
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f177372,f177358,f178024])).

fof(f178024,plain,
    ( spl8_117
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f177369,plain,
    ( spl8_114
    | ~ spl8_115 ),
    inference(avatar_split_clause,[],[f177362,f177351,f177347])).

fof(f177351,plain,
    ( spl8_115
  <=> r2_hidden(sK4(sK2,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f177362,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl8_115 ),
    inference(resolution,[],[f177353,f152])).

fof(f177353,plain,
    ( r2_hidden(sK4(sK2,sK0),k1_xboole_0)
    | ~ spl8_115 ),
    inference(avatar_component_clause,[],[f177351])).

fof(f177361,plain,
    ( spl8_116
    | ~ spl8_114 ),
    inference(avatar_split_clause,[],[f177356,f177347,f177358])).

fof(f177356,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl8_114 ),
    inference(resolution,[],[f177349,f51])).

fof(f177354,plain,
    ( spl8_114
    | spl8_115
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f177344,f4719,f177351,f177347])).

fof(f177344,plain,
    ( r2_hidden(sK4(sK2,sK0),k1_xboole_0)
    | r1_tarski(sK2,sK0)
    | ~ spl8_21 ),
    inference(duplicate_literal_removal,[],[f177338])).

fof(f177338,plain,
    ( r2_hidden(sK4(sK2,sK0),k1_xboole_0)
    | r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0)
    | ~ spl8_21 ),
    inference(resolution,[],[f84558,f54])).

fof(f84558,plain,
    ( ! [X21] :
        ( r2_hidden(sK4(sK2,X21),sK0)
        | r2_hidden(sK4(sK2,X21),k1_xboole_0)
        | r1_tarski(sK2,X21) )
    | ~ spl8_21 ),
    inference(superposition,[],[f175,f4721])).

fof(f163556,plain,
    ( spl8_113
    | ~ spl8_112 ),
    inference(avatar_split_clause,[],[f163545,f163540,f163553])).

fof(f163553,plain,
    ( spl8_113
  <=> r2_hidden(sK4(sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f163540,plain,
    ( spl8_112
  <=> r2_hidden(sK4(sK2,k1_xboole_0),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).

fof(f163545,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),sK2)
    | ~ spl8_112 ),
    inference(resolution,[],[f163542,f79])).

fof(f163542,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),k3_xboole_0(sK0,sK2))
    | ~ spl8_112 ),
    inference(avatar_component_clause,[],[f163540])).

fof(f163543,plain,
    ( spl8_94
    | spl8_112
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f99861,f12170,f163540,f100443])).

fof(f100443,plain,
    ( spl8_94
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f12170,plain,
    ( spl8_45
  <=> k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f99861,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),k3_xboole_0(sK0,sK2))
    | r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_45 ),
    inference(superposition,[],[f84569,f12172])).

fof(f12172,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f12170])).

fof(f163520,plain,
    ( spl8_111
    | ~ spl8_110 ),
    inference(avatar_split_clause,[],[f163509,f163504,f163517])).

fof(f163517,plain,
    ( spl8_111
  <=> r2_hidden(sK4(sK3,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).

fof(f163504,plain,
    ( spl8_110
  <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f163509,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),sK3)
    | ~ spl8_110 ),
    inference(resolution,[],[f163506,f79])).

fof(f163506,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3))
    | ~ spl8_110 ),
    inference(avatar_component_clause,[],[f163504])).

fof(f163507,plain,
    ( spl8_97
    | spl8_110
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f99862,f10042,f163504,f114015])).

fof(f114015,plain,
    ( spl8_97
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f10042,plain,
    ( spl8_43
  <=> k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f99862,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3))
    | r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_43 ),
    inference(superposition,[],[f84569,f10044])).

fof(f10044,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f10042])).

fof(f163105,plain,
    ( spl8_109
    | ~ spl8_108 ),
    inference(avatar_split_clause,[],[f163093,f163089,f163102])).

fof(f163102,plain,
    ( spl8_109
  <=> r2_hidden(sK4(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f163089,plain,
    ( spl8_108
  <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f163093,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK1)
    | ~ spl8_108 ),
    inference(resolution,[],[f163091,f80])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f163091,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3))
    | ~ spl8_108 ),
    inference(avatar_component_clause,[],[f163089])).

fof(f163092,plain,
    ( spl8_103
    | spl8_108
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f99860,f6783,f163089,f144042])).

fof(f144042,plain,
    ( spl8_103
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f6783,plain,
    ( spl8_31
  <=> k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f99860,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3))
    | r1_tarski(sK1,k1_xboole_0)
    | ~ spl8_31 ),
    inference(superposition,[],[f84569,f6785])).

fof(f6785,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f6783])).

fof(f163070,plain,
    ( spl8_107
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f163058,f163054,f163067])).

fof(f163067,plain,
    ( spl8_107
  <=> r2_hidden(sK4(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f163054,plain,
    ( spl8_106
  <=> r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).

fof(f163058,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),sK0)
    | ~ spl8_106 ),
    inference(resolution,[],[f163056,f80])).

fof(f163056,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,sK2))
    | ~ spl8_106 ),
    inference(avatar_component_clause,[],[f163054])).

fof(f163057,plain,
    ( spl8_100
    | spl8_106
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f99859,f9209,f163054,f128122])).

fof(f128122,plain,
    ( spl8_100
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).

fof(f9209,plain,
    ( spl8_40
  <=> k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f99859,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,sK2))
    | r1_tarski(sK0,k1_xboole_0)
    | ~ spl8_40 ),
    inference(superposition,[],[f84569,f9211])).

fof(f9211,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f9209])).

fof(f159468,plain,
    ( ~ spl8_105
    | ~ spl8_10
    | ~ spl8_104 ),
    inference(avatar_split_clause,[],[f159461,f144046,f1451,f159465])).

fof(f159465,plain,
    ( spl8_105
  <=> r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f144046,plain,
    ( spl8_104
  <=> r2_hidden(sK4(sK1,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f159461,plain,
    ( ~ r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl8_10
    | ~ spl8_104 ),
    inference(superposition,[],[f158668,f1453])).

fof(f158668,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK1,k1_xboole_0),k4_xboole_0(X2,sK3))
    | ~ spl8_104 ),
    inference(resolution,[],[f144048,f76])).

fof(f144048,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK3)
    | ~ spl8_104 ),
    inference(avatar_component_clause,[],[f144046])).

fof(f158509,plain,
    ( spl8_2
    | ~ spl8_103 ),
    inference(avatar_split_clause,[],[f144052,f144042,f87])).

fof(f87,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f144052,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_103 ),
    inference(forward_demodulation,[],[f144051,f48])).

fof(f144051,plain,
    ( sK1 = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl8_103 ),
    inference(resolution,[],[f144044,f51])).

fof(f144044,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl8_103 ),
    inference(avatar_component_clause,[],[f144042])).

fof(f144049,plain,
    ( spl8_103
    | spl8_104
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f99867,f1451,f144046,f144042])).

fof(f99867,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK3)
    | r1_tarski(sK1,k1_xboole_0)
    | ~ spl8_10 ),
    inference(superposition,[],[f84569,f1453])).

fof(f143766,plain,
    ( ~ spl8_102
    | ~ spl8_16
    | ~ spl8_101 ),
    inference(avatar_split_clause,[],[f143759,f128126,f3903,f143763])).

fof(f143763,plain,
    ( spl8_102
  <=> r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f128126,plain,
    ( spl8_101
  <=> r2_hidden(sK4(sK0,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f143759,plain,
    ( ~ r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_16
    | ~ spl8_101 ),
    inference(superposition,[],[f142966,f3905])).

fof(f142966,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK0,k1_xboole_0),k4_xboole_0(X2,sK2))
    | ~ spl8_101 ),
    inference(resolution,[],[f128128,f76])).

fof(f128128,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),sK2)
    | ~ spl8_101 ),
    inference(avatar_component_clause,[],[f128126])).

fof(f142807,plain,
    ( spl8_1
    | ~ spl8_100 ),
    inference(avatar_split_clause,[],[f128132,f128122,f82])).

fof(f82,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f128132,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_100 ),
    inference(forward_demodulation,[],[f128131,f48])).

fof(f128131,plain,
    ( sK0 = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl8_100 ),
    inference(resolution,[],[f128124,f51])).

fof(f128124,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl8_100 ),
    inference(avatar_component_clause,[],[f128122])).

fof(f128129,plain,
    ( spl8_100
    | spl8_101
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f99866,f3903,f128126,f128122])).

fof(f99866,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),sK2)
    | r1_tarski(sK0,k1_xboole_0)
    | ~ spl8_16 ),
    inference(superposition,[],[f84569,f3905])).

fof(f127665,plain,
    ( ~ spl8_99
    | ~ spl8_13
    | ~ spl8_98 ),
    inference(avatar_split_clause,[],[f127657,f114019,f1986,f127662])).

fof(f127662,plain,
    ( spl8_99
  <=> r2_hidden(sK4(sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f114019,plain,
    ( spl8_98
  <=> r2_hidden(sK4(sK3,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).

fof(f127657,plain,
    ( ~ r2_hidden(sK4(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_13
    | ~ spl8_98 ),
    inference(superposition,[],[f126869,f1988])).

fof(f126869,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK3,k1_xboole_0),k4_xboole_0(X2,sK1))
    | ~ spl8_98 ),
    inference(resolution,[],[f114021,f76])).

fof(f114021,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),sK1)
    | ~ spl8_98 ),
    inference(avatar_component_clause,[],[f114019])).

fof(f126713,plain,
    ( spl8_6
    | ~ spl8_97 ),
    inference(avatar_split_clause,[],[f114025,f114015,f163])).

fof(f114025,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_97 ),
    inference(forward_demodulation,[],[f114024,f48])).

fof(f114024,plain,
    ( sK3 = k3_xboole_0(sK3,k1_xboole_0)
    | ~ spl8_97 ),
    inference(resolution,[],[f114017,f51])).

fof(f114017,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_97 ),
    inference(avatar_component_clause,[],[f114015])).

fof(f114022,plain,
    ( spl8_97
    | spl8_98
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f99864,f1986,f114019,f114015])).

fof(f99864,plain,
    ( r2_hidden(sK4(sK3,k1_xboole_0),sK1)
    | r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_13 ),
    inference(superposition,[],[f84569,f1988])).

fof(f113740,plain,
    ( ~ spl8_96
    | ~ spl8_21
    | ~ spl8_95 ),
    inference(avatar_split_clause,[],[f113732,f100447,f4719,f113737])).

fof(f113737,plain,
    ( spl8_96
  <=> r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).

fof(f100447,plain,
    ( spl8_95
  <=> r2_hidden(sK4(sK2,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).

fof(f113732,plain,
    ( ~ r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl8_21
    | ~ spl8_95 ),
    inference(superposition,[],[f112916,f4721])).

fof(f112916,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK2,k1_xboole_0),k4_xboole_0(X2,sK0))
    | ~ spl8_95 ),
    inference(resolution,[],[f100449,f76])).

fof(f100449,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),sK0)
    | ~ spl8_95 ),
    inference(avatar_component_clause,[],[f100447])).

fof(f112761,plain,
    ( spl8_7
    | ~ spl8_94 ),
    inference(avatar_split_clause,[],[f100453,f100443,f167])).

fof(f100453,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_94 ),
    inference(forward_demodulation,[],[f100452,f48])).

fof(f100452,plain,
    ( sK2 = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl8_94 ),
    inference(resolution,[],[f100445,f51])).

fof(f100445,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f100443])).

fof(f100450,plain,
    ( spl8_94
    | spl8_95
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f99863,f4719,f100447,f100443])).

fof(f99863,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_21 ),
    inference(superposition,[],[f84569,f4721])).

fof(f100346,plain,
    ( spl8_93
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f100021,f46162,f100343])).

fof(f100343,plain,
    ( spl8_93
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f46162,plain,
    ( spl8_74
  <=> ! [X48] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X48) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f100021,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK2)
    | ~ spl8_74 ),
    inference(forward_demodulation,[],[f99906,f48])).

fof(f99906,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK2),sK2) = k3_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),k1_xboole_0)
    | ~ spl8_74 ),
    inference(superposition,[],[f99875,f46163])).

fof(f46163,plain,
    ( ! [X48] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X48)
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f46162])).

fof(f100245,plain,
    ( spl8_92
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f100016,f45354,f100242])).

fof(f100242,plain,
    ( spl8_92
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f45354,plain,
    ( spl8_72
  <=> ! [X48] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X48) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f100016,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK0)
    | ~ spl8_72 ),
    inference(forward_demodulation,[],[f99905,f48])).

fof(f99905,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK2),sK0) = k3_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),k1_xboole_0)
    | ~ spl8_72 ),
    inference(superposition,[],[f99875,f45355])).

fof(f45355,plain,
    ( ! [X48] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X48)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f45354])).

fof(f92907,plain,
    ( spl8_1
    | ~ spl8_17
    | ~ spl8_81 ),
    inference(avatar_split_clause,[],[f92391,f51615,f3967,f82])).

fof(f3967,plain,
    ( spl8_17
  <=> ! [X8] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f51615,plain,
    ( spl8_81
  <=> ! [X43] : k1_xboole_0 = k4_xboole_0(sK0,X43) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f92391,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_17
    | ~ spl8_81 ),
    inference(superposition,[],[f84584,f3968])).

fof(f3968,plain,
    ( ! [X8] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f3967])).

fof(f84584,plain,
    ( ! [X1] : sK0 = k3_xboole_0(sK0,X1)
    | ~ spl8_81 ),
    inference(resolution,[],[f84582,f51])).

fof(f84582,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl8_81 ),
    inference(duplicate_literal_removal,[],[f84575])).

fof(f84575,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,X0)
        | r1_tarski(sK0,X0) )
    | ~ spl8_81 ),
    inference(resolution,[],[f84565,f152])).

fof(f84565,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,X0),k1_xboole_0)
        | r1_tarski(sK0,X0) )
    | ~ spl8_81 ),
    inference(condensation,[],[f84550])).

fof(f84550,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK4(sK0,X9),k1_xboole_0)
        | r2_hidden(sK4(sK0,X9),X8)
        | r1_tarski(sK0,X9) )
    | ~ spl8_81 ),
    inference(superposition,[],[f175,f51616])).

fof(f51616,plain,
    ( ! [X43] : k1_xboole_0 = k4_xboole_0(sK0,X43)
    | ~ spl8_81 ),
    inference(avatar_component_clause,[],[f51615])).

fof(f75024,plain,
    ( spl8_91
    | spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f74308,f5487,f82,f75022])).

fof(f75022,plain,
    ( spl8_91
  <=> ! [X100,X99] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X99,sK1),k4_xboole_0(X100,k3_xboole_0(sK1,X99))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f5487,plain,
    ( spl8_27
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f74308,plain,
    ( ! [X99,X100] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X99,sK1),k4_xboole_0(X100,k3_xboole_0(sK1,X99))) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f74228])).

fof(f74228,plain,
    ( ! [X99,X100] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X99,sK1),k4_xboole_0(X100,k3_xboole_0(sK1,X99))) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f74022])).

fof(f74022,plain,
    ( ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(X0,sK1),k4_xboole_0(X1,k3_xboole_0(sK1,X0))))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f73891,f50])).

fof(f73891,plain,
    ( ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X1,k3_xboole_0(sK1,X0)),k3_xboole_0(X0,sK1)))
    | ~ spl8_27 ),
    inference(superposition,[],[f8228,f1217])).

fof(f1217,plain,(
    ! [X14,X15,X13] : k3_xboole_0(k2_zfmisc_1(X13,X15),k2_zfmisc_1(X13,X14)) = k2_zfmisc_1(X13,k3_xboole_0(X14,X15)) ),
    inference(superposition,[],[f837,f50])).

fof(f837,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f72,f49])).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f8228,plain,
    ( ! [X33,X31,X32] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(X31,sK1)),k2_zfmisc_1(X32,k4_xboole_0(X33,k3_xboole_0(sK1,X31))))
    | ~ spl8_27 ),
    inference(superposition,[],[f876,f8106])).

fof(f8106,plain,
    ( ! [X1] : k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X1))
    | ~ spl8_27 ),
    inference(superposition,[],[f6633,f5513])).

fof(f5513,plain,
    ( ! [X7] : k2_zfmisc_1(sK0,k3_xboole_0(X7,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(X7,k3_xboole_0(sK1,sK3)))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f5499,f837])).

fof(f5499,plain,
    ( ! [X7] : k3_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(X7,k3_xboole_0(sK1,sK3)))
    | ~ spl8_27 ),
    inference(superposition,[],[f837,f5489])).

fof(f5489,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f5487])).

fof(f6633,plain,
    ( ! [X0] : k2_zfmisc_1(sK0,k3_xboole_0(sK1,X0)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,k3_xboole_0(sK1,sK3)))
    | ~ spl8_27 ),
    inference(superposition,[],[f5512,f50])).

fof(f5512,plain,
    ( ! [X6] : k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),X6)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X6))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f5498,f837])).

fof(f5498,plain,
    ( ! [X6] : k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X6))
    | ~ spl8_27 ),
    inference(superposition,[],[f837,f5489])).

fof(f876,plain,(
    ! [X26,X24,X23,X25] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X26,k4_xboole_0(X24,X23))) ),
    inference(forward_demodulation,[],[f856,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f856,plain,(
    ! [X26,X24,X23,X25] : k3_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X26,k4_xboole_0(X24,X23))) = k2_zfmisc_1(k3_xboole_0(X25,X26),k1_xboole_0) ),
    inference(superposition,[],[f72,f581])).

fof(f581,plain,(
    ! [X24,X25] : k1_xboole_0 = k3_xboole_0(X24,k4_xboole_0(X25,X24)) ),
    inference(superposition,[],[f563,f48])).

fof(f563,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X3)) = k3_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)),X5) ),
    inference(resolution,[],[f561,f51])).

fof(f561,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X1,k4_xboole_0(X0,X1)),X2) ),
    inference(forward_demodulation,[],[f560,f50])).

fof(f560,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
    inference(duplicate_literal_removal,[],[f546])).

fof(f546,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2)
      | r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2) ) ),
    inference(resolution,[],[f218,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f80,f53])).

fof(f218,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X10,X11),X12),k4_xboole_0(X13,X11))
      | r1_tarski(k3_xboole_0(X10,X11),X12) ) ),
    inference(resolution,[],[f119,f76])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74818,plain,
    ( spl8_90
    | spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f74651,f5487,f82,f74816])).

fof(f74816,plain,
    ( spl8_90
  <=> ! [X46] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X46,sK1),k3_xboole_0(sK1,X46)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f74651,plain,
    ( ! [X46] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(X46,sK1),k3_xboole_0(sK1,X46)) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f74571])).

fof(f74571,plain,
    ( ! [X46] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(X46,sK1),k3_xboole_0(sK1,X46)) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f74193])).

fof(f74193,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(X1,sK1),k3_xboole_0(sK1,X1)))
    | ~ spl8_27 ),
    inference(superposition,[],[f74022,f200])).

fof(f73851,plain,
    ( spl8_1
    | spl8_89
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f8221,f5487,f73849,f82])).

fof(f73849,plain,
    ( spl8_89
  <=> ! [X16] :
        ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(X16,sK1))
        | k1_xboole_0 = k3_xboole_0(sK1,X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f8221,plain,
    ( ! [X16] :
        ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(X16,sK1))
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,X16) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f8106])).

fof(f73505,plain,
    ( spl8_88
    | spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f72797,f5487,f82,f73503])).

fof(f73503,plain,
    ( spl8_88
  <=> ! [X104,X103] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X103),k4_xboole_0(X104,k3_xboole_0(X103,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f72797,plain,
    ( ! [X103,X104] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X103),k4_xboole_0(X104,k3_xboole_0(X103,sK1))) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f72717])).

fof(f72717,plain,
    ( ! [X103,X104] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X103),k4_xboole_0(X104,k3_xboole_0(X103,sK1))) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f72509])).

fof(f72509,plain,
    ( ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(X1,k3_xboole_0(X0,sK1))))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f72370,f50])).

fof(f72370,plain,
    ( ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X1,k3_xboole_0(X0,sK1)),k3_xboole_0(sK1,X0)))
    | ~ spl8_27 ),
    inference(superposition,[],[f8197,f1217])).

fof(f8197,plain,
    ( ! [X33,X31,X32] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,X31)),k2_zfmisc_1(X32,k4_xboole_0(X33,k3_xboole_0(X31,sK1))))
    | ~ spl8_27 ),
    inference(superposition,[],[f876,f8106])).

fof(f73319,plain,
    ( spl8_87
    | spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f73153,f5487,f82,f73317])).

fof(f73317,plain,
    ( spl8_87
  <=> ! [X44] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X44),k3_xboole_0(X44,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f73153,plain,
    ( ! [X44] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X44),k3_xboole_0(X44,sK1)) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f73073])).

fof(f73073,plain,
    ( ! [X44] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X44),k3_xboole_0(X44,sK1)) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f72676])).

fof(f72676,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X0,sK1)))
    | ~ spl8_27 ),
    inference(superposition,[],[f72509,f200])).

fof(f71580,plain,
    ( spl8_1
    | spl8_86
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f8190,f5487,f71578,f82])).

fof(f71578,plain,
    ( spl8_86
  <=> ! [X16] :
        ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X16))
        | k1_xboole_0 = k3_xboole_0(X16,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f8190,plain,
    ( ! [X16] :
        ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X16))
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(X16,sK1) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f8106])).

fof(f56282,plain,
    ( spl8_85
    | spl8_1
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f55723,f5487,f1506,f82,f56280])).

fof(f56280,plain,
    ( spl8_85
  <=> ! [X57] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f1506,plain,
    ( spl8_11
  <=> ! [X2] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f55723,plain,
    ( ! [X57] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK3)) )
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f55661])).

fof(f55661,plain,
    ( ! [X57] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK3)) )
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f55528])).

fof(f55528,plain,
    ( ! [X6] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X6,sK3)))
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f55412,f50])).

fof(f55412,plain,
    ( ! [X6] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X6,sK3),k3_xboole_0(sK1,sK3)))
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(superposition,[],[f55232,f1217])).

fof(f55232,plain,
    ( ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK3)))
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f55204,f48])).

fof(f55204,plain,
    ( ! [X2,X3] : k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK3))) = k3_xboole_0(k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK3))),k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(resolution,[],[f53005,f51])).

fof(f53005,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X0,sK3))),k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f52945,f73])).

fof(f52945,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X0,sK3))),k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(superposition,[],[f6686,f1507])).

fof(f1507,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f6686,plain,
    ( ! [X41,X40] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X41,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,X40)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X40)))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f6661,f72])).

fof(f6661,plain,
    ( ! [X41,X40] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X41,sK0),k3_xboole_0(k3_xboole_0(sK1,sK3),X40)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X40)))
    | ~ spl8_27 ),
    inference(superposition,[],[f3580,f5512])).

fof(f3580,plain,(
    ! [X64,X65,X63] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X63,X65),X64),k2_zfmisc_1(X65,X64)) ),
    inference(superposition,[],[f232,f850])).

fof(f850,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f72,f49])).

fof(f56163,plain,
    ( spl8_84
    | spl8_1
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f56049,f55964,f82,f56160])).

fof(f56160,plain,
    ( spl8_84
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f55964,plain,
    ( spl8_83
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f56049,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)
    | ~ spl8_83 ),
    inference(trivial_inequality_removal,[],[f55987])).

fof(f55987,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)
    | ~ spl8_83 ),
    inference(superposition,[],[f55,f55966])).

fof(f55966,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK3))
    | ~ spl8_83 ),
    inference(avatar_component_clause,[],[f55964])).

fof(f55967,plain,
    ( spl8_83
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f55628,f5487,f1506,f55964])).

fof(f55628,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK3))
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(superposition,[],[f55528,f200])).

fof(f53775,plain,
    ( spl8_82
    | spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f53528,f5487,f82,f51997])).

fof(f51997,plain,
    ( spl8_82
  <=> ! [X116] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X116,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f53528,plain,
    ( ! [X57] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK1)) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f53466])).

fof(f53466,plain,
    ( ! [X57] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK1)) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f53329])).

fof(f53329,plain,
    ( ! [X6] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X6,sK1)))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f53211,f50])).

fof(f53211,plain,
    ( ! [X6] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X6,sK1),k3_xboole_0(sK1,sK3)))
    | ~ spl8_27 ),
    inference(superposition,[],[f53045,f1217])).

fof(f53045,plain,
    ( ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK1)))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f53015,f48])).

fof(f53015,plain,
    ( ! [X2,X3] : k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK1))) = k3_xboole_0(k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK1))),k1_xboole_0)
    | ~ spl8_27 ),
    inference(resolution,[],[f53008,f51])).

fof(f53008,plain,
    ( ! [X15,X16] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X16,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X15,sK1))),k1_xboole_0)
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f52953,f73])).

fof(f52953,plain,
    ( ! [X15,X16] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X16,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X15,sK1))),k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_27 ),
    inference(superposition,[],[f6686,f581])).

fof(f51999,plain,
    ( spl8_82
    | spl8_81
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f51860,f5487,f51615,f51997])).

fof(f51860,plain,
    ( ! [X116,X115] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X115)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X116,sK1)) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f51798])).

fof(f51798,plain,
    ( ! [X116,X115] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k4_xboole_0(sK0,X115)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X116,sK1)) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f51375])).

fof(f51375,plain,
    ( ! [X2,X3] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,X2),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X3,sK1)))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f51361,f48])).

fof(f51361,plain,
    ( ! [X2,X3] : k2_zfmisc_1(k4_xboole_0(sK0,X2),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X3,sK1))) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,X2),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X3,sK1))),k1_xboole_0)
    | ~ spl8_27 ),
    inference(resolution,[],[f51353,f51])).

fof(f51353,plain,
    ( ! [X15,X16] : r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,X16),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X15,sK1))),k1_xboole_0)
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f51324,f73])).

fof(f51324,plain,
    ( ! [X15,X16] : r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,X16),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X15,sK1))),k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_27 ),
    inference(superposition,[],[f6663,f581])).

fof(f6663,plain,
    ( ! [X45,X44] : r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,X45),k3_xboole_0(k3_xboole_0(sK1,sK3),X44)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X44)))
    | ~ spl8_27 ),
    inference(superposition,[],[f3655,f5512])).

fof(f3655,plain,(
    ! [X30,X28,X29] : r1_tarski(k2_zfmisc_1(k4_xboole_0(X28,X29),X30),k2_zfmisc_1(X28,X30)) ),
    inference(superposition,[],[f3580,f196])).

fof(f51617,plain,
    ( spl8_80
    | spl8_81
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f51519,f5487,f51615,f51611])).

fof(f51611,plain,
    ( spl8_80
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f51519,plain,
    ( ! [X43] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X43)
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f51457])).

fof(f51457,plain,
    ( ! [X43] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k4_xboole_0(sK0,X43)
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f51413])).

fof(f51413,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,X1),k4_xboole_0(k3_xboole_0(sK1,sK3),sK1))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f51409,f48])).

fof(f51409,plain,
    ( ! [X1] : k2_zfmisc_1(k4_xboole_0(sK0,X1),k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,X1),k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)),k1_xboole_0)
    | ~ spl8_27 ),
    inference(resolution,[],[f51374,f51])).

fof(f51374,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,X0),k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)),k1_xboole_0)
    | ~ spl8_27 ),
    inference(superposition,[],[f51353,f200])).

fof(f50887,plain,
    ( spl8_79
    | spl8_1
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f50800,f5487,f1506,f82,f50885])).

fof(f50885,plain,
    ( spl8_79
  <=> ! [X43] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X43) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f50800,plain,
    ( ! [X43] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X43) )
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f50738])).

fof(f50738,plain,
    ( ! [X43] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X43) )
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f50703])).

fof(f50703,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X1))
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f50701,f48])).

fof(f50701,plain,
    ( ! [X1] : k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X1)) = k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X1)),k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(resolution,[],[f50670,f51])).

fof(f50670,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X0)),k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(superposition,[],[f49795,f200])).

fof(f49795,plain,
    ( ! [X0,X1] : r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X0,sK3)),X1)),k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f49766,f73])).

fof(f49766,plain,
    ( ! [X0,X1] : r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X0,sK3)),X1)),k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_11
    | ~ spl8_27 ),
    inference(superposition,[],[f6660,f1507])).

fof(f6660,plain,
    ( ! [X39,X38] : r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),X38),X39)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X38)))
    | ~ spl8_27 ),
    inference(superposition,[],[f1282,f5512])).

fof(f1282,plain,(
    ! [X30,X28,X29] : r1_tarski(k2_zfmisc_1(X30,k4_xboole_0(X28,X29)),k2_zfmisc_1(X30,X28)) ),
    inference(superposition,[],[f1235,f196])).

fof(f1235,plain,(
    ! [X54,X55,X53] : r1_tarski(k2_zfmisc_1(X53,k3_xboole_0(X54,X55)),k2_zfmisc_1(X53,X55)) ),
    inference(superposition,[],[f232,f837])).

fof(f50435,plain,
    ( spl8_78
    | spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f50329,f5487,f82,f50433])).

fof(f50433,plain,
    ( spl8_78
  <=> ! [X77,X78] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X77,sK1)),X78) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f50329,plain,
    ( ! [X78,X77] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X77,sK1)),X78) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f50267])).

fof(f50267,plain,
    ( ! [X78,X77] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X77,sK1)),X78) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f49819])).

fof(f49819,plain,
    ( ! [X2,X3] : k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X2,sK1)),X3))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f49810,f48])).

fof(f49810,plain,
    ( ! [X2,X3] : k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X2,sK1)),X3)) = k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X2,sK1)),X3)),k1_xboole_0)
    | ~ spl8_27 ),
    inference(resolution,[],[f49802,f51])).

fof(f49802,plain,
    ( ! [X15,X16] : r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X15,sK1)),X16)),k1_xboole_0)
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f49774,f73])).

fof(f49774,plain,
    ( ! [X15,X16] : r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X15,sK1)),X16)),k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_27 ),
    inference(superposition,[],[f6660,f581])).

fof(f50028,plain,
    ( spl8_77
    | spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f49941,f5487,f82,f50026])).

fof(f50026,plain,
    ( spl8_77
  <=> ! [X43] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X43) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f49941,plain,
    ( ! [X43] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X43) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f49879])).

fof(f49879,plain,
    ( ! [X43] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X43) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f49844])).

fof(f49844,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X1))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f49842,f48])).

fof(f49842,plain,
    ( ! [X1] : k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X1)) = k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X1)),k1_xboole_0)
    | ~ spl8_27 ),
    inference(resolution,[],[f49817,f51])).

fof(f49817,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X0)),k1_xboole_0)
    | ~ spl8_27 ),
    inference(superposition,[],[f49802,f200])).

fof(f48686,plain,
    ( spl8_76
    | spl8_8
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f29262,f5431,f171,f48684])).

fof(f48684,plain,
    ( spl8_76
  <=> ! [X52] : r2_hidden(sK7(X52,k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f171,plain,
    ( spl8_8
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f5431,plain,
    ( spl8_25
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f29262,plain,
    ( ! [X52] :
        ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
        | r2_hidden(sK7(X52,k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) )
    | ~ spl8_25 ),
    inference(resolution,[],[f29241,f5437])).

fof(f5437,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X1,k2_zfmisc_1(sK0,sK3)) )
    | ~ spl8_25 ),
    inference(superposition,[],[f3574,f5433])).

fof(f5433,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f5431])).

fof(f3574,plain,(
    ! [X43,X41,X42,X40] :
      ( ~ r2_hidden(X43,k2_zfmisc_1(k3_xboole_0(X40,X42),X41))
      | r2_hidden(X43,k2_zfmisc_1(X40,X41)) ) ),
    inference(superposition,[],[f80,f850])).

fof(f46558,plain,
    ( spl8_75
    | spl8_8
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f12074,f5431,f171,f46556])).

fof(f46556,plain,
    ( spl8_75
  <=> ! [X51] : r2_hidden(sK7(k1_xboole_0,X51,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f12074,plain,
    ( ! [X51] :
        ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
        | r2_hidden(sK7(k1_xboole_0,X51,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) )
    | ~ spl8_25 ),
    inference(resolution,[],[f12056,f5437])).

fof(f46164,plain,
    ( spl8_2
    | spl8_74
    | ~ spl8_17
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f46083,f8778,f3967,f46162,f87])).

fof(f8778,plain,
    ( spl8_36
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f46083,plain,
    ( ! [X48] :
        ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X48)
        | k1_xboole_0 = sK1 )
    | ~ spl8_17
    | ~ spl8_36 ),
    inference(trivial_inequality_removal,[],[f46025])).

fof(f46025,plain,
    ( ! [X48] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X48)
        | k1_xboole_0 = sK1 )
    | ~ spl8_17
    | ~ spl8_36 ),
    inference(superposition,[],[f55,f45985])).

fof(f45985,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X1),sK1)
    | ~ spl8_17
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f45983,f48])).

fof(f45983,plain,
    ( ! [X1] : k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X1),sK1) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X1),sK1),k1_xboole_0)
    | ~ spl8_17
    | ~ spl8_36 ),
    inference(resolution,[],[f45961,f51])).

fof(f45961,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X0),sK1),k1_xboole_0)
    | ~ spl8_17
    | ~ spl8_36 ),
    inference(superposition,[],[f45132,f200])).

fof(f45132,plain,
    ( ! [X0,X1] : r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X0,sK2)),X1),sK1),k1_xboole_0)
    | ~ spl8_17
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f45100,f74])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45100,plain,
    ( ! [X0,X1] : r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X0,sK2)),X1),sK1),k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl8_17
    | ~ spl8_36 ),
    inference(superposition,[],[f9049,f3968])).

fof(f9049,plain,
    ( ! [X43,X44] : r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),X43),X44),sK1),k2_zfmisc_1(k3_xboole_0(sK0,X43),sK1))
    | ~ spl8_36 ),
    inference(superposition,[],[f3655,f8819])).

fof(f8819,plain,
    ( ! [X8] : k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X8),sK1)
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f8793,f850])).

fof(f8793,plain,
    ( ! [X8] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,sK1)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK1)
    | ~ spl8_36 ),
    inference(superposition,[],[f850,f8780])).

fof(f8780,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f8778])).

fof(f45742,plain,
    ( spl8_2
    | spl8_73
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f45648,f8778,f45740,f87])).

fof(f45740,plain,
    ( spl8_73
  <=> ! [X87,X88] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X87,sK0)),X88) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f45648,plain,
    ( ! [X88,X87] :
        ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X87,sK0)),X88)
        | k1_xboole_0 = sK1 )
    | ~ spl8_36 ),
    inference(trivial_inequality_removal,[],[f45590])).

fof(f45590,plain,
    ( ! [X88,X87] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X87,sK0)),X88)
        | k1_xboole_0 = sK1 )
    | ~ spl8_36 ),
    inference(superposition,[],[f55,f45161])).

fof(f45161,plain,
    ( ! [X2,X3] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X2,sK0)),X3),sK1)
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f45155,f48])).

fof(f45155,plain,
    ( ! [X2,X3] : k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X2,sK0)),X3),sK1) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X2,sK0)),X3),sK1),k1_xboole_0)
    | ~ spl8_36 ),
    inference(resolution,[],[f45139,f51])).

fof(f45139,plain,
    ( ! [X15,X16] : r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X15,sK0)),X16),sK1),k1_xboole_0)
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f45108,f74])).

fof(f45108,plain,
    ( ! [X15,X16] : r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X15,sK0)),X16),sK1),k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl8_36 ),
    inference(superposition,[],[f9049,f581])).

fof(f45356,plain,
    ( spl8_2
    | spl8_72
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f45275,f8778,f45354,f87])).

fof(f45275,plain,
    ( ! [X48] :
        ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X48)
        | k1_xboole_0 = sK1 )
    | ~ spl8_36 ),
    inference(trivial_inequality_removal,[],[f45217])).

fof(f45217,plain,
    ( ! [X48] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X48)
        | k1_xboole_0 = sK1 )
    | ~ spl8_36 ),
    inference(superposition,[],[f55,f45177])).

fof(f45177,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X1),sK1)
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f45175,f48])).

fof(f45175,plain,
    ( ! [X1] : k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X1),sK1) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X1),sK1),k1_xboole_0)
    | ~ spl8_36 ),
    inference(resolution,[],[f45159,f51])).

fof(f45159,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X0),sK1),k1_xboole_0)
    | ~ spl8_36 ),
    inference(superposition,[],[f45139,f200])).

fof(f44943,plain,
    ( spl8_71
    | spl8_8
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f6336,f5431,f171,f44941])).

fof(f44941,plain,
    ( spl8_71
  <=> ! [X51] : r2_hidden(sK6(X51,X51,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f6336,plain,
    ( ! [X51] :
        ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
        | r2_hidden(sK6(X51,X51,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) )
    | ~ spl8_25 ),
    inference(resolution,[],[f6317,f5437])).

fof(f44939,plain,
    ( spl8_6
    | spl8_70
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f5793,f101,f44937,f163])).

fof(f44937,plain,
    ( spl8_70
  <=> ! [X19] :
        ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(X19,sK2),sK3)
        | k1_xboole_0 = k3_xboole_0(sK2,X19) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f101,plain,
    ( spl8_5
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f5793,plain,
    ( ! [X19] :
        ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(X19,sK2),sK3)
        | k1_xboole_0 = k3_xboole_0(sK2,X19)
        | k1_xboole_0 = sK3 )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f5674])).

fof(f5674,plain,
    ( ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3)
    | ~ spl8_5 ),
    inference(superposition,[],[f4579,f3538])).

fof(f3538,plain,
    ( ! [X9] : k2_zfmisc_1(k3_xboole_0(X9,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_5 ),
    inference(superposition,[],[f850,f103])).

fof(f103,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f4579,plain,
    ( ! [X4] : k3_xboole_0(k2_zfmisc_1(X4,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK2,X4),sK3)
    | ~ spl8_5 ),
    inference(superposition,[],[f3532,f50])).

fof(f3532,plain,
    ( ! [X9] : k2_zfmisc_1(k3_xboole_0(sK2,X9),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK3))
    | ~ spl8_5 ),
    inference(superposition,[],[f850,f103])).

fof(f44930,plain,
    ( ~ spl8_69
    | spl8_7
    | ~ spl8_5
    | ~ spl8_18
    | ~ spl8_34
    | ~ spl8_36
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f44430,f44400,f8778,f8638,f4031,f101,f167,f44927])).

fof(f4031,plain,
    ( spl8_18
  <=> k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f8638,plain,
    ( spl8_34
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f44400,plain,
    ( spl8_68
  <=> ! [X19] :
        ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK2,X19),sK3)
        | k1_xboole_0 = k3_xboole_0(X19,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f44430,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl8_5
    | ~ spl8_18
    | ~ spl8_34
    | ~ spl8_36
    | ~ spl8_68 ),
    inference(forward_demodulation,[],[f44413,f49])).

fof(f44413,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | k1_xboole_0 = k3_xboole_0(sK2,sK2)
    | ~ spl8_5
    | ~ spl8_18
    | ~ spl8_34
    | ~ spl8_36
    | ~ spl8_68 ),
    inference(superposition,[],[f44401,f40263])).

fof(f40263,plain,
    ( ! [X2] : k2_zfmisc_1(k3_xboole_0(X2,sK2),sK3) = k2_zfmisc_1(k3_xboole_0(sK0,X2),sK1)
    | ~ spl8_5
    | ~ spl8_18
    | ~ spl8_34
    | ~ spl8_36 ),
    inference(superposition,[],[f34284,f50])).

fof(f34284,plain,
    ( ! [X1] : k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k2_zfmisc_1(k3_xboole_0(sK0,X1),sK1)
    | ~ spl8_5
    | ~ spl8_18
    | ~ spl8_34
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f34156,f8820])).

fof(f8820,plain,
    ( ! [X6] : k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(X6,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,X6),sK1)
    | ~ spl8_18
    | ~ spl8_36 ),
    inference(backward_demodulation,[],[f4057,f8819])).

fof(f4057,plain,
    ( ! [X6] : k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X6),sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(X6,sK3))
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f4042,f880])).

fof(f880,plain,(
    ! [X37,X35,X36,X34] : k3_xboole_0(k2_zfmisc_1(X36,k3_xboole_0(X34,X35)),k2_zfmisc_1(X37,X34)) = k3_xboole_0(k2_zfmisc_1(X36,X34),k2_zfmisc_1(X37,X35)) ),
    inference(forward_demodulation,[],[f859,f72])).

fof(f859,plain,(
    ! [X37,X35,X36,X34] : k3_xboole_0(k2_zfmisc_1(X36,k3_xboole_0(X34,X35)),k2_zfmisc_1(X37,X34)) = k2_zfmisc_1(k3_xboole_0(X36,X37),k3_xboole_0(X34,X35)) ),
    inference(superposition,[],[f72,f245])).

fof(f245,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f238,f51])).

fof(f4042,plain,
    ( ! [X6] : k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X6),sK1) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X6,sK1))
    | ~ spl8_18 ),
    inference(superposition,[],[f850,f4033])).

fof(f4033,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f4031])).

fof(f34156,plain,
    ( ! [X1] : k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(X1,sK3))
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(superposition,[],[f8722,f72])).

fof(f8722,plain,
    ( ! [X24] : k2_zfmisc_1(k3_xboole_0(sK2,X24),sK3) = k2_zfmisc_1(k3_xboole_0(sK2,X24),k3_xboole_0(sK1,sK3))
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f8721,f3532])).

fof(f8721,plain,
    ( ! [X24] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X24,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,X24),k3_xboole_0(sK1,sK3))
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f8675,f875])).

fof(f875,plain,(
    ! [X17,X15,X18,X16] : k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,k3_xboole_0(X15,X16))) = k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,X16)) ),
    inference(forward_demodulation,[],[f854,f72])).

fof(f854,plain,(
    ! [X17,X15,X18,X16] : k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,k3_xboole_0(X15,X16))) = k2_zfmisc_1(k3_xboole_0(X17,X18),k3_xboole_0(X15,X16)) ),
    inference(superposition,[],[f72,f281])).

fof(f281,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f245,f50])).

fof(f8675,plain,
    ( ! [X24] : k2_zfmisc_1(k3_xboole_0(sK2,X24),k3_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X24,k3_xboole_0(sK1,sK3)))
    | ~ spl8_34 ),
    inference(superposition,[],[f850,f8640])).

fof(f8640,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f8638])).

fof(f44401,plain,
    ( ! [X19] :
        ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK2,X19),sK3)
        | k1_xboole_0 = k3_xboole_0(X19,sK2) )
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f44400])).

fof(f44402,plain,
    ( spl8_6
    | spl8_68
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f5767,f101,f44400,f163])).

fof(f5767,plain,
    ( ! [X19] :
        ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK2,X19),sK3)
        | k1_xboole_0 = k3_xboole_0(X19,sK2)
        | k1_xboole_0 = sK3 )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f5674])).

fof(f44390,plain,
    ( spl8_8
    | spl8_67
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f5537,f5431,f44388,f171])).

fof(f44388,plain,
    ( spl8_67
  <=> ! [X20] : r2_hidden(sK6(k1_xboole_0,X20,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f5537,plain,
    ( ! [X20] :
        ( r2_hidden(sK6(k1_xboole_0,X20,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) )
    | ~ spl8_25 ),
    inference(resolution,[],[f5437,f2344])).

fof(f44386,plain,
    ( spl8_7
    | spl8_66
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f3065,f101,f44384,f167])).

fof(f44384,plain,
    ( spl8_66
  <=> ! [X13] :
        ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(X13,sK3))
        | k1_xboole_0 = k3_xboole_0(sK3,X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f3065,plain,
    ( ! [X13] :
        ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(X13,sK3))
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,X13) )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f2982])).

fof(f2982,plain,
    ( ! [X1] : k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,X1))
    | ~ spl8_5 ),
    inference(superposition,[],[f2930,f1207])).

fof(f1207,plain,
    ( ! [X9] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X9)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9))
    | ~ spl8_5 ),
    inference(superposition,[],[f837,f103])).

fof(f2930,plain,
    ( ! [X3] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X3)) = k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3))
    | ~ spl8_5 ),
    inference(superposition,[],[f1211,f50])).

fof(f1211,plain,
    ( ! [X9] : k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_5 ),
    inference(superposition,[],[f837,f103])).

fof(f43883,plain,
    ( spl8_6
    | ~ spl8_65
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f43853,f43848,f43880,f163])).

fof(f43848,plain,
    ( spl8_64
  <=> ! [X13] :
        ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK3,X13))
        | k1_xboole_0 = k3_xboole_0(X13,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f43853,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    | k1_xboole_0 = sK3
    | ~ spl8_64 ),
    inference(superposition,[],[f43849,f49])).

fof(f43849,plain,
    ( ! [X13] :
        ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK3,X13))
        | k1_xboole_0 = k3_xboole_0(X13,sK3) )
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f43848])).

fof(f43850,plain,
    ( spl8_7
    | spl8_64
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f3046,f101,f43848,f167])).

fof(f3046,plain,
    ( ! [X13] :
        ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK3,X13))
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(X13,sK3) )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f2982])).

fof(f42537,plain,
    ( spl8_6
    | spl8_61
    | ~ spl8_63
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f4865,f4853,f42532,f42502,f163])).

fof(f42502,plain,
    ( spl8_61
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f42532,plain,
    ( spl8_63
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f4853,plain,
    ( spl8_23
  <=> k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f4865,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ spl8_23 ),
    inference(superposition,[],[f55,f4855])).

fof(f4855,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f4853])).

fof(f42535,plain,
    ( ~ spl8_63
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_56
    | spl8_62 ),
    inference(avatar_split_clause,[],[f42527,f42506,f35009,f5431,f4853,f101,f42532])).

fof(f35009,plain,
    ( spl8_56
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f42506,plain,
    ( spl8_62
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f42527,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_56
    | spl8_62 ),
    inference(superposition,[],[f42508,f40709])).

fof(f40709,plain,
    ( ! [X0] : k2_zfmisc_1(sK0,k3_xboole_0(sK1,X0)) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,X0))
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_56 ),
    inference(superposition,[],[f35621,f50])).

fof(f35621,plain,
    ( ! [X19] : k2_zfmisc_1(sK0,k3_xboole_0(X19,sK1)) = k2_zfmisc_1(sK2,k3_xboole_0(X19,sK1))
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_56 ),
    inference(forward_demodulation,[],[f35558,f14170])).

fof(f14170,plain,
    ( ! [X9] : k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(X9,sK1))
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(backward_demodulation,[],[f1211,f14169])).

fof(f14169,plain,
    ( ! [X3] : k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1))
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(backward_demodulation,[],[f2930,f14044])).

fof(f14044,plain,
    ( ! [X9] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9)) = k2_zfmisc_1(sK0,k3_xboole_0(X9,sK1))
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(backward_demodulation,[],[f1207,f14043])).

fof(f14043,plain,
    ( ! [X7] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X7)) = k2_zfmisc_1(sK0,k3_xboole_0(X7,sK1))
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f14042,f5377])).

fof(f5377,plain,
    ( ! [X7] : k2_zfmisc_1(sK0,k3_xboole_0(X7,sK1)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(backward_demodulation,[],[f4888,f5366])).

fof(f5366,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f5365,f103])).

fof(f5365,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f5364,f49])).

fof(f5364,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f5363,f1240])).

fof(f1240,plain,(
    ! [X70,X68,X69] : k2_zfmisc_1(X68,k3_xboole_0(X69,X70)) = k3_xboole_0(k2_zfmisc_1(X68,k3_xboole_0(X69,X70)),k2_zfmisc_1(X68,X69)) ),
    inference(superposition,[],[f245,f837])).

fof(f5363,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f5310,f4890])).

fof(f4890,plain,
    ( ! [X8] : k2_zfmisc_1(k3_xboole_0(sK2,X8),sK3) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3)
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4889,f3532])).

fof(f4889,plain,
    ( ! [X8] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,sK3)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3)
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4868,f879])).

fof(f879,plain,(
    ! [X30,X33,X31,X32] : k3_xboole_0(k2_zfmisc_1(X32,k3_xboole_0(X30,X31)),k2_zfmisc_1(X33,X31)) = k3_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X33,X31)) ),
    inference(forward_demodulation,[],[f858,f72])).

fof(f858,plain,(
    ! [X30,X33,X31,X32] : k3_xboole_0(k2_zfmisc_1(X32,k3_xboole_0(X30,X31)),k2_zfmisc_1(X33,X31)) = k2_zfmisc_1(k3_xboole_0(X32,X33),k3_xboole_0(X30,X31)) ),
    inference(superposition,[],[f72,f236])).

fof(f236,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f232,f51])).

fof(f4868,plain,
    ( ! [X8] : k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X8,sK3))
    | ~ spl8_23 ),
    inference(superposition,[],[f850,f4855])).

fof(f5310,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3)
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(superposition,[],[f3538,f4855])).

fof(f4888,plain,
    ( ! [X7] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(sK0,k3_xboole_0(X7,sK1))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4887,f837])).

fof(f4887,plain,
    ( ! [X7] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4886,f103])).

fof(f4886,plain,
    ( ! [X7] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK2,sK3))
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4867,f72])).

fof(f4867,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X7,sK3)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl8_23 ),
    inference(superposition,[],[f837,f4855])).

fof(f14042,plain,
    ( ! [X7] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X7)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f14041,f5400])).

fof(f5400,plain,
    ( ! [X6] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X6))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f5399,f1207])).

fof(f5399,plain,
    ( ! [X6] : k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f5376,f865])).

fof(f865,plain,(
    ! [X17,X15,X18,X16] : k3_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(k3_xboole_0(X15,X16),X18)) = k3_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18)) ),
    inference(forward_demodulation,[],[f841,f72])).

fof(f841,plain,(
    ! [X17,X15,X18,X16] : k3_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(k3_xboole_0(X15,X16),X18)) = k2_zfmisc_1(k3_xboole_0(X15,X16),k3_xboole_0(X17,X18)) ),
    inference(superposition,[],[f72,f281])).

fof(f5376,plain,
    ( ! [X6] : k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(backward_demodulation,[],[f4885,f5366])).

fof(f4885,plain,
    ( ! [X6] : k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X6))
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4866,f72])).

fof(f4866,plain,
    ( ! [X6] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6))
    | ~ spl8_23 ),
    inference(superposition,[],[f837,f4855])).

fof(f14041,plain,
    ( ! [X7] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X7))
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f13878,f72])).

fof(f13878,plain,
    ( ! [X7] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X7))
    | ~ spl8_25 ),
    inference(superposition,[],[f1217,f5433])).

fof(f35558,plain,
    ( ! [X19] : k3_xboole_0(k2_zfmisc_1(sK2,X19),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,k3_xboole_0(X19,sK1))
    | ~ spl8_56 ),
    inference(superposition,[],[f837,f35011])).

fof(f35011,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f35009])).

fof(f42508,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))
    | spl8_62 ),
    inference(avatar_component_clause,[],[f42506])).

fof(f42509,plain,
    ( spl8_2
    | spl8_61
    | ~ spl8_62
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f4039,f4031,f42506,f42502,f87])).

fof(f4039,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1
    | ~ spl8_18 ),
    inference(superposition,[],[f55,f4033])).

fof(f37002,plain,
    ( ~ spl8_60
    | ~ spl8_56
    | spl8_57 ),
    inference(avatar_split_clause,[],[f35266,f35016,f35009,f36999])).

fof(f36999,plain,
    ( spl8_60
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f35016,plain,
    ( spl8_57
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f35266,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_56
    | spl8_57 ),
    inference(backward_demodulation,[],[f35018,f35011])).

fof(f35018,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl8_57 ),
    inference(avatar_component_clause,[],[f35016])).

fof(f35720,plain,
    ( ~ spl8_59
    | spl8_55
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f35542,f35009,f35005,f35717])).

fof(f35717,plain,
    ( spl8_59
  <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f35005,plain,
    ( spl8_55
  <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f35542,plain,
    ( ~ r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | spl8_55
    | ~ spl8_56 ),
    inference(forward_demodulation,[],[f35006,f35011])).

fof(f35006,plain,
    ( ~ r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | spl8_55 ),
    inference(avatar_component_clause,[],[f35005])).

fof(f35024,plain,
    ( spl8_58
    | ~ spl8_55 ),
    inference(avatar_split_clause,[],[f35014,f35005,f35021])).

fof(f35021,plain,
    ( spl8_58
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f35014,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1))
    | ~ spl8_55 ),
    inference(resolution,[],[f35007,f58])).

fof(f35007,plain,
    ( r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f35005])).

fof(f35019,plain,
    ( ~ spl8_57
    | ~ spl8_55 ),
    inference(avatar_split_clause,[],[f35013,f35005,f35016])).

fof(f35013,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_55 ),
    inference(resolution,[],[f35007,f59])).

fof(f35012,plain,
    ( spl8_55
    | spl8_56
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f8757,f8753,f35009,f35005])).

fof(f8753,plain,
    ( spl8_35
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f8757,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl8_35 ),
    inference(resolution,[],[f8755,f52])).

fof(f8755,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f8753])).

fof(f34059,plain,
    ( ~ spl8_54
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f34053,f34046,f34056])).

fof(f34056,plain,
    ( spl8_54
  <=> r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f34053,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)
    | ~ spl8_53 ),
    inference(superposition,[],[f34052,f47])).

fof(f34052,plain,
    ( ! [X2] : ~ r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k4_xboole_0(X2,k2_zfmisc_1(sK0,sK3)))
    | ~ spl8_53 ),
    inference(resolution,[],[f34048,f76])).

fof(f34049,plain,
    ( spl8_8
    | spl8_53
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f5526,f5431,f34046,f171])).

fof(f5526,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_25 ),
    inference(resolution,[],[f5437,f143])).

fof(f33038,plain,
    ( ~ spl8_52
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f33032,f33025,f33035])).

fof(f33025,plain,
    ( spl8_51
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f33032,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k1_xboole_0)
    | ~ spl8_51 ),
    inference(superposition,[],[f33031,f47])).

fof(f33031,plain,
    ( ! [X2] : ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k4_xboole_0(X2,k2_zfmisc_1(sK0,sK3)))
    | ~ spl8_51 ),
    inference(resolution,[],[f33027,f76])).

fof(f33027,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f33025])).

fof(f33028,plain,
    ( spl8_51
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f33018,f33009,f33025])).

fof(f33009,plain,
    ( spl8_48
  <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f33018,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_48 ),
    inference(resolution,[],[f33011,f58])).

fof(f33011,plain,
    ( r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f33009])).

fof(f33023,plain,
    ( ~ spl8_50
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f33017,f33009,f33020])).

fof(f33020,plain,
    ( spl8_50
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f33017,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_48 ),
    inference(resolution,[],[f33011,f59])).

fof(f33016,plain,
    ( spl8_48
    | spl8_49
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f5484,f5480,f33013,f33009])).

fof(f5480,plain,
    ( spl8_26
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f5484,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)
    | r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_26 ),
    inference(resolution,[],[f5482,f52])).

fof(f5482,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f5480])).

fof(f13062,plain,
    ( spl8_6
    | spl8_47
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f11936,f9274,f101,f13060,f163])).

fof(f13060,plain,
    ( spl8_47
  <=> ! [X54] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X54,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f9274,plain,
    ( spl8_41
  <=> ! [X14] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f11936,plain,
    ( ! [X54] :
        ( k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X54,k3_xboole_0(sK0,sK2)))
        | k1_xboole_0 = sK3 )
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(trivial_inequality_removal,[],[f11910])).

fof(f11910,plain,
    ( ! [X54] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X54,k3_xboole_0(sK0,sK2)))
        | k1_xboole_0 = sK3 )
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(superposition,[],[f55,f11857])).

fof(f11857,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X3,k3_xboole_0(sK0,sK2))),sK3)
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(forward_demodulation,[],[f11801,f50])).

fof(f11801,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X3,k3_xboole_0(sK0,sK2)),sK2),sK3)
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(superposition,[],[f9335,f5318])).

fof(f5318,plain,
    ( ! [X4] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3)) = k2_zfmisc_1(k3_xboole_0(X4,sK2),sK3)
    | ~ spl8_5 ),
    inference(superposition,[],[f3538,f50])).

fof(f9335,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X5),k2_zfmisc_1(k4_xboole_0(X4,k3_xboole_0(sK0,sK2)),X6))
    | ~ spl8_41 ),
    inference(forward_demodulation,[],[f9296,f74])).

fof(f9296,plain,
    ( ! [X6,X4,X5] : k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X5,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,X5),k2_zfmisc_1(k4_xboole_0(X4,k3_xboole_0(sK0,sK2)),X6))
    | ~ spl8_41 ),
    inference(superposition,[],[f72,f9275])).

fof(f9275,plain,
    ( ! [X14] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f9274])).

fof(f12585,plain,
    ( spl8_46
    | spl8_7
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f9886,f5487,f101,f167,f12583])).

fof(f12583,plain,
    ( spl8_46
  <=> ! [X51] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X51,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f9886,plain,
    ( ! [X51] :
        ( k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X51,k3_xboole_0(sK1,sK3))) )
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f9862])).

fof(f9862,plain,
    ( ! [X51] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X51,k3_xboole_0(sK1,sK3))) )
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f9816])).

fof(f9816,plain,
    ( ! [X9] : k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X9,k3_xboole_0(sK1,sK3))))
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f9767,f50])).

fof(f9767,plain,
    ( ! [X9] : k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(X9,k3_xboole_0(sK1,sK3)),sK3))
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(superposition,[],[f5504,f2930])).

fof(f5504,plain,
    ( ! [X14,X15] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X14,k4_xboole_0(X15,k3_xboole_0(sK1,sK3))))
    | ~ spl8_27 ),
    inference(superposition,[],[f876,f5489])).

fof(f12173,plain,
    ( spl8_6
    | spl8_45
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f12125,f12007,f12170,f163])).

fof(f12007,plain,
    ( spl8_44
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f12125,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK3
    | ~ spl8_44 ),
    inference(trivial_inequality_removal,[],[f12099])).

fof(f12099,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK3
    | ~ spl8_44 ),
    inference(superposition,[],[f55,f12009])).

fof(f12009,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f12007])).

fof(f12010,plain,
    ( spl8_44
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f11875,f9274,f101,f12007])).

fof(f11875,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3)
    | ~ spl8_5
    | ~ spl8_41 ),
    inference(superposition,[],[f11857,f200])).

fof(f10045,plain,
    ( spl8_43
    | spl8_7
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f10001,f9954,f167,f10042])).

fof(f9954,plain,
    ( spl8_42
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f10001,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))
    | ~ spl8_42 ),
    inference(trivial_inequality_removal,[],[f9977])).

fof(f9977,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))
    | ~ spl8_42 ),
    inference(superposition,[],[f55,f9956])).

fof(f9956,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f9954])).

fof(f9957,plain,
    ( spl8_42
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f9832,f5487,f101,f9954])).

fof(f9832,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)))
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(superposition,[],[f9816,f200])).

fof(f9276,plain,
    ( spl8_2
    | spl8_41
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f9129,f8778,f9274,f87])).

fof(f9129,plain,
    ( ! [X14] :
        ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))
        | k1_xboole_0 = sK1 )
    | ~ spl8_36 ),
    inference(trivial_inequality_removal,[],[f9106])).

fof(f9106,plain,
    ( ! [X14] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))
        | k1_xboole_0 = sK1 )
    | ~ spl8_36 ),
    inference(superposition,[],[f55,f9063])).

fof(f9063,plain,
    ( ! [X5] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f9025,f74])).

fof(f9025,plain,
    ( ! [X5] : k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl8_36 ),
    inference(superposition,[],[f8819,f581])).

fof(f9212,plain,
    ( spl8_2
    | spl8_40
    | ~ spl8_39 ),
    inference(avatar_split_clause,[],[f9187,f9154,f9209,f87])).

fof(f9154,plain,
    ( spl8_39
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f9187,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1
    | ~ spl8_39 ),
    inference(trivial_inequality_removal,[],[f9164])).

fof(f9164,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1
    | ~ spl8_39 ),
    inference(superposition,[],[f55,f9156])).

fof(f9156,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f9154])).

fof(f9157,plain,
    ( spl8_39
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f9097,f8778,f9154])).

fof(f9097,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl8_36 ),
    inference(superposition,[],[f9063,f200])).

fof(f8906,plain,
    ( spl8_38
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f8872,f8843,f8903])).

fof(f8903,plain,
    ( spl8_38
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f8843,plain,
    ( spl8_37
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f8872,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_37 ),
    inference(superposition,[],[f261,f8845])).

fof(f8845,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f8843])).

fof(f261,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f236,f50])).

fof(f8846,plain,
    ( spl8_37
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f8758,f8753,f8843])).

fof(f8758,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl8_35 ),
    inference(resolution,[],[f8755,f51])).

fof(f8781,plain,
    ( spl8_36
    | ~ spl8_5
    | ~ spl8_18
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f8553,f7944,f4031,f101,f8778])).

fof(f7944,plain,
    ( spl8_33
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f8553,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl8_5
    | ~ spl8_18
    | ~ spl8_33 ),
    inference(backward_demodulation,[],[f4033,f8552])).

fof(f8552,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f8551,f261])).

fof(f8551,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k3_xboole_0(sK1,sK3)))
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f8507,f50])).

fof(f8507,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(k3_xboole_0(sK1,sK3),sK3))
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(superposition,[],[f7946,f2930])).

fof(f7946,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f7944])).

fof(f8756,plain,
    ( spl8_35
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f8670,f8638,f8753])).

fof(f8670,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl8_34 ),
    inference(superposition,[],[f1238,f8640])).

fof(f1238,plain,(
    ! [X64,X62,X63] : r1_tarski(k2_zfmisc_1(X62,k3_xboole_0(X63,X64)),k2_zfmisc_1(X62,X63)) ),
    inference(superposition,[],[f238,f837])).

fof(f8641,plain,
    ( spl8_34
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f8552,f7944,f101,f8638])).

fof(f7947,plain,
    ( spl8_33
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f4320,f4315,f7944])).

fof(f4315,plain,
    ( spl8_19
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f4320,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl8_19 ),
    inference(resolution,[],[f4317,f51])).

fof(f4317,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f4315])).

fof(f6850,plain,
    ( spl8_32
    | spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f6724,f5487,f82,f6848])).

fof(f6848,plain,
    ( spl8_32
  <=> ! [X15] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f6724,plain,
    ( ! [X15] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3))) )
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f6707])).

fof(f6707,plain,
    ( ! [X15] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3))) )
    | ~ spl8_27 ),
    inference(superposition,[],[f55,f6671])).

fof(f6671,plain,
    ( ! [X5] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK1,sK3))))
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f6638,f73])).

fof(f6638,plain,
    ( ! [X5] : k2_zfmisc_1(sK0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK1,sK3))))
    | ~ spl8_27 ),
    inference(superposition,[],[f5512,f581])).

fof(f6786,plain,
    ( spl8_31
    | spl8_1
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f6769,f6741,f82,f6783])).

fof(f6741,plain,
    ( spl8_30
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f6769,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl8_30 ),
    inference(trivial_inequality_removal,[],[f6752])).

fof(f6752,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl8_30 ),
    inference(superposition,[],[f55,f6743])).

fof(f6743,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f6741])).

fof(f6744,plain,
    ( spl8_30
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f6697,f5487,f6741])).

fof(f6697,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl8_27 ),
    inference(superposition,[],[f6671,f200])).

fof(f5599,plain,
    ( spl8_29
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f5572,f5549,f5596])).

fof(f5596,plain,
    ( spl8_29
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f5549,plain,
    ( spl8_28
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f5572,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_28 ),
    inference(superposition,[],[f261,f5551])).

fof(f5551,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f5549])).

fof(f5552,plain,
    ( spl8_28
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f5485,f5480,f5549])).

fof(f5485,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_26 ),
    inference(resolution,[],[f5482,f51])).

fof(f5490,plain,
    ( spl8_27
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f5366,f4853,f101,f5487])).

fof(f5483,plain,
    ( spl8_26
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f5439,f5431,f5480])).

fof(f5439,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl8_25 ),
    inference(superposition,[],[f3583,f5433])).

fof(f3583,plain,(
    ! [X74,X72,X73] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X72,X74),X73),k2_zfmisc_1(X72,X73)) ),
    inference(superposition,[],[f238,f850])).

fof(f5434,plain,
    ( spl8_25
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f5367,f4853,f101,f5431])).

fof(f5367,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(backward_demodulation,[],[f4855,f5366])).

fof(f5202,plain,
    ( spl8_24
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f5188,f4853,f101,f5199])).

fof(f5199,plain,
    ( spl8_24
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f5188,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(superposition,[],[f4894,f49])).

fof(f4894,plain,
    ( ! [X18] : r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(X18,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4893,f837])).

fof(f4893,plain,
    ( ! [X18] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X18),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4892,f103])).

fof(f4892,plain,
    ( ! [X18] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X18),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f4874,f72])).

fof(f4874,plain,
    ( ! [X18] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X18,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl8_23 ),
    inference(superposition,[],[f1235,f4855])).

fof(f4856,plain,
    ( spl8_23
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f4629,f101,f4853])).

fof(f4629,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f4573,f50])).

fof(f4573,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)
    | ~ spl8_5 ),
    inference(superposition,[],[f3532,f837])).

fof(f4785,plain,
    ( spl8_6
    | spl8_22
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f4665,f101,f4783,f163])).

fof(f4783,plain,
    ( spl8_22
  <=> ! [X14] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f4665,plain,
    ( ! [X14] :
        ( k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0))
        | k1_xboole_0 = sK3 )
    | ~ spl8_5 ),
    inference(trivial_inequality_removal,[],[f4650])).

fof(f4650,plain,
    ( ! [X14] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0))
        | k1_xboole_0 = sK3 )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f4576])).

fof(f4576,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X3,sK0)),sK3)
    | ~ spl8_5 ),
    inference(superposition,[],[f3532,f866])).

fof(f866,plain,(
    ! [X26,X24,X23,X25] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(k4_xboole_0(X24,X23),X26)) ),
    inference(forward_demodulation,[],[f843,f74])).

fof(f843,plain,(
    ! [X26,X24,X23,X25] : k3_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(k4_xboole_0(X24,X23),X26)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X25,X26)) ),
    inference(superposition,[],[f72,f581])).

fof(f4722,plain,
    ( spl8_6
    | spl8_21
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f4708,f4681,f4719,f163])).

fof(f4681,plain,
    ( spl8_20
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f4708,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | k1_xboole_0 = sK3
    | ~ spl8_20 ),
    inference(trivial_inequality_removal,[],[f4693])).

fof(f4693,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | k1_xboole_0 = sK3
    | ~ spl8_20 ),
    inference(superposition,[],[f55,f4683])).

fof(f4683,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f4681])).

fof(f4684,plain,
    ( spl8_20
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f4641,f101,f4681])).

fof(f4641,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)
    | ~ spl8_5 ),
    inference(superposition,[],[f4576,f200])).

fof(f4318,plain,
    ( spl8_19
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f4304,f4031,f101,f4315])).

fof(f4304,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(superposition,[],[f4064,f49])).

fof(f4064,plain,
    ( ! [X19] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X19,sK0),sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f4051,f4060])).

fof(f4060,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k2_zfmisc_1(k3_xboole_0(X7,sK0),sK1)
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f4059,f850])).

fof(f4059,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f4058,f103])).

fof(f4058,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f4043,f875])).

fof(f4043,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl8_18 ),
    inference(superposition,[],[f850,f4033])).

fof(f4051,plain,
    ( ! [X19] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X19,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))
    | ~ spl8_18 ),
    inference(superposition,[],[f3580,f4033])).

fof(f4034,plain,
    ( spl8_18
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f3624,f101,f4031])).

fof(f3624,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f3548,f50])).

fof(f3548,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1)
    | ~ spl8_5 ),
    inference(superposition,[],[f850,f1211])).

fof(f3969,plain,
    ( spl8_2
    | spl8_17
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f3854,f101,f3967,f87])).

fof(f3854,plain,
    ( ! [X8] :
        ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))
        | k1_xboole_0 = sK1 )
    | ~ spl8_5 ),
    inference(trivial_inequality_removal,[],[f3839])).

fof(f3839,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))
        | k1_xboole_0 = sK1 )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f3544])).

fof(f3544,plain,
    ( ! [X11] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X11,sK2)),sK1)
    | ~ spl8_5 ),
    inference(superposition,[],[f850,f887])).

fof(f887,plain,
    ( ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X12,sK2),X13))
    | ~ spl8_5 ),
    inference(superposition,[],[f866,f103])).

fof(f3906,plain,
    ( spl8_2
    | spl8_16
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f3893,f3867,f3903,f87])).

fof(f3867,plain,
    ( spl8_15
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f3893,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1
    | ~ spl8_15 ),
    inference(trivial_inequality_removal,[],[f3878])).

fof(f3878,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1
    | ~ spl8_15 ),
    inference(superposition,[],[f55,f3869])).

fof(f3869,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f3867])).

fof(f3870,plain,
    ( spl8_15
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f3834,f101,f3867])).

fof(f3834,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl8_5 ),
    inference(superposition,[],[f3544,f200])).

fof(f2468,plain,
    ( spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f2166,f101,f171,f167,f163])).

fof(f2166,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f103])).

fof(f2362,plain,
    ( spl8_2
    | spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f2357,f171,f82,f87])).

fof(f2357,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_8 ),
    inference(trivial_inequality_removal,[],[f2347])).

fof(f2347,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_8 ),
    inference(superposition,[],[f55,f172])).

fof(f172,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f171])).

fof(f2239,plain,
    ( spl8_14
    | spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f1949,f101,f167,f2237])).

fof(f2237,plain,
    ( spl8_14
  <=> ! [X8] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f1949,plain,
    ( ! [X8] :
        ( k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1)) )
    | ~ spl8_5 ),
    inference(trivial_inequality_removal,[],[f1939])).

fof(f1939,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1)) )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f1886])).

fof(f1886,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X3,sK1)))
    | ~ spl8_5 ),
    inference(superposition,[],[f1207,f876])).

fof(f2119,plain,
    ( spl8_8
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f2031,f167,f101,f171])).

fof(f2031,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f1991,f74])).

fof(f1991,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f103,f169])).

fof(f169,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f167])).

fof(f1989,plain,
    ( spl8_13
    | spl8_7
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f1979,f1959,f167,f1986])).

fof(f1959,plain,
    ( spl8_12
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1979,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k4_xboole_0(sK3,sK1)
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f1969])).

fof(f1969,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k4_xboole_0(sK3,sK1)
    | ~ spl8_12 ),
    inference(superposition,[],[f55,f1961])).

fof(f1961,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f1959])).

fof(f1962,plain,
    ( spl8_12
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f1932,f101,f1959])).

fof(f1932,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))
    | ~ spl8_5 ),
    inference(superposition,[],[f1886,f200])).

fof(f1508,plain,
    ( spl8_11
    | spl8_1
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f1418,f101,f82,f1506])).

fof(f1418,plain,
    ( ! [X2] :
        ( k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3)) )
    | ~ spl8_5 ),
    inference(trivial_inequality_removal,[],[f1408])).

fof(f1408,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3)) )
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f1212])).

fof(f1212,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X0,sK3)))
    | ~ spl8_5 ),
    inference(superposition,[],[f837,f965])).

fof(f965,plain,
    ( ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)))
    | ~ spl8_5 ),
    inference(superposition,[],[f876,f103])).

fof(f1454,plain,
    ( spl8_10
    | spl8_1
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f1445,f1426,f82,f1451])).

fof(f1426,plain,
    ( spl8_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f1445,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl8_9 ),
    inference(trivial_inequality_removal,[],[f1435])).

fof(f1435,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl8_9 ),
    inference(superposition,[],[f55,f1428])).

fof(f1428,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f1426])).

fof(f1429,plain,
    ( spl8_9
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f1405,f101,f1426])).

fof(f1405,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl8_5 ),
    inference(superposition,[],[f1212,f200])).

fof(f174,plain,
    ( spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f161,f101,f171,f167,f163])).

fof(f161,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl8_5 ),
    inference(superposition,[],[f55,f103])).

fof(f104,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f43,f101])).

fof(f43,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f99,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f46,f96,f92])).

fof(f46,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f44,f82])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:07:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (5140)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (5141)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.49  % (5140)Refutation not found, incomplete strategy% (5140)------------------------------
% 0.20/0.49  % (5140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5133)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (5148)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (5140)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (5140)Memory used [KB]: 10746
% 0.20/0.50  % (5140)Time elapsed: 0.093 s
% 0.20/0.50  % (5140)------------------------------
% 0.20/0.50  % (5140)------------------------------
% 0.20/0.51  % (5153)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (5156)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (5153)Refutation not found, incomplete strategy% (5153)------------------------------
% 0.20/0.51  % (5153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5153)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5153)Memory used [KB]: 1663
% 0.20/0.51  % (5153)Time elapsed: 0.108 s
% 0.20/0.51  % (5153)------------------------------
% 0.20/0.51  % (5153)------------------------------
% 0.20/0.51  % (5155)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (5155)Refutation not found, incomplete strategy% (5155)------------------------------
% 0.20/0.51  % (5155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5155)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5155)Memory used [KB]: 1791
% 0.20/0.51  % (5155)Time elapsed: 0.086 s
% 0.20/0.51  % (5155)------------------------------
% 0.20/0.51  % (5155)------------------------------
% 0.20/0.51  % (5139)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (5154)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (5136)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (5135)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (5134)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (5137)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (5154)Refutation not found, incomplete strategy% (5154)------------------------------
% 0.20/0.52  % (5154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5154)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5154)Memory used [KB]: 10746
% 0.20/0.52  % (5154)Time elapsed: 0.087 s
% 0.20/0.52  % (5154)------------------------------
% 0.20/0.52  % (5154)------------------------------
% 0.20/0.52  % (5134)Refutation not found, incomplete strategy% (5134)------------------------------
% 0.20/0.52  % (5134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5134)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5134)Memory used [KB]: 10746
% 0.20/0.52  % (5134)Time elapsed: 0.117 s
% 0.20/0.52  % (5134)------------------------------
% 0.20/0.52  % (5134)------------------------------
% 0.20/0.52  % (5146)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (5144)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (5143)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (5158)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (5159)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (5157)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (5160)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (5138)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (5132)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (5132)Refutation not found, incomplete strategy% (5132)------------------------------
% 0.20/0.53  % (5132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5132)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5132)Memory used [KB]: 1663
% 0.20/0.53  % (5132)Time elapsed: 0.137 s
% 0.20/0.53  % (5132)------------------------------
% 0.20/0.53  % (5132)------------------------------
% 0.20/0.53  % (5150)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (5151)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (5152)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (5152)Refutation not found, incomplete strategy% (5152)------------------------------
% 0.20/0.54  % (5152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5152)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5152)Memory used [KB]: 10746
% 0.20/0.54  % (5152)Time elapsed: 0.139 s
% 0.20/0.54  % (5152)------------------------------
% 0.20/0.54  % (5152)------------------------------
% 0.20/0.54  % (5149)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (5161)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (5149)Refutation not found, incomplete strategy% (5149)------------------------------
% 0.20/0.54  % (5149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5149)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5149)Memory used [KB]: 10618
% 0.20/0.54  % (5149)Time elapsed: 0.149 s
% 0.20/0.54  % (5149)------------------------------
% 0.20/0.54  % (5149)------------------------------
% 0.20/0.54  % (5142)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (5145)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (5147)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.81/0.61  % (5162)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.81/0.61  % (5162)Refutation not found, incomplete strategy% (5162)------------------------------
% 1.81/0.61  % (5162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (5162)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (5162)Memory used [KB]: 6140
% 1.81/0.61  % (5162)Time elapsed: 0.051 s
% 1.81/0.61  % (5162)------------------------------
% 1.81/0.61  % (5162)------------------------------
% 2.26/0.64  % (5164)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.26/0.65  % (5163)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.26/0.67  % (5166)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.26/0.67  % (5167)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.26/0.67  % (5165)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.26/0.67  % (5168)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.26/0.69  % (5170)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.26/0.71  % (5169)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.28/0.80  % (5137)Time limit reached!
% 3.28/0.80  % (5137)------------------------------
% 3.28/0.80  % (5137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.80  % (5137)Termination reason: Time limit
% 3.28/0.80  % (5137)Termination phase: Saturation
% 3.28/0.80  
% 3.28/0.80  % (5137)Memory used [KB]: 8955
% 3.28/0.80  % (5137)Time elapsed: 0.400 s
% 3.28/0.80  % (5137)------------------------------
% 3.28/0.80  % (5137)------------------------------
% 3.95/0.91  % (5142)Time limit reached!
% 3.95/0.91  % (5142)------------------------------
% 3.95/0.91  % (5142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.91  % (5142)Termination reason: Time limit
% 3.95/0.91  % (5142)Termination phase: Saturation
% 3.95/0.91  
% 3.95/0.91  % (5142)Memory used [KB]: 17910
% 3.95/0.91  % (5142)Time elapsed: 0.500 s
% 3.95/0.91  % (5142)------------------------------
% 3.95/0.91  % (5142)------------------------------
% 3.95/0.91  % (5144)Time limit reached!
% 3.95/0.91  % (5144)------------------------------
% 3.95/0.91  % (5144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.91  % (5144)Termination reason: Time limit
% 3.95/0.91  
% 3.95/0.91  % (5144)Memory used [KB]: 8315
% 3.95/0.91  % (5144)Time elapsed: 0.522 s
% 3.95/0.91  % (5144)------------------------------
% 3.95/0.91  % (5144)------------------------------
% 4.26/0.91  % (5133)Time limit reached!
% 4.26/0.91  % (5133)------------------------------
% 4.26/0.91  % (5133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.91  % (5133)Termination reason: Time limit
% 4.26/0.91  % (5133)Termination phase: Saturation
% 4.26/0.91  
% 4.26/0.91  % (5133)Memory used [KB]: 11129
% 4.26/0.91  % (5133)Time elapsed: 0.500 s
% 4.26/0.91  % (5133)------------------------------
% 4.26/0.91  % (5133)------------------------------
% 4.26/0.93  % (5171)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.45/0.96  % (5165)Time limit reached!
% 4.45/0.96  % (5165)------------------------------
% 4.45/0.96  % (5165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.96  % (5165)Termination reason: Time limit
% 4.45/0.96  
% 4.45/0.96  % (5165)Memory used [KB]: 7419
% 4.45/0.96  % (5165)Time elapsed: 0.420 s
% 4.45/0.96  % (5165)------------------------------
% 4.45/0.96  % (5165)------------------------------
% 4.45/0.98  % (5166)Time limit reached!
% 4.45/0.98  % (5166)------------------------------
% 4.45/0.98  % (5166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.98  % (5166)Termination reason: Time limit
% 4.45/0.98  
% 4.45/0.98  % (5166)Memory used [KB]: 13432
% 4.45/0.98  % (5166)Time elapsed: 0.415 s
% 4.45/0.98  % (5166)------------------------------
% 4.45/0.98  % (5166)------------------------------
% 4.45/1.01  % (5139)Time limit reached!
% 4.45/1.01  % (5139)------------------------------
% 4.45/1.01  % (5139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.01  % (5139)Termination reason: Time limit
% 4.45/1.01  
% 4.45/1.01  % (5139)Memory used [KB]: 10106
% 4.45/1.01  % (5139)Time elapsed: 0.605 s
% 4.45/1.01  % (5139)------------------------------
% 4.45/1.01  % (5139)------------------------------
% 4.45/1.01  % (5160)Time limit reached!
% 4.45/1.01  % (5160)------------------------------
% 4.45/1.01  % (5160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.01  % (5160)Termination reason: Time limit
% 4.45/1.01  % (5160)Termination phase: Saturation
% 4.45/1.01  
% 4.45/1.01  % (5160)Memory used [KB]: 9466
% 4.45/1.01  % (5160)Time elapsed: 0.600 s
% 4.45/1.01  % (5160)------------------------------
% 4.45/1.01  % (5160)------------------------------
% 4.45/1.02  % (5148)Time limit reached!
% 4.45/1.02  % (5148)------------------------------
% 4.45/1.02  % (5148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/1.02  % (5148)Termination reason: Time limit
% 4.45/1.02  
% 4.45/1.02  % (5148)Memory used [KB]: 15863
% 4.45/1.02  % (5148)Time elapsed: 0.613 s
% 4.45/1.02  % (5148)------------------------------
% 4.45/1.02  % (5148)------------------------------
% 4.45/1.02  % (5174)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.03/1.03  % (5172)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.03/1.03  % (5172)Refutation not found, incomplete strategy% (5172)------------------------------
% 5.03/1.03  % (5172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.03  % (5172)Termination reason: Refutation not found, incomplete strategy
% 5.03/1.03  
% 5.03/1.03  % (5172)Memory used [KB]: 6268
% 5.03/1.03  % (5172)Time elapsed: 0.107 s
% 5.03/1.03  % (5172)------------------------------
% 5.03/1.03  % (5172)------------------------------
% 5.03/1.05  % (5173)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.03/1.05  % (5173)Refutation not found, incomplete strategy% (5173)------------------------------
% 5.03/1.05  % (5173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.05  % (5173)Termination reason: Refutation not found, incomplete strategy
% 5.03/1.05  
% 5.03/1.05  % (5173)Memory used [KB]: 1791
% 5.03/1.05  % (5173)Time elapsed: 0.117 s
% 5.03/1.05  % (5173)------------------------------
% 5.03/1.05  % (5173)------------------------------
% 5.40/1.09  % (5175)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.40/1.10  % (5175)Refutation not found, incomplete strategy% (5175)------------------------------
% 5.40/1.10  % (5175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.10  % (5175)Termination reason: Refutation not found, incomplete strategy
% 5.40/1.10  
% 5.40/1.10  % (5175)Memory used [KB]: 1663
% 5.40/1.10  % (5175)Time elapsed: 0.116 s
% 5.40/1.10  % (5175)------------------------------
% 5.40/1.10  % (5175)------------------------------
% 5.40/1.11  % (5176)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.40/1.14  % (5177)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.40/1.14  % (5177)Refutation not found, incomplete strategy% (5177)------------------------------
% 5.40/1.14  % (5177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.14  % (5177)Termination reason: Refutation not found, incomplete strategy
% 5.40/1.14  
% 5.40/1.14  % (5177)Memory used [KB]: 6268
% 5.40/1.14  % (5177)Time elapsed: 0.124 s
% 5.40/1.14  % (5177)------------------------------
% 5.40/1.14  % (5177)------------------------------
% 5.40/1.15  % (5178)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 5.40/1.16  % (5180)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.34/1.17  % (5179)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.51/1.18  % (5181)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.82/1.23  % (5182)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 6.97/1.31  % (5183)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.65/1.46  % (5174)Time limit reached!
% 8.65/1.46  % (5174)------------------------------
% 8.65/1.46  % (5174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.65/1.46  % (5174)Termination reason: Time limit
% 8.65/1.46  % (5174)Termination phase: Saturation
% 8.65/1.46  
% 8.65/1.46  % (5174)Memory used [KB]: 4349
% 8.65/1.46  % (5174)Time elapsed: 0.500 s
% 8.65/1.46  % (5174)------------------------------
% 8.65/1.46  % (5174)------------------------------
% 8.65/1.47  % (5178)Time limit reached!
% 8.65/1.47  % (5178)------------------------------
% 8.65/1.47  % (5178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.65/1.47  % (5178)Termination reason: Time limit
% 8.65/1.47  
% 8.65/1.47  % (5178)Memory used [KB]: 3965
% 8.65/1.47  % (5178)Time elapsed: 0.418 s
% 8.65/1.47  % (5178)------------------------------
% 8.65/1.47  % (5178)------------------------------
% 8.90/1.49  % (5181)Time limit reached!
% 8.90/1.49  % (5181)------------------------------
% 8.90/1.49  % (5181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.90/1.49  % (5181)Termination reason: Time limit
% 8.90/1.49  
% 8.90/1.49  % (5181)Memory used [KB]: 2686
% 8.90/1.49  % (5181)Time elapsed: 0.413 s
% 8.90/1.49  % (5181)------------------------------
% 8.90/1.49  % (5181)------------------------------
% 9.35/1.59  % (5158)Time limit reached!
% 9.35/1.59  % (5158)------------------------------
% 9.35/1.59  % (5158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.35/1.59  % (5158)Termination reason: Time limit
% 9.35/1.59  % (5158)Termination phase: Saturation
% 9.35/1.59  
% 9.35/1.59  % (5158)Memory used [KB]: 23411
% 9.35/1.59  % (5158)Time elapsed: 1.200 s
% 9.35/1.59  % (5158)------------------------------
% 9.35/1.59  % (5158)------------------------------
% 9.35/1.60  % (5184)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.86/1.62  % (5185)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 9.86/1.63  % (5186)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.44/1.70  % (5147)Time limit reached!
% 10.44/1.70  % (5147)------------------------------
% 10.44/1.70  % (5147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.44/1.70  % (5147)Termination reason: Time limit
% 10.44/1.70  
% 10.44/1.70  % (5147)Memory used [KB]: 17526
% 10.44/1.70  % (5147)Time elapsed: 1.304 s
% 10.44/1.70  % (5147)------------------------------
% 10.44/1.70  % (5147)------------------------------
% 10.44/1.70  % (5156)Time limit reached!
% 10.44/1.70  % (5156)------------------------------
% 10.44/1.70  % (5156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.44/1.70  % (5156)Termination reason: Time limit
% 10.44/1.70  % (5156)Termination phase: Saturation
% 10.44/1.70  
% 10.44/1.70  % (5156)Memory used [KB]: 28016
% 10.44/1.70  % (5156)Time elapsed: 1.300 s
% 10.44/1.70  % (5156)------------------------------
% 10.44/1.70  % (5156)------------------------------
% 10.44/1.74  % (5187)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 10.44/1.74  % (5187)Refutation not found, incomplete strategy% (5187)------------------------------
% 10.44/1.74  % (5187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.44/1.74  % (5187)Termination reason: Refutation not found, incomplete strategy
% 10.44/1.74  
% 10.44/1.74  % (5187)Memory used [KB]: 6268
% 10.44/1.74  % (5187)Time elapsed: 0.110 s
% 10.44/1.74  % (5187)------------------------------
% 10.44/1.74  % (5187)------------------------------
% 11.14/1.79  % (5168)Time limit reached!
% 11.14/1.79  % (5168)------------------------------
% 11.14/1.79  % (5168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.14/1.79  % (5168)Termination reason: Time limit
% 11.14/1.79  
% 11.14/1.79  % (5168)Memory used [KB]: 13304
% 11.14/1.79  % (5168)Time elapsed: 1.209 s
% 11.14/1.79  % (5168)------------------------------
% 11.14/1.79  % (5168)------------------------------
% 11.60/1.83  % (5189)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 11.60/1.83  % (5189)Refutation not found, incomplete strategy% (5189)------------------------------
% 11.60/1.83  % (5189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.60/1.83  % (5188)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.60/1.83  % (5189)Termination reason: Refutation not found, incomplete strategy
% 11.60/1.83  
% 11.60/1.83  % (5189)Memory used [KB]: 10746
% 11.60/1.83  % (5189)Time elapsed: 0.008 s
% 11.60/1.83  % (5189)------------------------------
% 11.60/1.83  % (5189)------------------------------
% 12.18/1.92  % (5159)Time limit reached!
% 12.18/1.92  % (5159)------------------------------
% 12.18/1.92  % (5159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.18/1.92  % (5159)Termination reason: Time limit
% 12.18/1.92  % (5159)Termination phase: Saturation
% 12.18/1.92  
% 12.18/1.92  % (5159)Memory used [KB]: 14967
% 12.18/1.92  % (5159)Time elapsed: 1.500 s
% 12.18/1.92  % (5159)------------------------------
% 12.18/1.92  % (5159)------------------------------
% 12.18/1.94  % (5186)Time limit reached!
% 12.18/1.94  % (5186)------------------------------
% 12.18/1.94  % (5186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.18/1.94  % (5186)Termination reason: Time limit
% 12.18/1.94  
% 12.18/1.94  % (5186)Memory used [KB]: 10490
% 12.18/1.94  % (5186)Time elapsed: 0.423 s
% 12.18/1.94  % (5186)------------------------------
% 12.18/1.94  % (5186)------------------------------
% 12.79/1.98  % (5136)Time limit reached!
% 12.79/1.98  % (5136)------------------------------
% 12.79/1.98  % (5136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.79/1.98  % (5136)Termination reason: Time limit
% 12.79/1.98  
% 12.79/1.98  % (5136)Memory used [KB]: 23666
% 12.79/1.98  % (5136)Time elapsed: 1.547 s
% 12.79/1.98  % (5136)------------------------------
% 12.79/1.98  % (5136)------------------------------
% 13.51/2.07  % (5143)Time limit reached!
% 13.51/2.07  % (5143)------------------------------
% 13.51/2.07  % (5143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.51/2.07  % (5143)Termination reason: Time limit
% 13.51/2.07  
% 13.51/2.07  % (5143)Memory used [KB]: 32877
% 13.51/2.07  % (5143)Time elapsed: 1.649 s
% 13.51/2.07  % (5143)------------------------------
% 13.51/2.07  % (5143)------------------------------
% 13.99/2.13  % (5188)Time limit reached!
% 13.99/2.13  % (5188)------------------------------
% 13.99/2.13  % (5188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.99/2.13  % (5188)Termination reason: Time limit
% 13.99/2.13  
% 13.99/2.13  % (5188)Memory used [KB]: 11385
% 13.99/2.13  % (5188)Time elapsed: 0.408 s
% 13.99/2.13  % (5188)------------------------------
% 13.99/2.13  % (5188)------------------------------
% 14.72/2.24  % (5164)Time limit reached!
% 14.72/2.24  % (5164)------------------------------
% 14.72/2.24  % (5164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.72/2.24  % (5164)Termination reason: Time limit
% 14.72/2.24  % (5164)Termination phase: Saturation
% 14.72/2.24  
% 14.72/2.24  % (5164)Memory used [KB]: 21492
% 14.72/2.24  % (5164)Time elapsed: 1.700 s
% 14.72/2.24  % (5164)------------------------------
% 14.72/2.24  % (5164)------------------------------
% 14.72/2.26  % (5146)Time limit reached!
% 14.72/2.26  % (5146)------------------------------
% 14.72/2.26  % (5146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.72/2.26  % (5146)Termination reason: Time limit
% 14.72/2.26  % (5146)Termination phase: Saturation
% 14.72/2.26  
% 14.72/2.26  % (5146)Memory used [KB]: 6396
% 14.72/2.26  % (5146)Time elapsed: 1.800 s
% 14.72/2.26  % (5146)------------------------------
% 14.72/2.26  % (5146)------------------------------
% 15.34/2.36  % (5170)Time limit reached!
% 15.34/2.36  % (5170)------------------------------
% 15.34/2.36  % (5170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.34/2.36  % (5170)Termination reason: Time limit
% 15.34/2.36  % (5170)Termination phase: Saturation
% 15.34/2.36  
% 15.34/2.36  % (5170)Memory used [KB]: 25074
% 15.34/2.36  % (5170)Time elapsed: 1.700 s
% 15.34/2.36  % (5170)------------------------------
% 15.34/2.36  % (5170)------------------------------
% 16.26/2.40  % (5180)Time limit reached!
% 16.26/2.40  % (5180)------------------------------
% 16.26/2.40  % (5180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.26/2.40  % (5180)Termination reason: Time limit
% 16.26/2.40  
% 16.26/2.40  % (5180)Memory used [KB]: 9722
% 16.26/2.40  % (5180)Time elapsed: 1.316 s
% 16.26/2.40  % (5180)------------------------------
% 16.26/2.40  % (5180)------------------------------
% 16.44/2.45  % (5138)Time limit reached!
% 16.44/2.45  % (5138)------------------------------
% 16.44/2.45  % (5138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.44/2.45  % (5138)Termination reason: Time limit
% 16.44/2.45  
% 16.44/2.45  % (5138)Memory used [KB]: 24306
% 16.44/2.45  % (5138)Time elapsed: 2.029 s
% 16.44/2.45  % (5138)------------------------------
% 16.44/2.45  % (5138)------------------------------
% 16.44/2.47  % (5150)Time limit reached!
% 16.44/2.47  % (5150)------------------------------
% 16.44/2.47  % (5150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.44/2.47  % (5150)Termination reason: Time limit
% 16.44/2.47  
% 16.44/2.47  % (5150)Memory used [KB]: 13048
% 16.44/2.47  % (5150)Time elapsed: 2.056 s
% 16.44/2.47  % (5150)------------------------------
% 16.44/2.47  % (5150)------------------------------
% 21.25/3.02  % (5151)Time limit reached!
% 21.25/3.02  % (5151)------------------------------
% 21.25/3.02  % (5151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.25/3.02  % (5151)Termination reason: Time limit
% 21.25/3.02  % (5151)Termination phase: Saturation
% 21.25/3.02  
% 21.25/3.02  % (5151)Memory used [KB]: 34796
% 21.25/3.02  % (5151)Time elapsed: 2.600 s
% 21.25/3.02  % (5151)------------------------------
% 21.25/3.02  % (5151)------------------------------
% 23.72/3.36  % (5163)Time limit reached!
% 23.72/3.36  % (5163)------------------------------
% 23.72/3.36  % (5163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.72/3.37  % (5163)Termination reason: Time limit
% 23.72/3.37  % (5163)Termination phase: Saturation
% 23.72/3.37  
% 23.72/3.37  % (5163)Memory used [KB]: 23539
% 23.72/3.37  % (5163)Time elapsed: 2.800 s
% 23.72/3.37  % (5163)------------------------------
% 23.72/3.37  % (5163)------------------------------
% 23.72/3.40  % (5145)Time limit reached!
% 23.72/3.40  % (5145)------------------------------
% 23.72/3.40  % (5145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.72/3.40  % (5145)Termination reason: Time limit
% 23.72/3.40  % (5145)Termination phase: Saturation
% 23.72/3.40  
% 23.72/3.40  % (5145)Memory used [KB]: 17782
% 23.72/3.40  % (5145)Time elapsed: 3.0000 s
% 23.72/3.40  % (5145)------------------------------
% 23.72/3.40  % (5145)------------------------------
% 31.66/4.32  % (5161)Time limit reached!
% 31.66/4.32  % (5161)------------------------------
% 31.66/4.32  % (5161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.66/4.32  % (5161)Termination reason: Time limit
% 31.66/4.32  
% 31.66/4.32  % (5161)Memory used [KB]: 43112
% 31.66/4.32  % (5161)Time elapsed: 3.926 s
% 31.66/4.32  % (5161)------------------------------
% 31.66/4.32  % (5161)------------------------------
% 32.99/4.51  % (5176)Time limit reached!
% 32.99/4.51  % (5176)------------------------------
% 32.99/4.51  % (5176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 32.99/4.51  % (5176)Termination reason: Time limit
% 32.99/4.51  
% 32.99/4.51  % (5176)Memory used [KB]: 62173
% 32.99/4.51  % (5176)Time elapsed: 3.513 s
% 32.99/4.51  % (5176)------------------------------
% 32.99/4.51  % (5176)------------------------------
% 36.87/5.01  % (5141)Time limit reached!
% 36.87/5.01  % (5141)------------------------------
% 36.87/5.01  % (5141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.87/5.03  % (5141)Termination reason: Time limit
% 36.87/5.03  % (5141)Termination phase: Saturation
% 36.87/5.03  
% 36.87/5.03  % (5141)Memory used [KB]: 51427
% 36.87/5.03  % (5141)Time elapsed: 4.600 s
% 36.87/5.03  % (5141)------------------------------
% 36.87/5.03  % (5141)------------------------------
% 41.68/5.60  % (5135)Time limit reached!
% 41.68/5.60  % (5135)------------------------------
% 41.68/5.60  % (5135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.68/5.60  % (5135)Termination reason: Time limit
% 41.68/5.60  % (5135)Termination phase: Saturation
% 41.68/5.60  
% 41.68/5.60  % (5135)Memory used [KB]: 84945
% 41.68/5.60  % (5135)Time elapsed: 5.200 s
% 41.68/5.60  % (5135)------------------------------
% 41.68/5.60  % (5135)------------------------------
% 45.25/6.07  % (5169)Time limit reached!
% 45.25/6.07  % (5169)------------------------------
% 45.25/6.07  % (5169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 45.25/6.07  % (5169)Termination reason: Time limit
% 45.25/6.07  % (5169)Termination phase: Saturation
% 45.25/6.07  
% 45.25/6.07  % (5169)Memory used [KB]: 96970
% 45.25/6.07  % (5169)Time elapsed: 5.500 s
% 45.25/6.07  % (5169)------------------------------
% 45.25/6.07  % (5169)------------------------------
% 47.47/6.33  % (5182)Refutation found. Thanks to Tanya!
% 47.47/6.33  % SZS status Theorem for theBenchmark
% 47.47/6.33  % SZS output start Proof for theBenchmark
% 47.47/6.33  fof(f193565,plain,(
% 47.47/6.33    $false),
% 47.47/6.33    inference(avatar_sat_refutation,[],[f85,f90,f99,f104,f174,f1429,f1454,f1508,f1962,f1989,f2119,f2239,f2362,f2468,f3870,f3906,f3969,f4034,f4318,f4684,f4722,f4785,f4856,f5202,f5434,f5483,f5490,f5552,f5599,f6744,f6786,f6850,f7947,f8641,f8756,f8781,f8846,f8906,f9157,f9212,f9276,f9957,f10045,f12010,f12173,f12585,f13062,f33016,f33023,f33028,f33038,f34049,f34059,f35012,f35019,f35024,f35720,f37002,f42509,f42535,f42537,f43850,f43883,f44386,f44390,f44402,f44930,f44939,f44943,f45356,f45742,f46164,f46558,f48686,f50028,f50435,f50887,f51617,f51999,f53775,f55967,f56163,f56282,f71580,f73319,f73505,f73851,f74818,f75024,f92907,f100245,f100346,f100450,f112761,f113740,f114022,f126713,f127665,f128129,f142807,f143766,f144049,f158509,f159468,f163057,f163070,f163092,f163105,f163507,f163520,f163543,f163556,f177354,f177361,f177369,f178027,f178182,f178188,f180825,f180938,f180946,f181257,f181264,f181981,f182131,f182132,f182169,f182170,f182175,f182180,f182227,f182264,f182281,f182356,f182357,f182358,f182359,f182363,f182377,f182394,f182411,f182779,f182783,f184286,f187007,f187447,f187452,f187503,f187508,f187516,f187521,f188083,f188292,f188304,f188305,f188306,f188307,f188328,f188342,f188359,f188376,f188766,f188770,f193564])).
% 47.47/6.33  fof(f193564,plain,(
% 47.47/6.33    spl8_140 | spl8_146 | ~spl8_16 | ~spl8_141),
% 47.47/6.33    inference(avatar_split_clause,[],[f193560,f187449,f3903,f188080,f187444])).
% 47.47/6.33  fof(f187444,plain,(
% 47.47/6.33    spl8_140 <=> r2_hidden(sK5(sK2,sK0),sK2)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).
% 47.47/6.33  fof(f188080,plain,(
% 47.47/6.33    spl8_146 <=> r2_hidden(sK5(sK2,sK0),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).
% 47.47/6.33  fof(f3903,plain,(
% 47.47/6.33    spl8_16 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 47.47/6.33  fof(f187449,plain,(
% 47.47/6.33    spl8_141 <=> r2_hidden(sK5(sK2,sK0),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).
% 47.47/6.33  fof(f193560,plain,(
% 47.47/6.33    r2_hidden(sK5(sK2,sK0),k1_xboole_0) | r2_hidden(sK5(sK2,sK0),sK2) | (~spl8_16 | ~spl8_141)),
% 47.47/6.33    inference(superposition,[],[f187454,f3905])).
% 47.47/6.33  fof(f3905,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl8_16),
% 47.47/6.33    inference(avatar_component_clause,[],[f3903])).
% 47.47/6.33  fof(f187454,plain,(
% 47.47/6.33    ( ! [X1] : (r2_hidden(sK5(sK2,sK0),k4_xboole_0(sK0,X1)) | r2_hidden(sK5(sK2,sK0),X1)) ) | ~spl8_141),
% 47.47/6.33    inference(resolution,[],[f187451,f75])).
% 47.47/6.33  fof(f75,plain,(
% 47.47/6.33    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X1) | r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 47.47/6.33    inference(equality_resolution,[],[f62])).
% 47.47/6.33  fof(f62,plain,(
% 47.47/6.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 47.47/6.33    inference(cnf_transformation,[],[f37])).
% 47.47/6.33  fof(f37,plain,(
% 47.47/6.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 47.47/6.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 47.47/6.33  fof(f36,plain,(
% 47.47/6.33    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 47.47/6.33    introduced(choice_axiom,[])).
% 47.47/6.33  fof(f35,plain,(
% 47.47/6.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 47.47/6.33    inference(rectify,[],[f34])).
% 47.47/6.33  fof(f34,plain,(
% 47.47/6.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 47.47/6.33    inference(flattening,[],[f33])).
% 47.47/6.33  fof(f33,plain,(
% 47.47/6.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 47.47/6.33    inference(nnf_transformation,[],[f4])).
% 47.47/6.33  fof(f4,axiom,(
% 47.47/6.33    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 47.47/6.33  fof(f187451,plain,(
% 47.47/6.33    r2_hidden(sK5(sK2,sK0),sK0) | ~spl8_141),
% 47.47/6.33    inference(avatar_component_clause,[],[f187449])).
% 47.47/6.33  fof(f188770,plain,(
% 47.47/6.33    spl8_7 | spl8_154 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177413,f177358,f188768,f167])).
% 47.47/6.33  fof(f167,plain,(
% 47.47/6.33    spl8_7 <=> k1_xboole_0 = sK2),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 47.47/6.33  fof(f188768,plain,(
% 47.47/6.33    spl8_154 <=> ! [X18] : ~r2_hidden(sK5(k1_xboole_0,sK2),k4_xboole_0(X18,sK0))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).
% 47.47/6.33  fof(f177358,plain,(
% 47.47/6.33    spl8_116 <=> sK2 = k3_xboole_0(sK2,sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).
% 47.47/6.33  fof(f177413,plain,(
% 47.47/6.33    ( ! [X18] : (~r2_hidden(sK5(k1_xboole_0,sK2),k4_xboole_0(X18,sK0)) | k1_xboole_0 = sK2) ) | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f449,f177360])).
% 47.47/6.33  fof(f177360,plain,(
% 47.47/6.33    sK2 = k3_xboole_0(sK2,sK0) | ~spl8_116),
% 47.47/6.33    inference(avatar_component_clause,[],[f177358])).
% 47.47/6.33  fof(f449,plain,(
% 47.47/6.33    ( ! [X6,X8,X7] : (~r2_hidden(sK5(k1_xboole_0,k3_xboole_0(X6,X7)),k4_xboole_0(X8,X7)) | k1_xboole_0 = k3_xboole_0(X6,X7)) )),
% 47.47/6.33    inference(resolution,[],[f146,f76])).
% 47.47/6.33  fof(f76,plain,(
% 47.47/6.33    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 47.47/6.33    inference(equality_resolution,[],[f61])).
% 47.47/6.33  fof(f61,plain,(
% 47.47/6.33    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 47.47/6.33    inference(cnf_transformation,[],[f37])).
% 47.47/6.33  fof(f146,plain,(
% 47.47/6.33    ( ! [X4,X5] : (r2_hidden(sK5(k1_xboole_0,k3_xboole_0(X4,X5)),X5) | k1_xboole_0 = k3_xboole_0(X4,X5)) )),
% 47.47/6.33    inference(resolution,[],[f143,f79])).
% 47.47/6.33  fof(f79,plain,(
% 47.47/6.33    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 47.47/6.33    inference(equality_resolution,[],[f67])).
% 47.47/6.33  fof(f67,plain,(
% 47.47/6.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 47.47/6.33    inference(cnf_transformation,[],[f42])).
% 47.47/6.33  fof(f42,plain,(
% 47.47/6.33    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 47.47/6.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 47.47/6.33  fof(f41,plain,(
% 47.47/6.33    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 47.47/6.33    introduced(choice_axiom,[])).
% 47.47/6.33  fof(f40,plain,(
% 47.47/6.33    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 47.47/6.33    inference(rectify,[],[f39])).
% 47.47/6.33  fof(f39,plain,(
% 47.47/6.33    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 47.47/6.33    inference(flattening,[],[f38])).
% 47.47/6.33  fof(f38,plain,(
% 47.47/6.33    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 47.47/6.33    inference(nnf_transformation,[],[f3])).
% 47.47/6.33  fof(f3,axiom,(
% 47.47/6.33    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 47.47/6.33  fof(f143,plain,(
% 47.47/6.33    ( ! [X1] : (r2_hidden(sK5(k1_xboole_0,X1),X1) | k1_xboole_0 = X1) )),
% 47.47/6.33    inference(resolution,[],[f141,f58])).
% 47.47/6.33  fof(f58,plain,(
% 47.47/6.33    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK5(X0,X1),X1)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f32])).
% 47.47/6.33  fof(f32,plain,(
% 47.47/6.33    ! [X0,X1] : ((~r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 47.47/6.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f31])).
% 47.47/6.33  fof(f31,plain,(
% 47.47/6.33    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1)))),
% 47.47/6.33    introduced(choice_axiom,[])).
% 47.47/6.33  fof(f24,plain,(
% 47.47/6.33    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 47.47/6.33    inference(ennf_transformation,[],[f7])).
% 47.47/6.33  fof(f7,axiom,(
% 47.47/6.33    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 47.47/6.33  fof(f141,plain,(
% 47.47/6.33    ( ! [X1] : (r2_xboole_0(k1_xboole_0,X1) | k1_xboole_0 = X1) )),
% 47.47/6.33    inference(resolution,[],[f52,f138])).
% 47.47/6.33  fof(f138,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f132])).
% 47.47/6.33  fof(f132,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 47.47/6.33    inference(resolution,[],[f125,f54])).
% 47.47/6.33  fof(f54,plain,(
% 47.47/6.33    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f28])).
% 47.47/6.33  fof(f28,plain,(
% 47.47/6.33    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 47.47/6.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f27])).
% 47.47/6.33  fof(f27,plain,(
% 47.47/6.33    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 47.47/6.33    introduced(choice_axiom,[])).
% 47.47/6.33  fof(f23,plain,(
% 47.47/6.33    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 47.47/6.33    inference(ennf_transformation,[],[f17])).
% 47.47/6.33  fof(f17,plain,(
% 47.47/6.33    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 47.47/6.33    inference(unused_predicate_definition_removal,[],[f2])).
% 47.47/6.33  fof(f2,axiom,(
% 47.47/6.33    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 47.47/6.33  fof(f125,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK4(k1_xboole_0,X0),X1) | r1_tarski(k1_xboole_0,X0)) )),
% 47.47/6.33    inference(resolution,[],[f124,f53])).
% 47.47/6.33  fof(f53,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f28])).
% 47.47/6.33  fof(f124,plain,(
% 47.47/6.33    ( ! [X10,X11] : (~r2_hidden(X11,k1_xboole_0) | r2_hidden(X11,X10)) )),
% 47.47/6.33    inference(superposition,[],[f79,f105])).
% 47.47/6.33  fof(f105,plain,(
% 47.47/6.33    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 47.47/6.33    inference(superposition,[],[f50,f48])).
% 47.47/6.33  fof(f48,plain,(
% 47.47/6.33    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f9])).
% 47.47/6.33  fof(f9,axiom,(
% 47.47/6.33    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 47.47/6.33  fof(f50,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f1])).
% 47.47/6.33  fof(f1,axiom,(
% 47.47/6.33    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 47.47/6.33  fof(f52,plain,(
% 47.47/6.33    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f22])).
% 47.47/6.33  fof(f22,plain,(
% 47.47/6.33    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 47.47/6.33    inference(flattening,[],[f21])).
% 47.47/6.33  fof(f21,plain,(
% 47.47/6.33    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 47.47/6.33    inference(ennf_transformation,[],[f16])).
% 47.47/6.33  fof(f16,plain,(
% 47.47/6.33    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 47.47/6.33    inference(unused_predicate_definition_removal,[],[f5])).
% 47.47/6.33  fof(f5,axiom,(
% 47.47/6.33    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 47.47/6.33  fof(f188766,plain,(
% 47.47/6.33    spl8_3 | spl8_153 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177410,f177358,f188764,f92])).
% 47.47/6.33  fof(f92,plain,(
% 47.47/6.33    spl8_3 <=> sK0 = sK2),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 47.47/6.33  fof(f188764,plain,(
% 47.47/6.33    spl8_153 <=> ! [X15] : ~r2_hidden(sK5(sK2,sK0),k4_xboole_0(X15,sK0))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_153])])).
% 47.47/6.33  fof(f177410,plain,(
% 47.47/6.33    ( ! [X15] : (~r2_hidden(sK5(sK2,sK0),k4_xboole_0(X15,sK0)) | sK0 = sK2) ) | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f393,f177360])).
% 47.47/6.33  fof(f393,plain,(
% 47.47/6.33    ( ! [X6,X8,X7] : (~r2_hidden(sK5(k3_xboole_0(X6,X7),X7),k4_xboole_0(X8,X7)) | k3_xboole_0(X6,X7) = X7) )),
% 47.47/6.33    inference(resolution,[],[f334,f76])).
% 47.47/6.33  fof(f334,plain,(
% 47.47/6.33    ( ! [X2,X3] : (r2_hidden(sK5(k3_xboole_0(X2,X3),X3),X3) | k3_xboole_0(X2,X3) = X3) )),
% 47.47/6.33    inference(resolution,[],[f235,f58])).
% 47.47/6.33  fof(f235,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_xboole_0(k3_xboole_0(X0,X1),X1) | k3_xboole_0(X0,X1) = X1) )),
% 47.47/6.33    inference(resolution,[],[f232,f52])).
% 47.47/6.33  fof(f232,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f215])).
% 47.47/6.33  fof(f215,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 47.47/6.33    inference(resolution,[],[f119,f54])).
% 47.47/6.33  fof(f119,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 47.47/6.33    inference(resolution,[],[f79,f53])).
% 47.47/6.33  fof(f188376,plain,(
% 47.47/6.33    spl8_7 | spl8_152 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177475,f177358,f188374,f167])).
% 47.47/6.33  fof(f188374,plain,(
% 47.47/6.33    spl8_152 <=> ! [X118] : r2_hidden(sK7(X118,k1_xboole_0,sK2),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_152])])).
% 47.47/6.33  fof(f177475,plain,(
% 47.47/6.33    ( ! [X118] : (r2_hidden(sK7(X118,k1_xboole_0,sK2),sK0) | k1_xboole_0 = sK2) ) | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f29246,f177360])).
% 47.47/6.33  fof(f29246,plain,(
% 47.47/6.33    ( ! [X14,X12,X13] : (r2_hidden(sK7(X14,k1_xboole_0,k3_xboole_0(X12,X13)),X13) | k1_xboole_0 = k3_xboole_0(X12,X13)) )),
% 47.47/6.33    inference(resolution,[],[f29241,f79])).
% 47.47/6.33  fof(f29241,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK7(X0,k1_xboole_0,X1),X1) | k1_xboole_0 = X1) )),
% 47.47/6.33    inference(forward_demodulation,[],[f29237,f48])).
% 47.47/6.33  fof(f29237,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK7(X0,k1_xboole_0,X1),X1) | k3_xboole_0(X0,k1_xboole_0) = X1) )),
% 47.47/6.33    inference(condensation,[],[f29198])).
% 47.47/6.33  fof(f29198,plain,(
% 47.47/6.33    ( ! [X35,X33,X34] : (r2_hidden(sK7(X33,k1_xboole_0,X34),X34) | k3_xboole_0(X33,k1_xboole_0) = X34 | r2_hidden(sK7(X33,k1_xboole_0,X34),X35)) )),
% 47.47/6.33    inference(resolution,[],[f70,f124])).
% 47.47/6.33  fof(f70,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 47.47/6.33    inference(cnf_transformation,[],[f42])).
% 47.47/6.33  fof(f188359,plain,(
% 47.47/6.33    spl8_7 | spl8_151 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177445,f177358,f188357,f167])).
% 47.47/6.33  fof(f188357,plain,(
% 47.47/6.33    spl8_151 <=> ! [X68] : r2_hidden(sK7(k1_xboole_0,X68,sK2),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).
% 47.47/6.33  fof(f177445,plain,(
% 47.47/6.33    ( ! [X68] : (r2_hidden(sK7(k1_xboole_0,X68,sK2),sK0) | k1_xboole_0 = sK2) ) | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f12061,f177360])).
% 47.47/6.33  fof(f12061,plain,(
% 47.47/6.33    ( ! [X14,X12,X13] : (r2_hidden(sK7(k1_xboole_0,X14,k3_xboole_0(X12,X13)),X13) | k1_xboole_0 = k3_xboole_0(X12,X13)) )),
% 47.47/6.33    inference(resolution,[],[f12056,f79])).
% 47.47/6.33  fof(f12056,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK7(k1_xboole_0,X0,X1),X1) | k1_xboole_0 = X1) )),
% 47.47/6.33    inference(forward_demodulation,[],[f12055,f105])).
% 47.47/6.33  fof(f12055,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK7(k1_xboole_0,X0,X1),X1) | k3_xboole_0(k1_xboole_0,X0) = X1) )),
% 47.47/6.33    inference(condensation,[],[f12017])).
% 47.47/6.33  fof(f12017,plain,(
% 47.47/6.33    ( ! [X26,X24,X25] : (r2_hidden(sK7(k1_xboole_0,X24,X25),X25) | k3_xboole_0(k1_xboole_0,X24) = X25 | r2_hidden(sK7(k1_xboole_0,X24,X25),X26)) )),
% 47.47/6.33    inference(resolution,[],[f69,f124])).
% 47.47/6.33  fof(f69,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 47.47/6.33    inference(cnf_transformation,[],[f42])).
% 47.47/6.33  fof(f188342,plain,(
% 47.47/6.33    spl8_7 | spl8_150 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177443,f177358,f188340,f167])).
% 47.47/6.33  fof(f188340,plain,(
% 47.47/6.33    spl8_150 <=> ! [X66] : r2_hidden(sK6(X66,X66,sK2),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).
% 47.47/6.33  fof(f177443,plain,(
% 47.47/6.33    ( ! [X66] : (r2_hidden(sK6(X66,X66,sK2),sK0) | k1_xboole_0 = sK2) ) | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f6323,f177360])).
% 47.47/6.33  fof(f6323,plain,(
% 47.47/6.33    ( ! [X14,X15,X13] : (r2_hidden(sK6(X15,X15,k3_xboole_0(X13,X14)),X14) | k1_xboole_0 = k3_xboole_0(X13,X14)) )),
% 47.47/6.33    inference(resolution,[],[f6317,f79])).
% 47.47/6.33  fof(f6317,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK6(X0,X0,X1),X1) | k1_xboole_0 = X1) )),
% 47.47/6.33    inference(forward_demodulation,[],[f6316,f490])).
% 47.47/6.33  fof(f490,plain,(
% 47.47/6.33    ( ! [X14] : (k1_xboole_0 = k4_xboole_0(X14,X14)) )),
% 47.47/6.33    inference(superposition,[],[f482,f48])).
% 47.47/6.33  fof(f482,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k3_xboole_0(k4_xboole_0(X2,X2),X3)) )),
% 47.47/6.33    inference(resolution,[],[f480,f51])).
% 47.47/6.33  fof(f51,plain,(
% 47.47/6.33    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 47.47/6.33    inference(cnf_transformation,[],[f20])).
% 47.47/6.33  fof(f20,plain,(
% 47.47/6.33    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 47.47/6.33    inference(ennf_transformation,[],[f8])).
% 47.47/6.33  fof(f8,axiom,(
% 47.47/6.33    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 47.47/6.33  fof(f480,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f477])).
% 47.47/6.33  fof(f477,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1) | r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 47.47/6.33    inference(resolution,[],[f184,f53])).
% 47.47/6.33  fof(f184,plain,(
% 47.47/6.33    ( ! [X12,X10,X13,X11] : (~r2_hidden(sK4(k4_xboole_0(X10,X11),X12),k4_xboole_0(X13,X10)) | r1_tarski(k4_xboole_0(X10,X11),X12)) )),
% 47.47/6.33    inference(resolution,[],[f117,f76])).
% 47.47/6.33  fof(f117,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 47.47/6.33    inference(resolution,[],[f77,f53])).
% 47.47/6.33  fof(f77,plain,(
% 47.47/6.33    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 47.47/6.33    inference(equality_resolution,[],[f60])).
% 47.47/6.33  fof(f60,plain,(
% 47.47/6.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 47.47/6.33    inference(cnf_transformation,[],[f37])).
% 47.47/6.33  fof(f6316,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = X1 | r2_hidden(sK6(X0,X0,X1),X1)) )),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f6308])).
% 47.47/6.33  fof(f6308,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = X1 | r2_hidden(sK6(X0,X0,X1),X1) | r2_hidden(sK6(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 47.47/6.33    inference(resolution,[],[f64,f63])).
% 47.47/6.33  fof(f63,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 47.47/6.33    inference(cnf_transformation,[],[f37])).
% 47.47/6.33  fof(f64,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f37])).
% 47.47/6.33  fof(f188328,plain,(
% 47.47/6.33    spl8_7 | spl8_149 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177429,f177358,f188326,f167])).
% 47.47/6.33  fof(f188326,plain,(
% 47.47/6.33    spl8_149 <=> ! [X42] : r2_hidden(sK6(k1_xboole_0,X42,sK2),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).
% 47.47/6.33  fof(f177429,plain,(
% 47.47/6.33    ( ! [X42] : (r2_hidden(sK6(k1_xboole_0,X42,sK2),sK0) | k1_xboole_0 = sK2) ) | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f2428,f177360])).
% 47.47/6.33  fof(f2428,plain,(
% 47.47/6.33    ( ! [X14,X12,X13] : (r2_hidden(sK6(k1_xboole_0,X14,k3_xboole_0(X12,X13)),X13) | k1_xboole_0 = k3_xboole_0(X12,X13)) )),
% 47.47/6.33    inference(resolution,[],[f2344,f79])).
% 47.47/6.33  fof(f2344,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK6(k1_xboole_0,X0,X1),X1) | k1_xboole_0 = X1) )),
% 47.47/6.33    inference(forward_demodulation,[],[f2343,f47])).
% 47.47/6.33  fof(f47,plain,(
% 47.47/6.33    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f10])).
% 47.47/6.33  fof(f10,axiom,(
% 47.47/6.33    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 47.47/6.33  fof(f2343,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_hidden(sK6(k1_xboole_0,X0,X1),X1) | k4_xboole_0(k1_xboole_0,X0) = X1) )),
% 47.47/6.33    inference(condensation,[],[f2327])).
% 47.47/6.33  fof(f2327,plain,(
% 47.47/6.33    ( ! [X26,X24,X25] : (r2_hidden(sK6(k1_xboole_0,X24,X25),X25) | k4_xboole_0(k1_xboole_0,X24) = X25 | r2_hidden(sK6(k1_xboole_0,X24,X25),X26)) )),
% 47.47/6.33    inference(resolution,[],[f63,f124])).
% 47.47/6.33  fof(f188307,plain,(
% 47.47/6.33    spl8_3 | ~spl8_146 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177414,f177358,f188080,f92])).
% 47.47/6.33  fof(f177414,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK2,sK0),k1_xboole_0) | sK0 = sK2 | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f717,f177360])).
% 47.47/6.33  fof(f717,plain,(
% 47.47/6.33    ( ! [X0,X1] : (~r2_hidden(sK5(k3_xboole_0(X1,X0),X0),k1_xboole_0) | k3_xboole_0(X1,X0) = X0) )),
% 47.47/6.33    inference(superposition,[],[f393,f47])).
% 47.47/6.33  fof(f188306,plain,(
% 47.47/6.33    spl8_3 | spl8_141 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177406,f177358,f187449,f92])).
% 47.47/6.33  fof(f177406,plain,(
% 47.47/6.33    r2_hidden(sK5(sK2,sK0),sK0) | sK0 = sK2 | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f334,f177360])).
% 47.47/6.33  fof(f188305,plain,(
% 47.47/6.33    spl8_3 | ~spl8_140 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177405,f177358,f187444,f92])).
% 47.47/6.33  fof(f177405,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK2,sK0),sK2) | sK0 = sK2 | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f333,f177360])).
% 47.47/6.33  fof(f333,plain,(
% 47.47/6.33    ( ! [X0,X1] : (~r2_hidden(sK5(k3_xboole_0(X0,X1),X1),k3_xboole_0(X0,X1)) | k3_xboole_0(X0,X1) = X1) )),
% 47.47/6.33    inference(resolution,[],[f235,f59])).
% 47.47/6.33  fof(f59,plain,(
% 47.47/6.33    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK5(X0,X1),X0)) )),
% 47.47/6.33    inference(cnf_transformation,[],[f32])).
% 47.47/6.33  fof(f188304,plain,(
% 47.47/6.33    ~spl8_148 | ~spl8_21 | ~spl8_147),
% 47.47/6.33    inference(avatar_split_clause,[],[f188296,f188289,f4719,f188301])).
% 47.47/6.33  fof(f188301,plain,(
% 47.47/6.33    spl8_148 <=> r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).
% 47.47/6.33  fof(f4719,plain,(
% 47.47/6.33    spl8_21 <=> k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 47.47/6.33  fof(f188289,plain,(
% 47.47/6.33    spl8_147 <=> r2_hidden(sK5(k1_xboole_0,sK2),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).
% 47.47/6.33  fof(f188296,plain,(
% 47.47/6.33    ~r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0) | (~spl8_21 | ~spl8_147)),
% 47.47/6.33    inference(superposition,[],[f188295,f4721])).
% 47.47/6.33  fof(f4721,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl8_21),
% 47.47/6.33    inference(avatar_component_clause,[],[f4719])).
% 47.47/6.33  fof(f188295,plain,(
% 47.47/6.33    ( ! [X2] : (~r2_hidden(sK5(k1_xboole_0,sK2),k4_xboole_0(X2,sK0))) ) | ~spl8_147),
% 47.47/6.33    inference(resolution,[],[f188291,f76])).
% 47.47/6.33  fof(f188291,plain,(
% 47.47/6.33    r2_hidden(sK5(k1_xboole_0,sK2),sK0) | ~spl8_147),
% 47.47/6.33    inference(avatar_component_clause,[],[f188289])).
% 47.47/6.33  fof(f188292,plain,(
% 47.47/6.33    spl8_7 | spl8_147 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177395,f177358,f188289,f167])).
% 47.47/6.33  fof(f177395,plain,(
% 47.47/6.33    r2_hidden(sK5(k1_xboole_0,sK2),sK0) | k1_xboole_0 = sK2 | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f146,f177360])).
% 47.47/6.33  fof(f188083,plain,(
% 47.47/6.33    ~spl8_146 | ~spl8_21 | ~spl8_141),
% 47.47/6.33    inference(avatar_split_clause,[],[f188075,f187449,f4719,f188080])).
% 47.47/6.33  fof(f188075,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK2,sK0),k1_xboole_0) | (~spl8_21 | ~spl8_141)),
% 47.47/6.33    inference(superposition,[],[f187455,f4721])).
% 47.47/6.33  fof(f187455,plain,(
% 47.47/6.33    ( ! [X2] : (~r2_hidden(sK5(sK2,sK0),k4_xboole_0(X2,sK0))) ) | ~spl8_141),
% 47.47/6.33    inference(resolution,[],[f187451,f76])).
% 47.47/6.33  fof(f187521,plain,(
% 47.47/6.33    ~spl8_145 | ~spl8_4 | spl8_132),
% 47.47/6.33    inference(avatar_split_clause,[],[f185875,f182353,f96,f187518])).
% 47.47/6.33  fof(f187518,plain,(
% 47.47/6.33    spl8_145 <=> r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).
% 47.47/6.33  fof(f96,plain,(
% 47.47/6.33    spl8_4 <=> sK1 = sK3),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 47.47/6.33  fof(f182353,plain,(
% 47.47/6.33    spl8_132 <=> r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).
% 47.47/6.33  fof(f185875,plain,(
% 47.47/6.33    ~r2_hidden(sK5(k1_xboole_0,sK1),k1_xboole_0) | (~spl8_4 | spl8_132)),
% 47.47/6.33    inference(backward_demodulation,[],[f182355,f97])).
% 47.47/6.33  fof(f97,plain,(
% 47.47/6.33    sK1 = sK3 | ~spl8_4),
% 47.47/6.33    inference(avatar_component_clause,[],[f96])).
% 47.47/6.33  fof(f182355,plain,(
% 47.47/6.33    ~r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0) | spl8_132),
% 47.47/6.33    inference(avatar_component_clause,[],[f182353])).
% 47.47/6.33  fof(f187516,plain,(
% 47.47/6.33    ~spl8_144 | ~spl8_4 | spl8_130),
% 47.47/6.33    inference(avatar_split_clause,[],[f185866,f182261,f96,f187513])).
% 47.47/6.33  fof(f187513,plain,(
% 47.47/6.33    spl8_144 <=> r2_hidden(sK5(sK1,sK1),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).
% 47.47/6.33  fof(f182261,plain,(
% 47.47/6.33    spl8_130 <=> r2_hidden(sK5(sK3,sK1),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_130])])).
% 47.47/6.33  fof(f185866,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK1,sK1),k1_xboole_0) | (~spl8_4 | spl8_130)),
% 47.47/6.33    inference(backward_demodulation,[],[f182263,f97])).
% 47.47/6.33  fof(f182263,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK3,sK1),k1_xboole_0) | spl8_130),
% 47.47/6.33    inference(avatar_component_clause,[],[f182261])).
% 47.47/6.33  fof(f187508,plain,(
% 47.47/6.33    spl8_143 | ~spl8_4 | ~spl8_131),
% 47.47/6.33    inference(avatar_split_clause,[],[f185869,f182278,f96,f187505])).
% 47.47/6.33  fof(f187505,plain,(
% 47.47/6.33    spl8_143 <=> r2_hidden(sK5(k1_xboole_0,sK1),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).
% 47.47/6.33  fof(f182278,plain,(
% 47.47/6.33    spl8_131 <=> r2_hidden(sK5(k1_xboole_0,sK3),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).
% 47.47/6.33  fof(f185869,plain,(
% 47.47/6.33    r2_hidden(sK5(k1_xboole_0,sK1),sK1) | (~spl8_4 | ~spl8_131)),
% 47.47/6.33    inference(backward_demodulation,[],[f182280,f97])).
% 47.47/6.33  fof(f182280,plain,(
% 47.47/6.33    r2_hidden(sK5(k1_xboole_0,sK3),sK1) | ~spl8_131),
% 47.47/6.33    inference(avatar_component_clause,[],[f182278])).
% 47.47/6.33  fof(f187503,plain,(
% 47.47/6.33    ~spl8_142 | ~spl8_4 | spl8_128),
% 47.47/6.33    inference(avatar_split_clause,[],[f185826,f182172,f96,f187500])).
% 47.47/6.33  fof(f187500,plain,(
% 47.47/6.33    spl8_142 <=> r2_hidden(sK5(sK1,sK1),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).
% 47.47/6.33  fof(f182172,plain,(
% 47.47/6.33    spl8_128 <=> r2_hidden(sK5(sK3,sK1),sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).
% 47.47/6.33  fof(f185826,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK1,sK1),sK1) | (~spl8_4 | spl8_128)),
% 47.47/6.33    inference(backward_demodulation,[],[f182174,f97])).
% 47.47/6.33  fof(f182174,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK3,sK1),sK3) | spl8_128),
% 47.47/6.33    inference(avatar_component_clause,[],[f182172])).
% 47.47/6.33  fof(f187452,plain,(
% 47.47/6.33    spl8_141 | ~spl8_119),
% 47.47/6.33    inference(avatar_split_clause,[],[f187002,f178185,f187449])).
% 47.47/6.33  fof(f178185,plain,(
% 47.47/6.33    spl8_119 <=> r2_xboole_0(sK2,sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).
% 47.47/6.33  fof(f187002,plain,(
% 47.47/6.33    r2_hidden(sK5(sK2,sK0),sK0) | ~spl8_119),
% 47.47/6.33    inference(resolution,[],[f178187,f58])).
% 47.47/6.33  fof(f178187,plain,(
% 47.47/6.33    r2_xboole_0(sK2,sK0) | ~spl8_119),
% 47.47/6.33    inference(avatar_component_clause,[],[f178185])).
% 47.47/6.33  fof(f187447,plain,(
% 47.47/6.33    ~spl8_140 | ~spl8_119),
% 47.47/6.33    inference(avatar_split_clause,[],[f187001,f178185,f187444])).
% 47.47/6.33  fof(f187001,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK2,sK0),sK2) | ~spl8_119),
% 47.47/6.33    inference(resolution,[],[f178187,f59])).
% 47.47/6.33  fof(f187007,plain,(
% 47.47/6.33    ~spl8_139 | ~spl8_4 | spl8_127),
% 47.47/6.33    inference(avatar_split_clause,[],[f185825,f182128,f96,f187004])).
% 47.47/6.33  fof(f187004,plain,(
% 47.47/6.33    spl8_139 <=> r2_xboole_0(sK1,sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_139])])).
% 47.47/6.33  fof(f182128,plain,(
% 47.47/6.33    spl8_127 <=> r2_xboole_0(sK3,sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).
% 47.47/6.33  fof(f185825,plain,(
% 47.47/6.33    ~r2_xboole_0(sK1,sK1) | (~spl8_4 | spl8_127)),
% 47.47/6.33    inference(backward_demodulation,[],[f182129,f97])).
% 47.47/6.33  fof(f182129,plain,(
% 47.47/6.33    ~r2_xboole_0(sK3,sK1) | spl8_127),
% 47.47/6.33    inference(avatar_component_clause,[],[f182128])).
% 47.47/6.33  fof(f184286,plain,(
% 47.47/6.33    spl8_128 | spl8_130 | ~spl8_10 | ~spl8_129),
% 47.47/6.33    inference(avatar_split_clause,[],[f184282,f182177,f1451,f182261,f182172])).
% 47.47/6.33  fof(f1451,plain,(
% 47.47/6.33    spl8_10 <=> k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 47.47/6.33  fof(f182177,plain,(
% 47.47/6.33    spl8_129 <=> r2_hidden(sK5(sK3,sK1),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).
% 47.47/6.33  fof(f184282,plain,(
% 47.47/6.33    r2_hidden(sK5(sK3,sK1),k1_xboole_0) | r2_hidden(sK5(sK3,sK1),sK3) | (~spl8_10 | ~spl8_129)),
% 47.47/6.33    inference(superposition,[],[f182182,f1453])).
% 47.47/6.33  fof(f1453,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl8_10),
% 47.47/6.33    inference(avatar_component_clause,[],[f1451])).
% 47.47/6.33  fof(f182182,plain,(
% 47.47/6.33    ( ! [X1] : (r2_hidden(sK5(sK3,sK1),k4_xboole_0(sK1,X1)) | r2_hidden(sK5(sK3,sK1),X1)) ) | ~spl8_129),
% 47.47/6.33    inference(resolution,[],[f182179,f75])).
% 47.47/6.33  fof(f182179,plain,(
% 47.47/6.33    r2_hidden(sK5(sK3,sK1),sK1) | ~spl8_129),
% 47.47/6.33    inference(avatar_component_clause,[],[f182177])).
% 47.47/6.33  fof(f182783,plain,(
% 47.47/6.33    spl8_6 | spl8_138 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181304,f181261,f182781,f163])).
% 47.47/6.33  fof(f163,plain,(
% 47.47/6.33    spl8_6 <=> k1_xboole_0 = sK3),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 47.47/6.33  fof(f182781,plain,(
% 47.47/6.33    spl8_138 <=> ! [X19] : ~r2_hidden(sK5(k1_xboole_0,sK3),k4_xboole_0(X19,sK1))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).
% 47.47/6.33  fof(f181261,plain,(
% 47.47/6.33    spl8_125 <=> sK3 = k3_xboole_0(sK3,sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_125])])).
% 47.47/6.33  fof(f181304,plain,(
% 47.47/6.33    ( ! [X19] : (~r2_hidden(sK5(k1_xboole_0,sK3),k4_xboole_0(X19,sK1)) | k1_xboole_0 = sK3) ) | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f449,f181263])).
% 47.47/6.33  fof(f181263,plain,(
% 47.47/6.33    sK3 = k3_xboole_0(sK3,sK1) | ~spl8_125),
% 47.47/6.33    inference(avatar_component_clause,[],[f181261])).
% 47.47/6.33  fof(f182779,plain,(
% 47.47/6.33    spl8_4 | spl8_137 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181301,f181261,f182777,f96])).
% 47.47/6.33  fof(f182777,plain,(
% 47.47/6.33    spl8_137 <=> ! [X16] : ~r2_hidden(sK5(sK3,sK1),k4_xboole_0(X16,sK1))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).
% 47.47/6.33  fof(f181301,plain,(
% 47.47/6.33    ( ! [X16] : (~r2_hidden(sK5(sK3,sK1),k4_xboole_0(X16,sK1)) | sK1 = sK3) ) | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f393,f181263])).
% 47.47/6.33  fof(f182411,plain,(
% 47.47/6.33    spl8_6 | spl8_136 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181366,f181261,f182409,f163])).
% 47.47/6.33  fof(f182409,plain,(
% 47.47/6.33    spl8_136 <=> ! [X119] : r2_hidden(sK7(X119,k1_xboole_0,sK3),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_136])])).
% 47.47/6.33  fof(f181366,plain,(
% 47.47/6.33    ( ! [X119] : (r2_hidden(sK7(X119,k1_xboole_0,sK3),sK1) | k1_xboole_0 = sK3) ) | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f29246,f181263])).
% 47.47/6.33  fof(f182394,plain,(
% 47.47/6.33    spl8_6 | spl8_135 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181336,f181261,f182392,f163])).
% 47.47/6.33  fof(f182392,plain,(
% 47.47/6.33    spl8_135 <=> ! [X69] : r2_hidden(sK7(k1_xboole_0,X69,sK3),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_135])])).
% 47.47/6.33  fof(f181336,plain,(
% 47.47/6.33    ( ! [X69] : (r2_hidden(sK7(k1_xboole_0,X69,sK3),sK1) | k1_xboole_0 = sK3) ) | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f12061,f181263])).
% 47.47/6.33  fof(f182377,plain,(
% 47.47/6.33    spl8_6 | spl8_134 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181334,f181261,f182375,f163])).
% 47.47/6.33  fof(f182375,plain,(
% 47.47/6.33    spl8_134 <=> ! [X67] : r2_hidden(sK6(X67,X67,sK3),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).
% 47.47/6.33  fof(f181334,plain,(
% 47.47/6.33    ( ! [X67] : (r2_hidden(sK6(X67,X67,sK3),sK1) | k1_xboole_0 = sK3) ) | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f6323,f181263])).
% 47.47/6.33  fof(f182363,plain,(
% 47.47/6.33    spl8_6 | spl8_133 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181320,f181261,f182361,f163])).
% 47.47/6.33  fof(f182361,plain,(
% 47.47/6.33    spl8_133 <=> ! [X43] : r2_hidden(sK6(k1_xboole_0,X43,sK3),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).
% 47.47/6.33  fof(f181320,plain,(
% 47.47/6.33    ( ! [X43] : (r2_hidden(sK6(k1_xboole_0,X43,sK3),sK1) | k1_xboole_0 = sK3) ) | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f2428,f181263])).
% 47.47/6.33  fof(f182359,plain,(
% 47.47/6.33    spl8_4 | ~spl8_130 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181305,f181261,f182261,f96])).
% 47.47/6.33  fof(f181305,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK3,sK1),k1_xboole_0) | sK1 = sK3 | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f717,f181263])).
% 47.47/6.33  fof(f182358,plain,(
% 47.47/6.33    spl8_4 | spl8_129 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181297,f181261,f182177,f96])).
% 47.47/6.33  fof(f181297,plain,(
% 47.47/6.33    r2_hidden(sK5(sK3,sK1),sK1) | sK1 = sK3 | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f334,f181263])).
% 47.47/6.33  fof(f182357,plain,(
% 47.47/6.33    spl8_4 | ~spl8_128 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181296,f181261,f182172,f96])).
% 47.47/6.33  fof(f181296,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK3,sK1),sK3) | sK1 = sK3 | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f333,f181263])).
% 47.47/6.33  fof(f182356,plain,(
% 47.47/6.33    ~spl8_132 | ~spl8_13 | ~spl8_131),
% 47.47/6.33    inference(avatar_split_clause,[],[f182348,f182278,f1986,f182353])).
% 47.47/6.33  fof(f1986,plain,(
% 47.47/6.33    spl8_13 <=> k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 47.47/6.33  fof(f182348,plain,(
% 47.47/6.33    ~r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0) | (~spl8_13 | ~spl8_131)),
% 47.47/6.33    inference(superposition,[],[f182284,f1988])).
% 47.47/6.33  fof(f1988,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(sK3,sK1) | ~spl8_13),
% 47.47/6.33    inference(avatar_component_clause,[],[f1986])).
% 47.47/6.33  fof(f182284,plain,(
% 47.47/6.33    ( ! [X2] : (~r2_hidden(sK5(k1_xboole_0,sK3),k4_xboole_0(X2,sK1))) ) | ~spl8_131),
% 47.47/6.33    inference(resolution,[],[f182280,f76])).
% 47.47/6.33  fof(f182281,plain,(
% 47.47/6.33    spl8_6 | spl8_131 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181286,f181261,f182278,f163])).
% 47.47/6.33  fof(f181286,plain,(
% 47.47/6.33    r2_hidden(sK5(k1_xboole_0,sK3),sK1) | k1_xboole_0 = sK3 | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f146,f181263])).
% 47.47/6.33  fof(f182264,plain,(
% 47.47/6.33    ~spl8_130 | ~spl8_13 | ~spl8_129),
% 47.47/6.33    inference(avatar_split_clause,[],[f182256,f182177,f1986,f182261])).
% 47.47/6.33  fof(f182256,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK3,sK1),k1_xboole_0) | (~spl8_13 | ~spl8_129)),
% 47.47/6.33    inference(superposition,[],[f182183,f1988])).
% 47.47/6.33  fof(f182183,plain,(
% 47.47/6.33    ( ! [X2] : (~r2_hidden(sK5(sK3,sK1),k4_xboole_0(X2,sK1))) ) | ~spl8_129),
% 47.47/6.33    inference(resolution,[],[f182179,f76])).
% 47.47/6.33  fof(f182227,plain,(
% 47.47/6.33    spl8_4 | spl8_127 | ~spl8_126),
% 47.47/6.33    inference(avatar_split_clause,[],[f182005,f181978,f182128,f96])).
% 47.47/6.33  fof(f181978,plain,(
% 47.47/6.33    spl8_126 <=> sK3 = k3_xboole_0(sK1,sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).
% 47.47/6.33  fof(f182005,plain,(
% 47.47/6.33    r2_xboole_0(sK3,sK1) | sK1 = sK3 | ~spl8_126),
% 47.47/6.33    inference(superposition,[],[f244,f181980])).
% 47.47/6.33  fof(f181980,plain,(
% 47.47/6.33    sK3 = k3_xboole_0(sK1,sK3) | ~spl8_126),
% 47.47/6.33    inference(avatar_component_clause,[],[f181978])).
% 47.47/6.33  fof(f244,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r2_xboole_0(k3_xboole_0(X0,X1),X0) | k3_xboole_0(X0,X1) = X0) )),
% 47.47/6.33    inference(resolution,[],[f238,f52])).
% 47.47/6.33  fof(f238,plain,(
% 47.47/6.33    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X2)) )),
% 47.47/6.33    inference(superposition,[],[f232,f50])).
% 47.47/6.33  fof(f182180,plain,(
% 47.47/6.33    spl8_129 | ~spl8_127),
% 47.47/6.33    inference(avatar_split_clause,[],[f182136,f182128,f182177])).
% 47.47/6.33  fof(f182136,plain,(
% 47.47/6.33    r2_hidden(sK5(sK3,sK1),sK1) | ~spl8_127),
% 47.47/6.33    inference(resolution,[],[f182130,f58])).
% 47.47/6.33  fof(f182130,plain,(
% 47.47/6.33    r2_xboole_0(sK3,sK1) | ~spl8_127),
% 47.47/6.33    inference(avatar_component_clause,[],[f182128])).
% 47.47/6.33  fof(f182175,plain,(
% 47.47/6.33    ~spl8_128 | ~spl8_127),
% 47.47/6.33    inference(avatar_split_clause,[],[f182135,f182128,f182172])).
% 47.47/6.33  fof(f182135,plain,(
% 47.47/6.33    ~r2_hidden(sK5(sK3,sK1),sK3) | ~spl8_127),
% 47.47/6.33    inference(resolution,[],[f182130,f59])).
% 47.47/6.33  fof(f182170,plain,(
% 47.47/6.33    ~spl8_124),
% 47.47/6.33    inference(avatar_contradiction_clause,[],[f182164])).
% 47.47/6.33  fof(f182164,plain,(
% 47.47/6.33    $false | ~spl8_124),
% 47.47/6.33    inference(resolution,[],[f182143,f182138])).
% 47.47/6.33  fof(f182138,plain,(
% 47.47/6.33    ( ! [X0] : (r2_hidden(sK4(sK3,sK1),X0)) ) | ~spl8_124),
% 47.47/6.33    inference(resolution,[],[f181256,f124])).
% 47.47/6.33  fof(f181256,plain,(
% 47.47/6.33    r2_hidden(sK4(sK3,sK1),k1_xboole_0) | ~spl8_124),
% 47.47/6.33    inference(avatar_component_clause,[],[f181254])).
% 47.47/6.33  fof(f181254,plain,(
% 47.47/6.33    spl8_124 <=> r2_hidden(sK4(sK3,sK1),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).
% 47.47/6.33  fof(f182143,plain,(
% 47.47/6.33    ( ! [X3] : (~r2_hidden(sK4(sK3,sK1),X3)) ) | ~spl8_124),
% 47.47/6.33    inference(forward_demodulation,[],[f182141,f99909])).
% 47.47/6.33  fof(f99909,plain,(
% 47.47/6.33    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 47.47/6.33    inference(superposition,[],[f99875,f200])).
% 47.47/6.33  fof(f200,plain,(
% 47.47/6.33    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 47.47/6.33    inference(superposition,[],[f196,f50])).
% 47.47/6.33  fof(f196,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 47.47/6.33    inference(resolution,[],[f192,f51])).
% 47.47/6.33  fof(f192,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f181])).
% 47.47/6.33  fof(f181,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 47.47/6.33    inference(resolution,[],[f117,f54])).
% 47.47/6.33  fof(f99875,plain,(
% 47.47/6.33    ( ! [X1] : (k3_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X1) )),
% 47.47/6.33    inference(resolution,[],[f99869,f51])).
% 47.47/6.33  fof(f99869,plain,(
% 47.47/6.33    ( ! [X29] : (r1_tarski(X29,k4_xboole_0(X29,k1_xboole_0))) )),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f99841])).
% 47.47/6.33  fof(f99841,plain,(
% 47.47/6.33    ( ! [X29] : (r1_tarski(X29,k4_xboole_0(X29,k1_xboole_0)) | r1_tarski(X29,k4_xboole_0(X29,k1_xboole_0))) )),
% 47.47/6.33    inference(resolution,[],[f84569,f152])).
% 47.47/6.33  fof(f152,plain,(
% 47.47/6.33    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 47.47/6.33    inference(superposition,[],[f116,f47])).
% 47.47/6.33  fof(f116,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X0)) | r1_tarski(X0,X1)) )),
% 47.47/6.33    inference(resolution,[],[f76,f53])).
% 47.47/6.33  fof(f84569,plain,(
% 47.47/6.33    ( ! [X14,X15] : (r2_hidden(sK4(X14,k4_xboole_0(X14,X15)),X15) | r1_tarski(X14,k4_xboole_0(X14,X15))) )),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f84542])).
% 47.47/6.33  fof(f84542,plain,(
% 47.47/6.33    ( ! [X14,X15] : (r2_hidden(sK4(X14,k4_xboole_0(X14,X15)),X15) | r1_tarski(X14,k4_xboole_0(X14,X15)) | r1_tarski(X14,k4_xboole_0(X14,X15))) )),
% 47.47/6.33    inference(resolution,[],[f175,f54])).
% 47.47/6.33  fof(f175,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,X2)) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 47.47/6.33    inference(resolution,[],[f75,f53])).
% 47.47/6.33  fof(f182141,plain,(
% 47.47/6.33    ( ! [X3] : (~r2_hidden(sK4(sK3,sK1),k4_xboole_0(X3,k1_xboole_0))) ) | ~spl8_124),
% 47.47/6.33    inference(resolution,[],[f181256,f76])).
% 47.47/6.33  fof(f182169,plain,(
% 47.47/6.33    ~spl8_124),
% 47.47/6.33    inference(avatar_contradiction_clause,[],[f182167])).
% 47.47/6.33  fof(f182167,plain,(
% 47.47/6.33    $false | ~spl8_124),
% 47.47/6.33    inference(resolution,[],[f182143,f181256])).
% 47.47/6.33  fof(f182132,plain,(
% 47.47/6.33    spl8_123 | ~spl8_126),
% 47.47/6.33    inference(avatar_split_clause,[],[f182004,f181978,f181250])).
% 47.47/6.33  fof(f181250,plain,(
% 47.47/6.33    spl8_123 <=> r1_tarski(sK3,sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).
% 47.47/6.33  fof(f182004,plain,(
% 47.47/6.33    r1_tarski(sK3,sK1) | ~spl8_126),
% 47.47/6.33    inference(superposition,[],[f238,f181980])).
% 47.47/6.33  fof(f182131,plain,(
% 47.47/6.33    spl8_127 | spl8_4 | ~spl8_123),
% 47.47/6.33    inference(avatar_split_clause,[],[f181258,f181250,f96,f182128])).
% 47.47/6.33  fof(f181258,plain,(
% 47.47/6.33    sK1 = sK3 | r2_xboole_0(sK3,sK1) | ~spl8_123),
% 47.47/6.33    inference(resolution,[],[f181252,f52])).
% 47.47/6.33  fof(f181252,plain,(
% 47.47/6.33    r1_tarski(sK3,sK1) | ~spl8_123),
% 47.47/6.33    inference(avatar_component_clause,[],[f181250])).
% 47.47/6.33  fof(f181981,plain,(
% 47.47/6.33    spl8_126 | ~spl8_125),
% 47.47/6.33    inference(avatar_split_clause,[],[f181265,f181261,f181978])).
% 47.47/6.33  fof(f181265,plain,(
% 47.47/6.33    sK3 = k3_xboole_0(sK1,sK3) | ~spl8_125),
% 47.47/6.33    inference(superposition,[],[f181263,f50])).
% 47.47/6.33  fof(f181264,plain,(
% 47.47/6.33    spl8_125 | ~spl8_123),
% 47.47/6.33    inference(avatar_split_clause,[],[f181259,f181250,f181261])).
% 47.47/6.33  fof(f181259,plain,(
% 47.47/6.33    sK3 = k3_xboole_0(sK3,sK1) | ~spl8_123),
% 47.47/6.33    inference(resolution,[],[f181252,f51])).
% 47.47/6.33  fof(f181257,plain,(
% 47.47/6.33    spl8_123 | spl8_124 | ~spl8_13),
% 47.47/6.33    inference(avatar_split_clause,[],[f181247,f1986,f181254,f181250])).
% 47.47/6.33  fof(f181247,plain,(
% 47.47/6.33    r2_hidden(sK4(sK3,sK1),k1_xboole_0) | r1_tarski(sK3,sK1) | ~spl8_13),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f181241])).
% 47.47/6.33  fof(f181241,plain,(
% 47.47/6.33    r2_hidden(sK4(sK3,sK1),k1_xboole_0) | r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl8_13),
% 47.47/6.33    inference(resolution,[],[f84559,f54])).
% 47.47/6.33  fof(f84559,plain,(
% 47.47/6.33    ( ! [X22] : (r2_hidden(sK4(sK3,X22),sK1) | r2_hidden(sK4(sK3,X22),k1_xboole_0) | r1_tarski(sK3,X22)) ) | ~spl8_13),
% 47.47/6.33    inference(superposition,[],[f175,f1988])).
% 47.47/6.33  fof(f180946,plain,(
% 47.47/6.33    ~spl8_122 | ~spl8_49 | spl8_52),
% 47.47/6.33    inference(avatar_split_clause,[],[f178248,f33035,f33013,f180943])).
% 47.47/6.33  fof(f180943,plain,(
% 47.47/6.33    spl8_122 <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).
% 47.47/6.33  fof(f33013,plain,(
% 47.47/6.33    spl8_49 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 47.47/6.33  fof(f33035,plain,(
% 47.47/6.33    spl8_52 <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 47.47/6.33  fof(f178248,plain,(
% 47.47/6.33    ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k1_xboole_0) | (~spl8_49 | spl8_52)),
% 47.47/6.33    inference(backward_demodulation,[],[f33037,f33015])).
% 47.47/6.33  fof(f33015,plain,(
% 47.47/6.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) | ~spl8_49),
% 47.47/6.33    inference(avatar_component_clause,[],[f33013])).
% 47.47/6.33  fof(f33037,plain,(
% 47.47/6.33    ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k1_xboole_0) | spl8_52),
% 47.47/6.33    inference(avatar_component_clause,[],[f33035])).
% 47.47/6.33  fof(f180938,plain,(
% 47.47/6.33    spl8_121 | ~spl8_49 | ~spl8_53),
% 47.47/6.33    inference(avatar_split_clause,[],[f178249,f34046,f33013,f180935])).
% 47.47/6.33  fof(f180935,plain,(
% 47.47/6.33    spl8_121 <=> r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_121])])).
% 47.47/6.33  fof(f34046,plain,(
% 47.47/6.33    spl8_53 <=> r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 47.47/6.33  fof(f178249,plain,(
% 47.47/6.33    r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | (~spl8_49 | ~spl8_53)),
% 47.47/6.33    inference(backward_demodulation,[],[f34048,f33015])).
% 47.47/6.33  fof(f34048,plain,(
% 47.47/6.33    r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) | ~spl8_53),
% 47.47/6.33    inference(avatar_component_clause,[],[f34046])).
% 47.47/6.33  fof(f180825,plain,(
% 47.47/6.33    ~spl8_120 | ~spl8_3 | spl8_65),
% 47.47/6.33    inference(avatar_split_clause,[],[f179426,f43880,f92,f180822])).
% 47.47/6.33  fof(f180822,plain,(
% 47.47/6.33    spl8_120 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).
% 47.47/6.33  fof(f43880,plain,(
% 47.47/6.33    spl8_65 <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).
% 47.47/6.33  fof(f179426,plain,(
% 47.47/6.33    k1_xboole_0 != k2_zfmisc_1(sK0,sK3) | (~spl8_3 | spl8_65)),
% 47.47/6.33    inference(backward_demodulation,[],[f43882,f93])).
% 47.47/6.33  fof(f93,plain,(
% 47.47/6.33    sK0 = sK2 | ~spl8_3),
% 47.47/6.33    inference(avatar_component_clause,[],[f92])).
% 47.47/6.33  fof(f43882,plain,(
% 47.47/6.33    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) | spl8_65),
% 47.47/6.33    inference(avatar_component_clause,[],[f43880])).
% 47.47/6.33  fof(f178188,plain,(
% 47.47/6.33    spl8_119 | spl8_3 | ~spl8_114),
% 47.47/6.33    inference(avatar_split_clause,[],[f177370,f177347,f92,f178185])).
% 47.47/6.33  fof(f177347,plain,(
% 47.47/6.33    spl8_114 <=> r1_tarski(sK2,sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).
% 47.47/6.33  fof(f177370,plain,(
% 47.47/6.33    sK0 = sK2 | r2_xboole_0(sK2,sK0) | ~spl8_114),
% 47.47/6.33    inference(resolution,[],[f177349,f52])).
% 47.47/6.33  fof(f177349,plain,(
% 47.47/6.33    r1_tarski(sK2,sK0) | ~spl8_114),
% 47.47/6.33    inference(avatar_component_clause,[],[f177347])).
% 47.47/6.33  fof(f178182,plain,(
% 47.47/6.33    ~spl8_118 | spl8_69 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177668,f177358,f44927,f178179])).
% 47.47/6.33  fof(f178179,plain,(
% 47.47/6.33    spl8_118 <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).
% 47.47/6.33  fof(f44927,plain,(
% 47.47/6.33    spl8_69 <=> k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).
% 47.47/6.33  fof(f177668,plain,(
% 47.47/6.33    k1_xboole_0 != k2_zfmisc_1(sK2,sK1) | (spl8_69 | ~spl8_116)),
% 47.47/6.33    inference(backward_demodulation,[],[f44929,f177372])).
% 47.47/6.33  fof(f177372,plain,(
% 47.47/6.33    sK2 = k3_xboole_0(sK0,sK2) | ~spl8_116),
% 47.47/6.33    inference(superposition,[],[f177360,f50])).
% 47.47/6.33  fof(f44929,plain,(
% 47.47/6.33    k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | spl8_69),
% 47.47/6.33    inference(avatar_component_clause,[],[f44927])).
% 47.47/6.33  fof(f178027,plain,(
% 47.47/6.33    spl8_117 | ~spl8_116),
% 47.47/6.33    inference(avatar_split_clause,[],[f177372,f177358,f178024])).
% 47.47/6.33  fof(f178024,plain,(
% 47.47/6.33    spl8_117 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).
% 47.47/6.33  fof(f177369,plain,(
% 47.47/6.33    spl8_114 | ~spl8_115),
% 47.47/6.33    inference(avatar_split_clause,[],[f177362,f177351,f177347])).
% 47.47/6.33  fof(f177351,plain,(
% 47.47/6.33    spl8_115 <=> r2_hidden(sK4(sK2,sK0),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).
% 47.47/6.33  fof(f177362,plain,(
% 47.47/6.33    r1_tarski(sK2,sK0) | ~spl8_115),
% 47.47/6.33    inference(resolution,[],[f177353,f152])).
% 47.47/6.33  fof(f177353,plain,(
% 47.47/6.33    r2_hidden(sK4(sK2,sK0),k1_xboole_0) | ~spl8_115),
% 47.47/6.33    inference(avatar_component_clause,[],[f177351])).
% 47.47/6.33  fof(f177361,plain,(
% 47.47/6.33    spl8_116 | ~spl8_114),
% 47.47/6.33    inference(avatar_split_clause,[],[f177356,f177347,f177358])).
% 47.47/6.33  fof(f177356,plain,(
% 47.47/6.33    sK2 = k3_xboole_0(sK2,sK0) | ~spl8_114),
% 47.47/6.33    inference(resolution,[],[f177349,f51])).
% 47.47/6.33  fof(f177354,plain,(
% 47.47/6.33    spl8_114 | spl8_115 | ~spl8_21),
% 47.47/6.33    inference(avatar_split_clause,[],[f177344,f4719,f177351,f177347])).
% 47.47/6.33  fof(f177344,plain,(
% 47.47/6.33    r2_hidden(sK4(sK2,sK0),k1_xboole_0) | r1_tarski(sK2,sK0) | ~spl8_21),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f177338])).
% 47.47/6.33  fof(f177338,plain,(
% 47.47/6.33    r2_hidden(sK4(sK2,sK0),k1_xboole_0) | r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0) | ~spl8_21),
% 47.47/6.33    inference(resolution,[],[f84558,f54])).
% 47.47/6.33  fof(f84558,plain,(
% 47.47/6.33    ( ! [X21] : (r2_hidden(sK4(sK2,X21),sK0) | r2_hidden(sK4(sK2,X21),k1_xboole_0) | r1_tarski(sK2,X21)) ) | ~spl8_21),
% 47.47/6.33    inference(superposition,[],[f175,f4721])).
% 47.47/6.33  fof(f163556,plain,(
% 47.47/6.33    spl8_113 | ~spl8_112),
% 47.47/6.33    inference(avatar_split_clause,[],[f163545,f163540,f163553])).
% 47.47/6.33  fof(f163553,plain,(
% 47.47/6.33    spl8_113 <=> r2_hidden(sK4(sK2,k1_xboole_0),sK2)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).
% 47.47/6.33  fof(f163540,plain,(
% 47.47/6.33    spl8_112 <=> r2_hidden(sK4(sK2,k1_xboole_0),k3_xboole_0(sK0,sK2))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).
% 47.47/6.33  fof(f163545,plain,(
% 47.47/6.33    r2_hidden(sK4(sK2,k1_xboole_0),sK2) | ~spl8_112),
% 47.47/6.33    inference(resolution,[],[f163542,f79])).
% 47.47/6.33  fof(f163542,plain,(
% 47.47/6.33    r2_hidden(sK4(sK2,k1_xboole_0),k3_xboole_0(sK0,sK2)) | ~spl8_112),
% 47.47/6.33    inference(avatar_component_clause,[],[f163540])).
% 47.47/6.33  fof(f163543,plain,(
% 47.47/6.33    spl8_94 | spl8_112 | ~spl8_45),
% 47.47/6.33    inference(avatar_split_clause,[],[f99861,f12170,f163540,f100443])).
% 47.47/6.33  fof(f100443,plain,(
% 47.47/6.33    spl8_94 <=> r1_tarski(sK2,k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).
% 47.47/6.33  fof(f12170,plain,(
% 47.47/6.33    spl8_45 <=> k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 47.47/6.33  fof(f99861,plain,(
% 47.47/6.33    r2_hidden(sK4(sK2,k1_xboole_0),k3_xboole_0(sK0,sK2)) | r1_tarski(sK2,k1_xboole_0) | ~spl8_45),
% 47.47/6.33    inference(superposition,[],[f84569,f12172])).
% 47.47/6.33  fof(f12172,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)) | ~spl8_45),
% 47.47/6.33    inference(avatar_component_clause,[],[f12170])).
% 47.47/6.33  fof(f163520,plain,(
% 47.47/6.33    spl8_111 | ~spl8_110),
% 47.47/6.33    inference(avatar_split_clause,[],[f163509,f163504,f163517])).
% 47.47/6.33  fof(f163517,plain,(
% 47.47/6.33    spl8_111 <=> r2_hidden(sK4(sK3,k1_xboole_0),sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).
% 47.47/6.33  fof(f163504,plain,(
% 47.47/6.33    spl8_110 <=> r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).
% 47.47/6.33  fof(f163509,plain,(
% 47.47/6.33    r2_hidden(sK4(sK3,k1_xboole_0),sK3) | ~spl8_110),
% 47.47/6.33    inference(resolution,[],[f163506,f79])).
% 47.47/6.33  fof(f163506,plain,(
% 47.47/6.33    r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3)) | ~spl8_110),
% 47.47/6.33    inference(avatar_component_clause,[],[f163504])).
% 47.47/6.33  fof(f163507,plain,(
% 47.47/6.33    spl8_97 | spl8_110 | ~spl8_43),
% 47.47/6.33    inference(avatar_split_clause,[],[f99862,f10042,f163504,f114015])).
% 47.47/6.33  fof(f114015,plain,(
% 47.47/6.33    spl8_97 <=> r1_tarski(sK3,k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).
% 47.47/6.33  fof(f10042,plain,(
% 47.47/6.33    spl8_43 <=> k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 47.47/6.33  fof(f99862,plain,(
% 47.47/6.33    r2_hidden(sK4(sK3,k1_xboole_0),k3_xboole_0(sK1,sK3)) | r1_tarski(sK3,k1_xboole_0) | ~spl8_43),
% 47.47/6.33    inference(superposition,[],[f84569,f10044])).
% 47.47/6.33  fof(f10044,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) | ~spl8_43),
% 47.47/6.33    inference(avatar_component_clause,[],[f10042])).
% 47.47/6.33  fof(f163105,plain,(
% 47.47/6.33    spl8_109 | ~spl8_108),
% 47.47/6.33    inference(avatar_split_clause,[],[f163093,f163089,f163102])).
% 47.47/6.33  fof(f163102,plain,(
% 47.47/6.33    spl8_109 <=> r2_hidden(sK4(sK1,k1_xboole_0),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).
% 47.47/6.33  fof(f163089,plain,(
% 47.47/6.33    spl8_108 <=> r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).
% 47.47/6.33  fof(f163093,plain,(
% 47.47/6.33    r2_hidden(sK4(sK1,k1_xboole_0),sK1) | ~spl8_108),
% 47.47/6.33    inference(resolution,[],[f163091,f80])).
% 47.47/6.33  fof(f80,plain,(
% 47.47/6.33    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 47.47/6.33    inference(equality_resolution,[],[f66])).
% 47.47/6.33  fof(f66,plain,(
% 47.47/6.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 47.47/6.33    inference(cnf_transformation,[],[f42])).
% 47.47/6.33  fof(f163091,plain,(
% 47.47/6.33    r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3)) | ~spl8_108),
% 47.47/6.33    inference(avatar_component_clause,[],[f163089])).
% 47.47/6.33  fof(f163092,plain,(
% 47.47/6.33    spl8_103 | spl8_108 | ~spl8_31),
% 47.47/6.33    inference(avatar_split_clause,[],[f99860,f6783,f163089,f144042])).
% 47.47/6.33  fof(f144042,plain,(
% 47.47/6.33    spl8_103 <=> r1_tarski(sK1,k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).
% 47.47/6.33  fof(f6783,plain,(
% 47.47/6.33    spl8_31 <=> k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 47.47/6.33  fof(f99860,plain,(
% 47.47/6.33    r2_hidden(sK4(sK1,k1_xboole_0),k3_xboole_0(sK1,sK3)) | r1_tarski(sK1,k1_xboole_0) | ~spl8_31),
% 47.47/6.33    inference(superposition,[],[f84569,f6785])).
% 47.47/6.33  fof(f6785,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl8_31),
% 47.47/6.33    inference(avatar_component_clause,[],[f6783])).
% 47.47/6.33  fof(f163070,plain,(
% 47.47/6.33    spl8_107 | ~spl8_106),
% 47.47/6.33    inference(avatar_split_clause,[],[f163058,f163054,f163067])).
% 47.47/6.33  fof(f163067,plain,(
% 47.47/6.33    spl8_107 <=> r2_hidden(sK4(sK0,k1_xboole_0),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).
% 47.47/6.33  fof(f163054,plain,(
% 47.47/6.33    spl8_106 <=> r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,sK2))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).
% 47.47/6.33  fof(f163058,plain,(
% 47.47/6.33    r2_hidden(sK4(sK0,k1_xboole_0),sK0) | ~spl8_106),
% 47.47/6.33    inference(resolution,[],[f163056,f80])).
% 47.47/6.33  fof(f163056,plain,(
% 47.47/6.33    r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,sK2)) | ~spl8_106),
% 47.47/6.33    inference(avatar_component_clause,[],[f163054])).
% 47.47/6.33  fof(f163057,plain,(
% 47.47/6.33    spl8_100 | spl8_106 | ~spl8_40),
% 47.47/6.33    inference(avatar_split_clause,[],[f99859,f9209,f163054,f128122])).
% 47.47/6.33  fof(f128122,plain,(
% 47.47/6.33    spl8_100 <=> r1_tarski(sK0,k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).
% 47.47/6.33  fof(f9209,plain,(
% 47.47/6.33    spl8_40 <=> k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 47.47/6.33  fof(f99859,plain,(
% 47.47/6.33    r2_hidden(sK4(sK0,k1_xboole_0),k3_xboole_0(sK0,sK2)) | r1_tarski(sK0,k1_xboole_0) | ~spl8_40),
% 47.47/6.33    inference(superposition,[],[f84569,f9211])).
% 47.47/6.33  fof(f9211,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl8_40),
% 47.47/6.33    inference(avatar_component_clause,[],[f9209])).
% 47.47/6.33  fof(f159468,plain,(
% 47.47/6.33    ~spl8_105 | ~spl8_10 | ~spl8_104),
% 47.47/6.33    inference(avatar_split_clause,[],[f159461,f144046,f1451,f159465])).
% 47.47/6.33  fof(f159465,plain,(
% 47.47/6.33    spl8_105 <=> r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).
% 47.47/6.33  fof(f144046,plain,(
% 47.47/6.33    spl8_104 <=> r2_hidden(sK4(sK1,k1_xboole_0),sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).
% 47.47/6.33  fof(f159461,plain,(
% 47.47/6.33    ~r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0) | (~spl8_10 | ~spl8_104)),
% 47.47/6.33    inference(superposition,[],[f158668,f1453])).
% 47.47/6.33  fof(f158668,plain,(
% 47.47/6.33    ( ! [X2] : (~r2_hidden(sK4(sK1,k1_xboole_0),k4_xboole_0(X2,sK3))) ) | ~spl8_104),
% 47.47/6.33    inference(resolution,[],[f144048,f76])).
% 47.47/6.33  fof(f144048,plain,(
% 47.47/6.33    r2_hidden(sK4(sK1,k1_xboole_0),sK3) | ~spl8_104),
% 47.47/6.33    inference(avatar_component_clause,[],[f144046])).
% 47.47/6.33  fof(f158509,plain,(
% 47.47/6.33    spl8_2 | ~spl8_103),
% 47.47/6.33    inference(avatar_split_clause,[],[f144052,f144042,f87])).
% 47.47/6.33  fof(f87,plain,(
% 47.47/6.33    spl8_2 <=> k1_xboole_0 = sK1),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 47.47/6.33  fof(f144052,plain,(
% 47.47/6.33    k1_xboole_0 = sK1 | ~spl8_103),
% 47.47/6.33    inference(forward_demodulation,[],[f144051,f48])).
% 47.47/6.33  fof(f144051,plain,(
% 47.47/6.33    sK1 = k3_xboole_0(sK1,k1_xboole_0) | ~spl8_103),
% 47.47/6.33    inference(resolution,[],[f144044,f51])).
% 47.47/6.33  fof(f144044,plain,(
% 47.47/6.33    r1_tarski(sK1,k1_xboole_0) | ~spl8_103),
% 47.47/6.33    inference(avatar_component_clause,[],[f144042])).
% 47.47/6.33  fof(f144049,plain,(
% 47.47/6.33    spl8_103 | spl8_104 | ~spl8_10),
% 47.47/6.33    inference(avatar_split_clause,[],[f99867,f1451,f144046,f144042])).
% 47.47/6.33  fof(f99867,plain,(
% 47.47/6.33    r2_hidden(sK4(sK1,k1_xboole_0),sK3) | r1_tarski(sK1,k1_xboole_0) | ~spl8_10),
% 47.47/6.33    inference(superposition,[],[f84569,f1453])).
% 47.47/6.33  fof(f143766,plain,(
% 47.47/6.33    ~spl8_102 | ~spl8_16 | ~spl8_101),
% 47.47/6.33    inference(avatar_split_clause,[],[f143759,f128126,f3903,f143763])).
% 47.47/6.33  fof(f143763,plain,(
% 47.47/6.33    spl8_102 <=> r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).
% 47.47/6.33  fof(f128126,plain,(
% 47.47/6.33    spl8_101 <=> r2_hidden(sK4(sK0,k1_xboole_0),sK2)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).
% 47.47/6.33  fof(f143759,plain,(
% 47.47/6.33    ~r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0) | (~spl8_16 | ~spl8_101)),
% 47.47/6.33    inference(superposition,[],[f142966,f3905])).
% 47.47/6.33  fof(f142966,plain,(
% 47.47/6.33    ( ! [X2] : (~r2_hidden(sK4(sK0,k1_xboole_0),k4_xboole_0(X2,sK2))) ) | ~spl8_101),
% 47.47/6.33    inference(resolution,[],[f128128,f76])).
% 47.47/6.33  fof(f128128,plain,(
% 47.47/6.33    r2_hidden(sK4(sK0,k1_xboole_0),sK2) | ~spl8_101),
% 47.47/6.33    inference(avatar_component_clause,[],[f128126])).
% 47.47/6.33  fof(f142807,plain,(
% 47.47/6.33    spl8_1 | ~spl8_100),
% 47.47/6.33    inference(avatar_split_clause,[],[f128132,f128122,f82])).
% 47.47/6.33  fof(f82,plain,(
% 47.47/6.33    spl8_1 <=> k1_xboole_0 = sK0),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 47.47/6.33  fof(f128132,plain,(
% 47.47/6.33    k1_xboole_0 = sK0 | ~spl8_100),
% 47.47/6.33    inference(forward_demodulation,[],[f128131,f48])).
% 47.47/6.33  fof(f128131,plain,(
% 47.47/6.33    sK0 = k3_xboole_0(sK0,k1_xboole_0) | ~spl8_100),
% 47.47/6.33    inference(resolution,[],[f128124,f51])).
% 47.47/6.33  fof(f128124,plain,(
% 47.47/6.33    r1_tarski(sK0,k1_xboole_0) | ~spl8_100),
% 47.47/6.33    inference(avatar_component_clause,[],[f128122])).
% 47.47/6.33  fof(f128129,plain,(
% 47.47/6.33    spl8_100 | spl8_101 | ~spl8_16),
% 47.47/6.33    inference(avatar_split_clause,[],[f99866,f3903,f128126,f128122])).
% 47.47/6.33  fof(f99866,plain,(
% 47.47/6.33    r2_hidden(sK4(sK0,k1_xboole_0),sK2) | r1_tarski(sK0,k1_xboole_0) | ~spl8_16),
% 47.47/6.33    inference(superposition,[],[f84569,f3905])).
% 47.47/6.33  fof(f127665,plain,(
% 47.47/6.33    ~spl8_99 | ~spl8_13 | ~spl8_98),
% 47.47/6.33    inference(avatar_split_clause,[],[f127657,f114019,f1986,f127662])).
% 47.47/6.33  fof(f127662,plain,(
% 47.47/6.33    spl8_99 <=> r2_hidden(sK4(sK3,k1_xboole_0),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).
% 47.47/6.33  fof(f114019,plain,(
% 47.47/6.33    spl8_98 <=> r2_hidden(sK4(sK3,k1_xboole_0),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).
% 47.47/6.33  fof(f127657,plain,(
% 47.47/6.33    ~r2_hidden(sK4(sK3,k1_xboole_0),k1_xboole_0) | (~spl8_13 | ~spl8_98)),
% 47.47/6.33    inference(superposition,[],[f126869,f1988])).
% 47.47/6.33  fof(f126869,plain,(
% 47.47/6.33    ( ! [X2] : (~r2_hidden(sK4(sK3,k1_xboole_0),k4_xboole_0(X2,sK1))) ) | ~spl8_98),
% 47.47/6.33    inference(resolution,[],[f114021,f76])).
% 47.47/6.33  fof(f114021,plain,(
% 47.47/6.33    r2_hidden(sK4(sK3,k1_xboole_0),sK1) | ~spl8_98),
% 47.47/6.33    inference(avatar_component_clause,[],[f114019])).
% 47.47/6.33  fof(f126713,plain,(
% 47.47/6.33    spl8_6 | ~spl8_97),
% 47.47/6.33    inference(avatar_split_clause,[],[f114025,f114015,f163])).
% 47.47/6.33  fof(f114025,plain,(
% 47.47/6.33    k1_xboole_0 = sK3 | ~spl8_97),
% 47.47/6.33    inference(forward_demodulation,[],[f114024,f48])).
% 47.47/6.33  fof(f114024,plain,(
% 47.47/6.33    sK3 = k3_xboole_0(sK3,k1_xboole_0) | ~spl8_97),
% 47.47/6.33    inference(resolution,[],[f114017,f51])).
% 47.47/6.33  fof(f114017,plain,(
% 47.47/6.33    r1_tarski(sK3,k1_xboole_0) | ~spl8_97),
% 47.47/6.33    inference(avatar_component_clause,[],[f114015])).
% 47.47/6.33  fof(f114022,plain,(
% 47.47/6.33    spl8_97 | spl8_98 | ~spl8_13),
% 47.47/6.33    inference(avatar_split_clause,[],[f99864,f1986,f114019,f114015])).
% 47.47/6.33  fof(f99864,plain,(
% 47.47/6.33    r2_hidden(sK4(sK3,k1_xboole_0),sK1) | r1_tarski(sK3,k1_xboole_0) | ~spl8_13),
% 47.47/6.33    inference(superposition,[],[f84569,f1988])).
% 47.47/6.33  fof(f113740,plain,(
% 47.47/6.33    ~spl8_96 | ~spl8_21 | ~spl8_95),
% 47.47/6.33    inference(avatar_split_clause,[],[f113732,f100447,f4719,f113737])).
% 47.47/6.33  fof(f113737,plain,(
% 47.47/6.33    spl8_96 <=> r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).
% 47.47/6.33  fof(f100447,plain,(
% 47.47/6.33    spl8_95 <=> r2_hidden(sK4(sK2,k1_xboole_0),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).
% 47.47/6.33  fof(f113732,plain,(
% 47.47/6.33    ~r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) | (~spl8_21 | ~spl8_95)),
% 47.47/6.33    inference(superposition,[],[f112916,f4721])).
% 47.47/6.33  fof(f112916,plain,(
% 47.47/6.33    ( ! [X2] : (~r2_hidden(sK4(sK2,k1_xboole_0),k4_xboole_0(X2,sK0))) ) | ~spl8_95),
% 47.47/6.33    inference(resolution,[],[f100449,f76])).
% 47.47/6.33  fof(f100449,plain,(
% 47.47/6.33    r2_hidden(sK4(sK2,k1_xboole_0),sK0) | ~spl8_95),
% 47.47/6.33    inference(avatar_component_clause,[],[f100447])).
% 47.47/6.33  fof(f112761,plain,(
% 47.47/6.33    spl8_7 | ~spl8_94),
% 47.47/6.33    inference(avatar_split_clause,[],[f100453,f100443,f167])).
% 47.47/6.33  fof(f100453,plain,(
% 47.47/6.33    k1_xboole_0 = sK2 | ~spl8_94),
% 47.47/6.33    inference(forward_demodulation,[],[f100452,f48])).
% 47.47/6.33  fof(f100452,plain,(
% 47.47/6.33    sK2 = k3_xboole_0(sK2,k1_xboole_0) | ~spl8_94),
% 47.47/6.33    inference(resolution,[],[f100445,f51])).
% 47.47/6.33  fof(f100445,plain,(
% 47.47/6.33    r1_tarski(sK2,k1_xboole_0) | ~spl8_94),
% 47.47/6.33    inference(avatar_component_clause,[],[f100443])).
% 47.47/6.33  fof(f100450,plain,(
% 47.47/6.33    spl8_94 | spl8_95 | ~spl8_21),
% 47.47/6.33    inference(avatar_split_clause,[],[f99863,f4719,f100447,f100443])).
% 47.47/6.33  fof(f99863,plain,(
% 47.47/6.33    r2_hidden(sK4(sK2,k1_xboole_0),sK0) | r1_tarski(sK2,k1_xboole_0) | ~spl8_21),
% 47.47/6.33    inference(superposition,[],[f84569,f4721])).
% 47.47/6.33  fof(f100346,plain,(
% 47.47/6.33    spl8_93 | ~spl8_74),
% 47.47/6.33    inference(avatar_split_clause,[],[f100021,f46162,f100343])).
% 47.47/6.33  fof(f100343,plain,(
% 47.47/6.33    spl8_93 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK2)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).
% 47.47/6.33  fof(f46162,plain,(
% 47.47/6.33    spl8_74 <=> ! [X48] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X48)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).
% 47.47/6.33  fof(f100021,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK2) | ~spl8_74),
% 47.47/6.33    inference(forward_demodulation,[],[f99906,f48])).
% 47.47/6.33  fof(f99906,plain,(
% 47.47/6.33    k4_xboole_0(k3_xboole_0(sK0,sK2),sK2) = k3_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),k1_xboole_0) | ~spl8_74),
% 47.47/6.33    inference(superposition,[],[f99875,f46163])).
% 47.47/6.33  fof(f46163,plain,(
% 47.47/6.33    ( ! [X48] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X48)) ) | ~spl8_74),
% 47.47/6.33    inference(avatar_component_clause,[],[f46162])).
% 47.47/6.33  fof(f100245,plain,(
% 47.47/6.33    spl8_92 | ~spl8_72),
% 47.47/6.33    inference(avatar_split_clause,[],[f100016,f45354,f100242])).
% 47.47/6.33  fof(f100242,plain,(
% 47.47/6.33    spl8_92 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK0)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).
% 47.47/6.33  fof(f45354,plain,(
% 47.47/6.33    spl8_72 <=> ! [X48] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X48)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).
% 47.47/6.33  fof(f100016,plain,(
% 47.47/6.33    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK0) | ~spl8_72),
% 47.47/6.33    inference(forward_demodulation,[],[f99905,f48])).
% 47.47/6.33  fof(f99905,plain,(
% 47.47/6.33    k4_xboole_0(k3_xboole_0(sK0,sK2),sK0) = k3_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),k1_xboole_0) | ~spl8_72),
% 47.47/6.33    inference(superposition,[],[f99875,f45355])).
% 47.47/6.33  fof(f45355,plain,(
% 47.47/6.33    ( ! [X48] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X48)) ) | ~spl8_72),
% 47.47/6.33    inference(avatar_component_clause,[],[f45354])).
% 47.47/6.33  fof(f92907,plain,(
% 47.47/6.33    spl8_1 | ~spl8_17 | ~spl8_81),
% 47.47/6.33    inference(avatar_split_clause,[],[f92391,f51615,f3967,f82])).
% 47.47/6.33  fof(f3967,plain,(
% 47.47/6.33    spl8_17 <=> ! [X8] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 47.47/6.33  fof(f51615,plain,(
% 47.47/6.33    spl8_81 <=> ! [X43] : k1_xboole_0 = k4_xboole_0(sK0,X43)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).
% 47.47/6.33  fof(f92391,plain,(
% 47.47/6.33    k1_xboole_0 = sK0 | (~spl8_17 | ~spl8_81)),
% 47.47/6.33    inference(superposition,[],[f84584,f3968])).
% 47.47/6.33  fof(f3968,plain,(
% 47.47/6.33    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2))) ) | ~spl8_17),
% 47.47/6.33    inference(avatar_component_clause,[],[f3967])).
% 47.47/6.33  fof(f84584,plain,(
% 47.47/6.33    ( ! [X1] : (sK0 = k3_xboole_0(sK0,X1)) ) | ~spl8_81),
% 47.47/6.33    inference(resolution,[],[f84582,f51])).
% 47.47/6.33  fof(f84582,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl8_81),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f84575])).
% 47.47/6.33  fof(f84575,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(sK0,X0) | r1_tarski(sK0,X0)) ) | ~spl8_81),
% 47.47/6.33    inference(resolution,[],[f84565,f152])).
% 47.47/6.33  fof(f84565,plain,(
% 47.47/6.33    ( ! [X0] : (r2_hidden(sK4(sK0,X0),k1_xboole_0) | r1_tarski(sK0,X0)) ) | ~spl8_81),
% 47.47/6.33    inference(condensation,[],[f84550])).
% 47.47/6.33  fof(f84550,plain,(
% 47.47/6.33    ( ! [X8,X9] : (r2_hidden(sK4(sK0,X9),k1_xboole_0) | r2_hidden(sK4(sK0,X9),X8) | r1_tarski(sK0,X9)) ) | ~spl8_81),
% 47.47/6.33    inference(superposition,[],[f175,f51616])).
% 47.47/6.33  fof(f51616,plain,(
% 47.47/6.33    ( ! [X43] : (k1_xboole_0 = k4_xboole_0(sK0,X43)) ) | ~spl8_81),
% 47.47/6.33    inference(avatar_component_clause,[],[f51615])).
% 47.47/6.33  fof(f75024,plain,(
% 47.47/6.33    spl8_91 | spl8_1 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f74308,f5487,f82,f75022])).
% 47.47/6.33  fof(f75022,plain,(
% 47.47/6.33    spl8_91 <=> ! [X100,X99] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X99,sK1),k4_xboole_0(X100,k3_xboole_0(sK1,X99)))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).
% 47.47/6.33  fof(f5487,plain,(
% 47.47/6.33    spl8_27 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 47.47/6.33  fof(f74308,plain,(
% 47.47/6.33    ( ! [X99,X100] : (k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X99,sK1),k4_xboole_0(X100,k3_xboole_0(sK1,X99)))) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f74228])).
% 47.47/6.33  fof(f74228,plain,(
% 47.47/6.33    ( ! [X99,X100] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X99,sK1),k4_xboole_0(X100,k3_xboole_0(sK1,X99)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f74022])).
% 47.47/6.33  fof(f74022,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(X0,sK1),k4_xboole_0(X1,k3_xboole_0(sK1,X0))))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f73891,f50])).
% 47.47/6.33  fof(f73891,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X1,k3_xboole_0(sK1,X0)),k3_xboole_0(X0,sK1)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f8228,f1217])).
% 47.47/6.33  fof(f1217,plain,(
% 47.47/6.33    ( ! [X14,X15,X13] : (k3_xboole_0(k2_zfmisc_1(X13,X15),k2_zfmisc_1(X13,X14)) = k2_zfmisc_1(X13,k3_xboole_0(X14,X15))) )),
% 47.47/6.33    inference(superposition,[],[f837,f50])).
% 47.47/6.33  fof(f837,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 47.47/6.33    inference(superposition,[],[f72,f49])).
% 47.47/6.33  fof(f49,plain,(
% 47.47/6.33    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 47.47/6.33    inference(cnf_transformation,[],[f15])).
% 47.47/6.33  fof(f15,plain,(
% 47.47/6.33    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 47.47/6.33    inference(rectify,[],[f6])).
% 47.47/6.33  fof(f6,axiom,(
% 47.47/6.33    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 47.47/6.33  fof(f72,plain,(
% 47.47/6.33    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 47.47/6.33    inference(cnf_transformation,[],[f12])).
% 47.47/6.33  fof(f12,axiom,(
% 47.47/6.33    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 47.47/6.33  fof(f8228,plain,(
% 47.47/6.33    ( ! [X33,X31,X32] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(X31,sK1)),k2_zfmisc_1(X32,k4_xboole_0(X33,k3_xboole_0(sK1,X31))))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f876,f8106])).
% 47.47/6.33  fof(f8106,plain,(
% 47.47/6.33    ( ! [X1] : (k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X1))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f6633,f5513])).
% 47.47/6.33  fof(f5513,plain,(
% 47.47/6.33    ( ! [X7] : (k2_zfmisc_1(sK0,k3_xboole_0(X7,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(X7,k3_xboole_0(sK1,sK3)))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f5499,f837])).
% 47.47/6.33  fof(f5499,plain,(
% 47.47/6.33    ( ! [X7] : (k3_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(X7,k3_xboole_0(sK1,sK3)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f837,f5489])).
% 47.47/6.33  fof(f5489,plain,(
% 47.47/6.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | ~spl8_27),
% 47.47/6.33    inference(avatar_component_clause,[],[f5487])).
% 47.47/6.33  fof(f6633,plain,(
% 47.47/6.33    ( ! [X0] : (k2_zfmisc_1(sK0,k3_xboole_0(sK1,X0)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,k3_xboole_0(sK1,sK3)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f5512,f50])).
% 47.47/6.33  fof(f5512,plain,(
% 47.47/6.33    ( ! [X6] : (k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),X6)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X6))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f5498,f837])).
% 47.47/6.33  fof(f5498,plain,(
% 47.47/6.33    ( ! [X6] : (k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X6))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f837,f5489])).
% 47.47/6.33  fof(f876,plain,(
% 47.47/6.33    ( ! [X26,X24,X23,X25] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X26,k4_xboole_0(X24,X23)))) )),
% 47.47/6.33    inference(forward_demodulation,[],[f856,f73])).
% 47.47/6.33  fof(f73,plain,(
% 47.47/6.33    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 47.47/6.33    inference(equality_resolution,[],[f57])).
% 47.47/6.33  fof(f57,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 47.47/6.33    inference(cnf_transformation,[],[f30])).
% 47.47/6.33  fof(f30,plain,(
% 47.47/6.33    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 47.47/6.33    inference(flattening,[],[f29])).
% 47.47/6.33  fof(f29,plain,(
% 47.47/6.33    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 47.47/6.33    inference(nnf_transformation,[],[f11])).
% 47.47/6.33  fof(f11,axiom,(
% 47.47/6.33    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 47.47/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 47.47/6.33  fof(f856,plain,(
% 47.47/6.33    ( ! [X26,X24,X23,X25] : (k3_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X26,k4_xboole_0(X24,X23))) = k2_zfmisc_1(k3_xboole_0(X25,X26),k1_xboole_0)) )),
% 47.47/6.33    inference(superposition,[],[f72,f581])).
% 47.47/6.33  fof(f581,plain,(
% 47.47/6.33    ( ! [X24,X25] : (k1_xboole_0 = k3_xboole_0(X24,k4_xboole_0(X25,X24))) )),
% 47.47/6.33    inference(superposition,[],[f563,f48])).
% 47.47/6.33  fof(f563,plain,(
% 47.47/6.33    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X3)) = k3_xboole_0(k3_xboole_0(X3,k4_xboole_0(X4,X3)),X5)) )),
% 47.47/6.33    inference(resolution,[],[f561,f51])).
% 47.47/6.33  fof(f561,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) )),
% 47.47/6.33    inference(forward_demodulation,[],[f560,f50])).
% 47.47/6.33  fof(f560,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2)) )),
% 47.47/6.33    inference(duplicate_literal_removal,[],[f546])).
% 47.47/6.33  fof(f546,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2) | r1_tarski(k3_xboole_0(k4_xboole_0(X0,X1),X1),X2)) )),
% 47.47/6.33    inference(resolution,[],[f218,f126])).
% 47.47/6.33  fof(f126,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 47.47/6.33    inference(resolution,[],[f80,f53])).
% 47.47/6.33  fof(f218,plain,(
% 47.47/6.33    ( ! [X12,X10,X13,X11] : (~r2_hidden(sK4(k3_xboole_0(X10,X11),X12),k4_xboole_0(X13,X11)) | r1_tarski(k3_xboole_0(X10,X11),X12)) )),
% 47.47/6.33    inference(resolution,[],[f119,f76])).
% 47.47/6.33  fof(f55,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 47.47/6.33    inference(cnf_transformation,[],[f30])).
% 47.47/6.33  fof(f74818,plain,(
% 47.47/6.33    spl8_90 | spl8_1 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f74651,f5487,f82,f74816])).
% 47.47/6.33  fof(f74816,plain,(
% 47.47/6.33    spl8_90 <=> ! [X46] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X46,sK1),k3_xboole_0(sK1,X46))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).
% 47.47/6.33  fof(f74651,plain,(
% 47.47/6.33    ( ! [X46] : (k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(X46,sK1),k3_xboole_0(sK1,X46))) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f74571])).
% 47.47/6.33  fof(f74571,plain,(
% 47.47/6.33    ( ! [X46] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(X46,sK1),k3_xboole_0(sK1,X46))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f74193])).
% 47.47/6.33  fof(f74193,plain,(
% 47.47/6.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(X1,sK1),k3_xboole_0(sK1,X1)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f74022,f200])).
% 47.47/6.33  fof(f73851,plain,(
% 47.47/6.33    spl8_1 | spl8_89 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f8221,f5487,f73849,f82])).
% 47.47/6.33  fof(f73849,plain,(
% 47.47/6.33    spl8_89 <=> ! [X16] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(X16,sK1)) | k1_xboole_0 = k3_xboole_0(sK1,X16))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).
% 47.47/6.33  fof(f8221,plain,(
% 47.47/6.33    ( ! [X16] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(X16,sK1)) | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,X16)) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f8106])).
% 47.47/6.33  fof(f73505,plain,(
% 47.47/6.33    spl8_88 | spl8_1 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f72797,f5487,f82,f73503])).
% 47.47/6.33  fof(f73503,plain,(
% 47.47/6.33    spl8_88 <=> ! [X104,X103] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X103),k4_xboole_0(X104,k3_xboole_0(X103,sK1)))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).
% 47.47/6.33  fof(f72797,plain,(
% 47.47/6.33    ( ! [X103,X104] : (k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X103),k4_xboole_0(X104,k3_xboole_0(X103,sK1)))) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f72717])).
% 47.47/6.33  fof(f72717,plain,(
% 47.47/6.33    ( ! [X103,X104] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X103),k4_xboole_0(X104,k3_xboole_0(X103,sK1)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f72509])).
% 47.47/6.33  fof(f72509,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(X1,k3_xboole_0(X0,sK1))))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f72370,f50])).
% 47.47/6.33  fof(f72370,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X1,k3_xboole_0(X0,sK1)),k3_xboole_0(sK1,X0)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f8197,f1217])).
% 47.47/6.33  fof(f8197,plain,(
% 47.47/6.33    ( ! [X33,X31,X32] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,X31)),k2_zfmisc_1(X32,k4_xboole_0(X33,k3_xboole_0(X31,sK1))))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f876,f8106])).
% 47.47/6.33  fof(f73319,plain,(
% 47.47/6.33    spl8_87 | spl8_1 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f73153,f5487,f82,f73317])).
% 47.47/6.33  fof(f73317,plain,(
% 47.47/6.33    spl8_87 <=> ! [X44] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X44),k3_xboole_0(X44,sK1))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).
% 47.47/6.33  fof(f73153,plain,(
% 47.47/6.33    ( ! [X44] : (k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X44),k3_xboole_0(X44,sK1))) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f73073])).
% 47.47/6.33  fof(f73073,plain,(
% 47.47/6.33    ( ! [X44] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X44),k3_xboole_0(X44,sK1))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f72676])).
% 47.47/6.33  fof(f72676,plain,(
% 47.47/6.33    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X0,sK1)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f72509,f200])).
% 47.47/6.33  fof(f71580,plain,(
% 47.47/6.33    spl8_1 | spl8_86 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f8190,f5487,f71578,f82])).
% 47.47/6.33  fof(f71578,plain,(
% 47.47/6.33    spl8_86 <=> ! [X16] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X16)) | k1_xboole_0 = k3_xboole_0(X16,sK1))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).
% 47.47/6.33  fof(f8190,plain,(
% 47.47/6.33    ( ! [X16] : (k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,X16)) | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(X16,sK1)) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f8106])).
% 47.47/6.33  fof(f56282,plain,(
% 47.47/6.33    spl8_85 | spl8_1 | ~spl8_11 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f55723,f5487,f1506,f82,f56280])).
% 47.47/6.33  fof(f56280,plain,(
% 47.47/6.33    spl8_85 <=> ! [X57] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).
% 47.47/6.33  fof(f1506,plain,(
% 47.47/6.33    spl8_11 <=> ! [X2] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 47.47/6.33  fof(f55723,plain,(
% 47.47/6.33    ( ! [X57] : (k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK3))) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f55661])).
% 47.47/6.33  fof(f55661,plain,(
% 47.47/6.33    ( ! [X57] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK3))) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(superposition,[],[f55,f55528])).
% 47.47/6.33  fof(f55528,plain,(
% 47.47/6.33    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X6,sK3)))) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(forward_demodulation,[],[f55412,f50])).
% 47.47/6.33  fof(f55412,plain,(
% 47.47/6.33    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X6,sK3),k3_xboole_0(sK1,sK3)))) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(superposition,[],[f55232,f1217])).
% 47.47/6.33  fof(f55232,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK3)))) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(forward_demodulation,[],[f55204,f48])).
% 47.47/6.33  fof(f55204,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK3))) = k3_xboole_0(k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK3))),k1_xboole_0)) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(resolution,[],[f53005,f51])).
% 47.47/6.33  fof(f53005,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X0,sK3))),k1_xboole_0)) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(forward_demodulation,[],[f52945,f73])).
% 47.47/6.33  fof(f52945,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X0,sK3))),k2_zfmisc_1(sK0,k1_xboole_0))) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(superposition,[],[f6686,f1507])).
% 47.47/6.33  fof(f1507,plain,(
% 47.47/6.33    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))) ) | ~spl8_11),
% 47.47/6.33    inference(avatar_component_clause,[],[f1506])).
% 47.47/6.33  fof(f6686,plain,(
% 47.47/6.33    ( ! [X41,X40] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X41,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,X40)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X40)))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f6661,f72])).
% 47.47/6.33  fof(f6661,plain,(
% 47.47/6.33    ( ! [X41,X40] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X41,sK0),k3_xboole_0(k3_xboole_0(sK1,sK3),X40)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X40)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f3580,f5512])).
% 47.47/6.33  fof(f3580,plain,(
% 47.47/6.33    ( ! [X64,X65,X63] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X63,X65),X64),k2_zfmisc_1(X65,X64))) )),
% 47.47/6.33    inference(superposition,[],[f232,f850])).
% 47.47/6.33  fof(f850,plain,(
% 47.47/6.33    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 47.47/6.33    inference(superposition,[],[f72,f49])).
% 47.47/6.33  fof(f56163,plain,(
% 47.47/6.33    spl8_84 | spl8_1 | ~spl8_83),
% 47.47/6.33    inference(avatar_split_clause,[],[f56049,f55964,f82,f56160])).
% 47.47/6.33  fof(f56160,plain,(
% 47.47/6.33    spl8_84 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).
% 47.47/6.33  fof(f55964,plain,(
% 47.47/6.33    spl8_83 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).
% 47.47/6.33  fof(f56049,plain,(
% 47.47/6.33    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3) | ~spl8_83),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f55987])).
% 47.47/6.33  fof(f55987,plain,(
% 47.47/6.33    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK3) | ~spl8_83),
% 47.47/6.33    inference(superposition,[],[f55,f55966])).
% 47.47/6.33  fof(f55966,plain,(
% 47.47/6.33    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)) | ~spl8_83),
% 47.47/6.33    inference(avatar_component_clause,[],[f55964])).
% 47.47/6.33  fof(f55967,plain,(
% 47.47/6.33    spl8_83 | ~spl8_11 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f55628,f5487,f1506,f55964])).
% 47.47/6.33  fof(f55628,plain,(
% 47.47/6.33    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK3)) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(superposition,[],[f55528,f200])).
% 47.47/6.33  fof(f53775,plain,(
% 47.47/6.33    spl8_82 | spl8_1 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f53528,f5487,f82,f51997])).
% 47.47/6.33  fof(f51997,plain,(
% 47.47/6.33    spl8_82 <=> ! [X116] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X116,sK1))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).
% 47.47/6.33  fof(f53528,plain,(
% 47.47/6.33    ( ! [X57] : (k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK1))) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f53466])).
% 47.47/6.33  fof(f53466,plain,(
% 47.47/6.33    ( ! [X57] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X57,sK1))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f53329])).
% 47.47/6.33  fof(f53329,plain,(
% 47.47/6.33    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X6,sK1)))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f53211,f50])).
% 47.47/6.33  fof(f53211,plain,(
% 47.47/6.33    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(k4_xboole_0(X6,sK1),k3_xboole_0(sK1,sK3)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f53045,f1217])).
% 47.47/6.33  fof(f53045,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK1)))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f53015,f48])).
% 47.47/6.33  fof(f53015,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK1))) = k3_xboole_0(k3_xboole_0(k2_zfmisc_1(X2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X3,sK1))),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(resolution,[],[f53008,f51])).
% 47.47/6.33  fof(f53008,plain,(
% 47.47/6.33    ( ! [X15,X16] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X16,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X15,sK1))),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f52953,f73])).
% 47.47/6.33  fof(f52953,plain,(
% 47.47/6.33    ( ! [X15,X16] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X16,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k4_xboole_0(X15,sK1))),k2_zfmisc_1(sK0,k1_xboole_0))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f6686,f581])).
% 47.47/6.33  fof(f51999,plain,(
% 47.47/6.33    spl8_82 | spl8_81 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f51860,f5487,f51615,f51997])).
% 47.47/6.33  fof(f51860,plain,(
% 47.47/6.33    ( ! [X116,X115] : (k1_xboole_0 = k4_xboole_0(sK0,X115) | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X116,sK1))) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f51798])).
% 47.47/6.33  fof(f51798,plain,(
% 47.47/6.33    ( ! [X116,X115] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,X115) | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X116,sK1))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f51375])).
% 47.47/6.33  fof(f51375,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,X2),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X3,sK1)))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f51361,f48])).
% 47.47/6.33  fof(f51361,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k2_zfmisc_1(k4_xboole_0(sK0,X2),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X3,sK1))) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,X2),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X3,sK1))),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(resolution,[],[f51353,f51])).
% 47.47/6.33  fof(f51353,plain,(
% 47.47/6.33    ( ! [X15,X16] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,X16),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X15,sK1))),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f51324,f73])).
% 47.47/6.33  fof(f51324,plain,(
% 47.47/6.33    ( ! [X15,X16] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,X16),k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X15,sK1))),k2_zfmisc_1(sK0,k1_xboole_0))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f6663,f581])).
% 47.47/6.33  fof(f6663,plain,(
% 47.47/6.33    ( ! [X45,X44] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,X45),k3_xboole_0(k3_xboole_0(sK1,sK3),X44)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X44)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f3655,f5512])).
% 47.47/6.33  fof(f3655,plain,(
% 47.47/6.33    ( ! [X30,X28,X29] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(X28,X29),X30),k2_zfmisc_1(X28,X30))) )),
% 47.47/6.33    inference(superposition,[],[f3580,f196])).
% 47.47/6.33  fof(f51617,plain,(
% 47.47/6.33    spl8_80 | spl8_81 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f51519,f5487,f51615,f51611])).
% 47.47/6.33  fof(f51611,plain,(
% 47.47/6.33    spl8_80 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).
% 47.47/6.33  fof(f51519,plain,(
% 47.47/6.33    ( ! [X43] : (k1_xboole_0 = k4_xboole_0(sK0,X43) | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f51457])).
% 47.47/6.33  fof(f51457,plain,(
% 47.47/6.33    ( ! [X43] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,X43) | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f51413])).
% 47.47/6.33  fof(f51413,plain,(
% 47.47/6.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,X1),k4_xboole_0(k3_xboole_0(sK1,sK3),sK1))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f51409,f48])).
% 47.47/6.33  fof(f51409,plain,(
% 47.47/6.33    ( ! [X1] : (k2_zfmisc_1(k4_xboole_0(sK0,X1),k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,X1),k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(resolution,[],[f51374,f51])).
% 47.47/6.33  fof(f51374,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,X0),k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f51353,f200])).
% 47.47/6.33  fof(f50887,plain,(
% 47.47/6.33    spl8_79 | spl8_1 | ~spl8_11 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f50800,f5487,f1506,f82,f50885])).
% 47.47/6.33  fof(f50885,plain,(
% 47.47/6.33    spl8_79 <=> ! [X43] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X43)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).
% 47.47/6.33  fof(f50800,plain,(
% 47.47/6.33    ( ! [X43] : (k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X43)) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f50738])).
% 47.47/6.33  fof(f50738,plain,(
% 47.47/6.33    ( ! [X43] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X43)) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(superposition,[],[f55,f50703])).
% 47.47/6.33  fof(f50703,plain,(
% 47.47/6.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X1))) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(forward_demodulation,[],[f50701,f48])).
% 47.47/6.33  fof(f50701,plain,(
% 47.47/6.33    ( ! [X1] : (k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X1)) = k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X1)),k1_xboole_0)) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(resolution,[],[f50670,f51])).
% 47.47/6.33  fof(f50670,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK3),X0)),k1_xboole_0)) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(superposition,[],[f49795,f200])).
% 47.47/6.33  fof(f49795,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X0,sK3)),X1)),k1_xboole_0)) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(forward_demodulation,[],[f49766,f73])).
% 47.47/6.33  fof(f49766,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X0,sK3)),X1)),k2_zfmisc_1(sK0,k1_xboole_0))) ) | (~spl8_11 | ~spl8_27)),
% 47.47/6.33    inference(superposition,[],[f6660,f1507])).
% 47.47/6.33  fof(f6660,plain,(
% 47.47/6.33    ( ! [X39,X38] : (r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),X38),X39)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X38)))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f1282,f5512])).
% 47.47/6.33  fof(f1282,plain,(
% 47.47/6.33    ( ! [X30,X28,X29] : (r1_tarski(k2_zfmisc_1(X30,k4_xboole_0(X28,X29)),k2_zfmisc_1(X30,X28))) )),
% 47.47/6.33    inference(superposition,[],[f1235,f196])).
% 47.47/6.33  fof(f1235,plain,(
% 47.47/6.33    ( ! [X54,X55,X53] : (r1_tarski(k2_zfmisc_1(X53,k3_xboole_0(X54,X55)),k2_zfmisc_1(X53,X55))) )),
% 47.47/6.33    inference(superposition,[],[f232,f837])).
% 47.47/6.33  fof(f50435,plain,(
% 47.47/6.33    spl8_78 | spl8_1 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f50329,f5487,f82,f50433])).
% 47.47/6.33  fof(f50433,plain,(
% 47.47/6.33    spl8_78 <=> ! [X77,X78] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X77,sK1)),X78)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).
% 47.47/6.33  fof(f50329,plain,(
% 47.47/6.33    ( ! [X78,X77] : (k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X77,sK1)),X78)) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f50267])).
% 47.47/6.33  fof(f50267,plain,(
% 47.47/6.33    ( ! [X78,X77] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X77,sK1)),X78)) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f49819])).
% 47.47/6.33  fof(f49819,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X2,sK1)),X3))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f49810,f48])).
% 47.47/6.33  fof(f49810,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X2,sK1)),X3)) = k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X2,sK1)),X3)),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(resolution,[],[f49802,f51])).
% 47.47/6.33  fof(f49802,plain,(
% 47.47/6.33    ( ! [X15,X16] : (r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X15,sK1)),X16)),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f49774,f73])).
% 47.47/6.33  fof(f49774,plain,(
% 47.47/6.33    ( ! [X15,X16] : (r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK3),k4_xboole_0(X15,sK1)),X16)),k2_zfmisc_1(sK0,k1_xboole_0))) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f6660,f581])).
% 47.47/6.33  fof(f50028,plain,(
% 47.47/6.33    spl8_77 | spl8_1 | ~spl8_27),
% 47.47/6.33    inference(avatar_split_clause,[],[f49941,f5487,f82,f50026])).
% 47.47/6.33  fof(f50026,plain,(
% 47.47/6.33    spl8_77 <=> ! [X43] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X43)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).
% 47.47/6.33  fof(f49941,plain,(
% 47.47/6.33    ( ! [X43] : (k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X43)) ) | ~spl8_27),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f49879])).
% 47.47/6.33  fof(f49879,plain,(
% 47.47/6.33    ( ! [X43] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X43)) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f55,f49844])).
% 47.47/6.33  fof(f49844,plain,(
% 47.47/6.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X1))) ) | ~spl8_27),
% 47.47/6.33    inference(forward_demodulation,[],[f49842,f48])).
% 47.47/6.33  fof(f49842,plain,(
% 47.47/6.33    ( ! [X1] : (k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X1)) = k3_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X1)),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(resolution,[],[f49817,f51])).
% 47.47/6.33  fof(f49817,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK3),sK1),X0)),k1_xboole_0)) ) | ~spl8_27),
% 47.47/6.33    inference(superposition,[],[f49802,f200])).
% 47.47/6.33  fof(f48686,plain,(
% 47.47/6.33    spl8_76 | spl8_8 | ~spl8_25),
% 47.47/6.33    inference(avatar_split_clause,[],[f29262,f5431,f171,f48684])).
% 47.47/6.33  fof(f48684,plain,(
% 47.47/6.33    spl8_76 <=> ! [X52] : r2_hidden(sK7(X52,k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).
% 47.47/6.33  fof(f171,plain,(
% 47.47/6.33    spl8_8 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 47.47/6.33  fof(f5431,plain,(
% 47.47/6.33    spl8_25 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 47.47/6.33  fof(f29262,plain,(
% 47.47/6.33    ( ! [X52] : (k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r2_hidden(sK7(X52,k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))) ) | ~spl8_25),
% 47.47/6.33    inference(resolution,[],[f29241,f5437])).
% 47.47/6.33  fof(f5437,plain,(
% 47.47/6.33    ( ! [X1] : (~r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,k2_zfmisc_1(sK0,sK3))) ) | ~spl8_25),
% 47.47/6.33    inference(superposition,[],[f3574,f5433])).
% 47.47/6.33  fof(f5433,plain,(
% 47.47/6.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | ~spl8_25),
% 47.47/6.33    inference(avatar_component_clause,[],[f5431])).
% 47.47/6.33  fof(f3574,plain,(
% 47.47/6.33    ( ! [X43,X41,X42,X40] : (~r2_hidden(X43,k2_zfmisc_1(k3_xboole_0(X40,X42),X41)) | r2_hidden(X43,k2_zfmisc_1(X40,X41))) )),
% 47.47/6.33    inference(superposition,[],[f80,f850])).
% 47.47/6.33  fof(f46558,plain,(
% 47.47/6.33    spl8_75 | spl8_8 | ~spl8_25),
% 47.47/6.33    inference(avatar_split_clause,[],[f12074,f5431,f171,f46556])).
% 47.47/6.33  fof(f46556,plain,(
% 47.47/6.33    spl8_75 <=> ! [X51] : r2_hidden(sK7(k1_xboole_0,X51,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).
% 47.47/6.33  fof(f12074,plain,(
% 47.47/6.33    ( ! [X51] : (k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r2_hidden(sK7(k1_xboole_0,X51,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))) ) | ~spl8_25),
% 47.47/6.33    inference(resolution,[],[f12056,f5437])).
% 47.47/6.33  fof(f46164,plain,(
% 47.47/6.33    spl8_2 | spl8_74 | ~spl8_17 | ~spl8_36),
% 47.47/6.33    inference(avatar_split_clause,[],[f46083,f8778,f3967,f46162,f87])).
% 47.47/6.33  fof(f8778,plain,(
% 47.47/6.33    spl8_36 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 47.47/6.33  fof(f46083,plain,(
% 47.47/6.33    ( ! [X48] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X48) | k1_xboole_0 = sK1) ) | (~spl8_17 | ~spl8_36)),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f46025])).
% 47.47/6.33  fof(f46025,plain,(
% 47.47/6.33    ( ! [X48] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X48) | k1_xboole_0 = sK1) ) | (~spl8_17 | ~spl8_36)),
% 47.47/6.33    inference(superposition,[],[f55,f45985])).
% 47.47/6.33  fof(f45985,plain,(
% 47.47/6.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X1),sK1)) ) | (~spl8_17 | ~spl8_36)),
% 47.47/6.33    inference(forward_demodulation,[],[f45983,f48])).
% 47.47/6.33  fof(f45983,plain,(
% 47.47/6.33    ( ! [X1] : (k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X1),sK1) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X1),sK1),k1_xboole_0)) ) | (~spl8_17 | ~spl8_36)),
% 47.47/6.33    inference(resolution,[],[f45961,f51])).
% 47.47/6.33  fof(f45961,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),X0),sK1),k1_xboole_0)) ) | (~spl8_17 | ~spl8_36)),
% 47.47/6.33    inference(superposition,[],[f45132,f200])).
% 47.47/6.33  fof(f45132,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X0,sK2)),X1),sK1),k1_xboole_0)) ) | (~spl8_17 | ~spl8_36)),
% 47.47/6.33    inference(forward_demodulation,[],[f45100,f74])).
% 47.47/6.33  fof(f74,plain,(
% 47.47/6.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 47.47/6.33    inference(equality_resolution,[],[f56])).
% 47.47/6.33  fof(f56,plain,(
% 47.47/6.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 47.47/6.33    inference(cnf_transformation,[],[f30])).
% 47.47/6.33  fof(f45100,plain,(
% 47.47/6.33    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X0,sK2)),X1),sK1),k2_zfmisc_1(k1_xboole_0,sK1))) ) | (~spl8_17 | ~spl8_36)),
% 47.47/6.33    inference(superposition,[],[f9049,f3968])).
% 47.47/6.33  fof(f9049,plain,(
% 47.47/6.33    ( ! [X43,X44] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),X43),X44),sK1),k2_zfmisc_1(k3_xboole_0(sK0,X43),sK1))) ) | ~spl8_36),
% 47.47/6.33    inference(superposition,[],[f3655,f8819])).
% 47.47/6.33  fof(f8819,plain,(
% 47.47/6.33    ( ! [X8] : (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,X8),sK1)) ) | ~spl8_36),
% 47.47/6.33    inference(forward_demodulation,[],[f8793,f850])).
% 47.47/6.33  fof(f8793,plain,(
% 47.47/6.33    ( ! [X8] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,sK1)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK1)) ) | ~spl8_36),
% 47.47/6.33    inference(superposition,[],[f850,f8780])).
% 47.47/6.33  fof(f8780,plain,(
% 47.47/6.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl8_36),
% 47.47/6.33    inference(avatar_component_clause,[],[f8778])).
% 47.47/6.33  fof(f45742,plain,(
% 47.47/6.33    spl8_2 | spl8_73 | ~spl8_36),
% 47.47/6.33    inference(avatar_split_clause,[],[f45648,f8778,f45740,f87])).
% 47.47/6.33  fof(f45740,plain,(
% 47.47/6.33    spl8_73 <=> ! [X87,X88] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X87,sK0)),X88)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).
% 47.47/6.33  fof(f45648,plain,(
% 47.47/6.33    ( ! [X88,X87] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X87,sK0)),X88) | k1_xboole_0 = sK1) ) | ~spl8_36),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f45590])).
% 47.47/6.33  fof(f45590,plain,(
% 47.47/6.33    ( ! [X88,X87] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X87,sK0)),X88) | k1_xboole_0 = sK1) ) | ~spl8_36),
% 47.47/6.33    inference(superposition,[],[f55,f45161])).
% 47.47/6.33  fof(f45161,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X2,sK0)),X3),sK1)) ) | ~spl8_36),
% 47.47/6.33    inference(forward_demodulation,[],[f45155,f48])).
% 47.47/6.33  fof(f45155,plain,(
% 47.47/6.33    ( ! [X2,X3] : (k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X2,sK0)),X3),sK1) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X2,sK0)),X3),sK1),k1_xboole_0)) ) | ~spl8_36),
% 47.47/6.33    inference(resolution,[],[f45139,f51])).
% 47.47/6.33  fof(f45139,plain,(
% 47.47/6.33    ( ! [X15,X16] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X15,sK0)),X16),sK1),k1_xboole_0)) ) | ~spl8_36),
% 47.47/6.33    inference(forward_demodulation,[],[f45108,f74])).
% 47.47/6.33  fof(f45108,plain,(
% 47.47/6.33    ( ! [X15,X16] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(X15,sK0)),X16),sK1),k2_zfmisc_1(k1_xboole_0,sK1))) ) | ~spl8_36),
% 47.47/6.33    inference(superposition,[],[f9049,f581])).
% 47.47/6.33  fof(f45356,plain,(
% 47.47/6.33    spl8_2 | spl8_72 | ~spl8_36),
% 47.47/6.33    inference(avatar_split_clause,[],[f45275,f8778,f45354,f87])).
% 47.47/6.33  fof(f45275,plain,(
% 47.47/6.33    ( ! [X48] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X48) | k1_xboole_0 = sK1) ) | ~spl8_36),
% 47.47/6.33    inference(trivial_inequality_removal,[],[f45217])).
% 47.47/6.33  fof(f45217,plain,(
% 47.47/6.33    ( ! [X48] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X48) | k1_xboole_0 = sK1) ) | ~spl8_36),
% 47.47/6.33    inference(superposition,[],[f55,f45177])).
% 47.47/6.33  fof(f45177,plain,(
% 47.47/6.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X1),sK1)) ) | ~spl8_36),
% 47.47/6.33    inference(forward_demodulation,[],[f45175,f48])).
% 47.47/6.33  fof(f45175,plain,(
% 47.47/6.33    ( ! [X1] : (k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X1),sK1) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X1),sK1),k1_xboole_0)) ) | ~spl8_36),
% 47.47/6.33    inference(resolution,[],[f45159,f51])).
% 47.47/6.33  fof(f45159,plain,(
% 47.47/6.33    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK0),X0),sK1),k1_xboole_0)) ) | ~spl8_36),
% 47.47/6.33    inference(superposition,[],[f45139,f200])).
% 47.47/6.33  fof(f44943,plain,(
% 47.47/6.33    spl8_71 | spl8_8 | ~spl8_25),
% 47.47/6.33    inference(avatar_split_clause,[],[f6336,f5431,f171,f44941])).
% 47.47/6.33  fof(f44941,plain,(
% 47.47/6.33    spl8_71 <=> ! [X51] : r2_hidden(sK6(X51,X51,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).
% 47.47/6.33  fof(f6336,plain,(
% 47.47/6.33    ( ! [X51] : (k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r2_hidden(sK6(X51,X51,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))) ) | ~spl8_25),
% 47.47/6.33    inference(resolution,[],[f6317,f5437])).
% 47.47/6.33  fof(f44939,plain,(
% 47.47/6.33    spl8_6 | spl8_70 | ~spl8_5),
% 47.47/6.33    inference(avatar_split_clause,[],[f5793,f101,f44937,f163])).
% 47.47/6.33  fof(f44937,plain,(
% 47.47/6.33    spl8_70 <=> ! [X19] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(X19,sK2),sK3) | k1_xboole_0 = k3_xboole_0(sK2,X19))),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).
% 47.47/6.33  fof(f101,plain,(
% 47.47/6.33    spl8_5 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 47.47/6.33    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 47.47/6.33  fof(f5793,plain,(
% 47.47/6.33    ( ! [X19] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(X19,sK2),sK3) | k1_xboole_0 = k3_xboole_0(sK2,X19) | k1_xboole_0 = sK3) ) | ~spl8_5),
% 47.47/6.33    inference(superposition,[],[f55,f5674])).
% 47.47/6.33  fof(f5674,plain,(
% 47.47/6.33    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3)) ) | ~spl8_5),
% 47.47/6.33    inference(superposition,[],[f4579,f3538])).
% 47.47/6.33  fof(f3538,plain,(
% 47.47/6.33    ( ! [X9] : (k2_zfmisc_1(k3_xboole_0(X9,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(sK0,sK1))) ) | ~spl8_5),
% 47.47/6.33    inference(superposition,[],[f850,f103])).
% 47.47/6.33  fof(f103,plain,(
% 47.47/6.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | ~spl8_5),
% 47.47/6.33    inference(avatar_component_clause,[],[f101])).
% 47.47/6.34  fof(f4579,plain,(
% 47.47/6.34    ( ! [X4] : (k3_xboole_0(k2_zfmisc_1(X4,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK2,X4),sK3)) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f3532,f50])).
% 47.47/6.34  fof(f3532,plain,(
% 47.47/6.34    ( ! [X9] : (k2_zfmisc_1(k3_xboole_0(sK2,X9),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK3))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f850,f103])).
% 47.47/6.34  fof(f44930,plain,(
% 47.47/6.34    ~spl8_69 | spl8_7 | ~spl8_5 | ~spl8_18 | ~spl8_34 | ~spl8_36 | ~spl8_68),
% 47.47/6.34    inference(avatar_split_clause,[],[f44430,f44400,f8778,f8638,f4031,f101,f167,f44927])).
% 47.47/6.34  fof(f4031,plain,(
% 47.47/6.34    spl8_18 <=> k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 47.47/6.34  fof(f8638,plain,(
% 47.47/6.34    spl8_34 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 47.47/6.34  fof(f44400,plain,(
% 47.47/6.34    spl8_68 <=> ! [X19] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK2,X19),sK3) | k1_xboole_0 = k3_xboole_0(X19,sK2))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 47.47/6.34  fof(f44430,plain,(
% 47.47/6.34    k1_xboole_0 = sK2 | k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | (~spl8_5 | ~spl8_18 | ~spl8_34 | ~spl8_36 | ~spl8_68)),
% 47.47/6.34    inference(forward_demodulation,[],[f44413,f49])).
% 47.47/6.34  fof(f44413,plain,(
% 47.47/6.34    k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | k1_xboole_0 = k3_xboole_0(sK2,sK2) | (~spl8_5 | ~spl8_18 | ~spl8_34 | ~spl8_36 | ~spl8_68)),
% 47.47/6.34    inference(superposition,[],[f44401,f40263])).
% 47.47/6.34  fof(f40263,plain,(
% 47.47/6.34    ( ! [X2] : (k2_zfmisc_1(k3_xboole_0(X2,sK2),sK3) = k2_zfmisc_1(k3_xboole_0(sK0,X2),sK1)) ) | (~spl8_5 | ~spl8_18 | ~spl8_34 | ~spl8_36)),
% 47.47/6.34    inference(superposition,[],[f34284,f50])).
% 47.47/6.34  fof(f34284,plain,(
% 47.47/6.34    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k2_zfmisc_1(k3_xboole_0(sK0,X1),sK1)) ) | (~spl8_5 | ~spl8_18 | ~spl8_34 | ~spl8_36)),
% 47.47/6.34    inference(forward_demodulation,[],[f34156,f8820])).
% 47.47/6.34  fof(f8820,plain,(
% 47.47/6.34    ( ! [X6] : (k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(X6,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,X6),sK1)) ) | (~spl8_18 | ~spl8_36)),
% 47.47/6.34    inference(backward_demodulation,[],[f4057,f8819])).
% 47.47/6.34  fof(f4057,plain,(
% 47.47/6.34    ( ! [X6] : (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X6),sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(X6,sK3))) ) | ~spl8_18),
% 47.47/6.34    inference(forward_demodulation,[],[f4042,f880])).
% 47.47/6.34  fof(f880,plain,(
% 47.47/6.34    ( ! [X37,X35,X36,X34] : (k3_xboole_0(k2_zfmisc_1(X36,k3_xboole_0(X34,X35)),k2_zfmisc_1(X37,X34)) = k3_xboole_0(k2_zfmisc_1(X36,X34),k2_zfmisc_1(X37,X35))) )),
% 47.47/6.34    inference(forward_demodulation,[],[f859,f72])).
% 47.47/6.34  fof(f859,plain,(
% 47.47/6.34    ( ! [X37,X35,X36,X34] : (k3_xboole_0(k2_zfmisc_1(X36,k3_xboole_0(X34,X35)),k2_zfmisc_1(X37,X34)) = k2_zfmisc_1(k3_xboole_0(X36,X37),k3_xboole_0(X34,X35))) )),
% 47.47/6.34    inference(superposition,[],[f72,f245])).
% 47.47/6.34  fof(f245,plain,(
% 47.47/6.34    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 47.47/6.34    inference(resolution,[],[f238,f51])).
% 47.47/6.34  fof(f4042,plain,(
% 47.47/6.34    ( ! [X6] : (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X6),sK1) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X6,sK1))) ) | ~spl8_18),
% 47.47/6.34    inference(superposition,[],[f850,f4033])).
% 47.47/6.34  fof(f4033,plain,(
% 47.47/6.34    k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl8_18),
% 47.47/6.34    inference(avatar_component_clause,[],[f4031])).
% 47.47/6.34  fof(f34156,plain,(
% 47.47/6.34    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(X1,sK3))) ) | (~spl8_5 | ~spl8_34)),
% 47.47/6.34    inference(superposition,[],[f8722,f72])).
% 47.47/6.34  fof(f8722,plain,(
% 47.47/6.34    ( ! [X24] : (k2_zfmisc_1(k3_xboole_0(sK2,X24),sK3) = k2_zfmisc_1(k3_xboole_0(sK2,X24),k3_xboole_0(sK1,sK3))) ) | (~spl8_5 | ~spl8_34)),
% 47.47/6.34    inference(forward_demodulation,[],[f8721,f3532])).
% 47.47/6.34  fof(f8721,plain,(
% 47.47/6.34    ( ! [X24] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X24,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,X24),k3_xboole_0(sK1,sK3))) ) | ~spl8_34),
% 47.47/6.34    inference(forward_demodulation,[],[f8675,f875])).
% 47.47/6.34  fof(f875,plain,(
% 47.47/6.34    ( ! [X17,X15,X18,X16] : (k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,k3_xboole_0(X15,X16))) = k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,X16))) )),
% 47.47/6.34    inference(forward_demodulation,[],[f854,f72])).
% 47.47/6.34  fof(f854,plain,(
% 47.47/6.34    ( ! [X17,X15,X18,X16] : (k3_xboole_0(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X18,k3_xboole_0(X15,X16))) = k2_zfmisc_1(k3_xboole_0(X17,X18),k3_xboole_0(X15,X16))) )),
% 47.47/6.34    inference(superposition,[],[f72,f281])).
% 47.47/6.34  fof(f281,plain,(
% 47.47/6.34    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 47.47/6.34    inference(superposition,[],[f245,f50])).
% 47.47/6.34  fof(f8675,plain,(
% 47.47/6.34    ( ! [X24] : (k2_zfmisc_1(k3_xboole_0(sK2,X24),k3_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X24,k3_xboole_0(sK1,sK3)))) ) | ~spl8_34),
% 47.47/6.34    inference(superposition,[],[f850,f8640])).
% 47.47/6.34  fof(f8640,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) | ~spl8_34),
% 47.47/6.34    inference(avatar_component_clause,[],[f8638])).
% 47.47/6.34  fof(f44401,plain,(
% 47.47/6.34    ( ! [X19] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK2,X19),sK3) | k1_xboole_0 = k3_xboole_0(X19,sK2)) ) | ~spl8_68),
% 47.47/6.34    inference(avatar_component_clause,[],[f44400])).
% 47.47/6.34  fof(f44402,plain,(
% 47.47/6.34    spl8_6 | spl8_68 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f5767,f101,f44400,f163])).
% 47.47/6.34  fof(f5767,plain,(
% 47.47/6.34    ( ! [X19] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(sK2,X19),sK3) | k1_xboole_0 = k3_xboole_0(X19,sK2) | k1_xboole_0 = sK3) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f5674])).
% 47.47/6.34  fof(f44390,plain,(
% 47.47/6.34    spl8_8 | spl8_67 | ~spl8_25),
% 47.47/6.34    inference(avatar_split_clause,[],[f5537,f5431,f44388,f171])).
% 47.47/6.34  fof(f44388,plain,(
% 47.47/6.34    spl8_67 <=> ! [X20] : r2_hidden(sK6(k1_xboole_0,X20,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).
% 47.47/6.34  fof(f5537,plain,(
% 47.47/6.34    ( ! [X20] : (r2_hidden(sK6(k1_xboole_0,X20,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)) ) | ~spl8_25),
% 47.47/6.34    inference(resolution,[],[f5437,f2344])).
% 47.47/6.34  fof(f44386,plain,(
% 47.47/6.34    spl8_7 | spl8_66 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f3065,f101,f44384,f167])).
% 47.47/6.34  fof(f44384,plain,(
% 47.47/6.34    spl8_66 <=> ! [X13] : (k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(X13,sK3)) | k1_xboole_0 = k3_xboole_0(sK3,X13))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).
% 47.47/6.34  fof(f3065,plain,(
% 47.47/6.34    ( ! [X13] : (k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(X13,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,X13)) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f2982])).
% 47.47/6.34  fof(f2982,plain,(
% 47.47/6.34    ( ! [X1] : (k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,X1))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f2930,f1207])).
% 47.47/6.34  fof(f1207,plain,(
% 47.47/6.34    ( ! [X9] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X9)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f837,f103])).
% 47.47/6.34  fof(f2930,plain,(
% 47.47/6.34    ( ! [X3] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X3)) = k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f1211,f50])).
% 47.47/6.34  fof(f1211,plain,(
% 47.47/6.34    ( ! [X9] : (k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f837,f103])).
% 47.47/6.34  fof(f43883,plain,(
% 47.47/6.34    spl8_6 | ~spl8_65 | ~spl8_64),
% 47.47/6.34    inference(avatar_split_clause,[],[f43853,f43848,f43880,f163])).
% 47.47/6.34  fof(f43848,plain,(
% 47.47/6.34    spl8_64 <=> ! [X13] : (k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK3,X13)) | k1_xboole_0 = k3_xboole_0(X13,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).
% 47.47/6.34  fof(f43853,plain,(
% 47.47/6.34    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) | k1_xboole_0 = sK3 | ~spl8_64),
% 47.47/6.34    inference(superposition,[],[f43849,f49])).
% 47.47/6.34  fof(f43849,plain,(
% 47.47/6.34    ( ! [X13] : (k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK3,X13)) | k1_xboole_0 = k3_xboole_0(X13,sK3)) ) | ~spl8_64),
% 47.47/6.34    inference(avatar_component_clause,[],[f43848])).
% 47.47/6.34  fof(f43850,plain,(
% 47.47/6.34    spl8_7 | spl8_64 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f3046,f101,f43848,f167])).
% 47.47/6.34  fof(f3046,plain,(
% 47.47/6.34    ( ! [X13] : (k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK3,X13)) | k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(X13,sK3)) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f2982])).
% 47.47/6.34  fof(f42537,plain,(
% 47.47/6.34    spl8_6 | spl8_61 | ~spl8_63 | ~spl8_23),
% 47.47/6.34    inference(avatar_split_clause,[],[f4865,f4853,f42532,f42502,f163])).
% 47.47/6.34  fof(f42502,plain,(
% 47.47/6.34    spl8_61 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).
% 47.47/6.34  fof(f42532,plain,(
% 47.47/6.34    spl8_63 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).
% 47.47/6.34  fof(f4853,plain,(
% 47.47/6.34    spl8_23 <=> k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 47.47/6.34  fof(f4865,plain,(
% 47.47/6.34    k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = sK3 | ~spl8_23),
% 47.47/6.34    inference(superposition,[],[f55,f4855])).
% 47.47/6.34  fof(f4855,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | ~spl8_23),
% 47.47/6.34    inference(avatar_component_clause,[],[f4853])).
% 47.47/6.34  fof(f42535,plain,(
% 47.47/6.34    ~spl8_63 | ~spl8_5 | ~spl8_23 | ~spl8_25 | ~spl8_56 | spl8_62),
% 47.47/6.34    inference(avatar_split_clause,[],[f42527,f42506,f35009,f5431,f4853,f101,f42532])).
% 47.47/6.34  fof(f35009,plain,(
% 47.47/6.34    spl8_56 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 47.47/6.34  fof(f42506,plain,(
% 47.47/6.34    spl8_62 <=> k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 47.47/6.34  fof(f42527,plain,(
% 47.47/6.34    k1_xboole_0 != k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | (~spl8_5 | ~spl8_23 | ~spl8_25 | ~spl8_56 | spl8_62)),
% 47.47/6.34    inference(superposition,[],[f42508,f40709])).
% 47.47/6.34  fof(f40709,plain,(
% 47.47/6.34    ( ! [X0] : (k2_zfmisc_1(sK0,k3_xboole_0(sK1,X0)) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,X0))) ) | (~spl8_5 | ~spl8_23 | ~spl8_25 | ~spl8_56)),
% 47.47/6.34    inference(superposition,[],[f35621,f50])).
% 47.47/6.34  fof(f35621,plain,(
% 47.47/6.34    ( ! [X19] : (k2_zfmisc_1(sK0,k3_xboole_0(X19,sK1)) = k2_zfmisc_1(sK2,k3_xboole_0(X19,sK1))) ) | (~spl8_5 | ~spl8_23 | ~spl8_25 | ~spl8_56)),
% 47.47/6.34    inference(forward_demodulation,[],[f35558,f14170])).
% 47.47/6.34  fof(f14170,plain,(
% 47.47/6.34    ( ! [X9] : (k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(X9,sK1))) ) | (~spl8_5 | ~spl8_23 | ~spl8_25)),
% 47.47/6.34    inference(backward_demodulation,[],[f1211,f14169])).
% 47.47/6.34  fof(f14169,plain,(
% 47.47/6.34    ( ! [X3] : (k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1))) ) | (~spl8_5 | ~spl8_23 | ~spl8_25)),
% 47.47/6.34    inference(backward_demodulation,[],[f2930,f14044])).
% 47.47/6.34  fof(f14044,plain,(
% 47.47/6.34    ( ! [X9] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9)) = k2_zfmisc_1(sK0,k3_xboole_0(X9,sK1))) ) | (~spl8_5 | ~spl8_23 | ~spl8_25)),
% 47.47/6.34    inference(backward_demodulation,[],[f1207,f14043])).
% 47.47/6.34  fof(f14043,plain,(
% 47.47/6.34    ( ! [X7] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X7)) = k2_zfmisc_1(sK0,k3_xboole_0(X7,sK1))) ) | (~spl8_5 | ~spl8_23 | ~spl8_25)),
% 47.47/6.34    inference(forward_demodulation,[],[f14042,f5377])).
% 47.47/6.34  fof(f5377,plain,(
% 47.47/6.34    ( ! [X7] : (k2_zfmisc_1(sK0,k3_xboole_0(X7,sK1)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,sK1))) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(backward_demodulation,[],[f4888,f5366])).
% 47.47/6.34  fof(f5366,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f5365,f103])).
% 47.47/6.34  fof(f5365,plain,(
% 47.47/6.34    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f5364,f49])).
% 47.47/6.34  fof(f5364,plain,(
% 47.47/6.34    k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f5363,f1240])).
% 47.47/6.34  fof(f1240,plain,(
% 47.47/6.34    ( ! [X70,X68,X69] : (k2_zfmisc_1(X68,k3_xboole_0(X69,X70)) = k3_xboole_0(k2_zfmisc_1(X68,k3_xboole_0(X69,X70)),k2_zfmisc_1(X68,X69))) )),
% 47.47/6.34    inference(superposition,[],[f245,f837])).
% 47.47/6.34  fof(f5363,plain,(
% 47.47/6.34    k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f5310,f4890])).
% 47.47/6.34  fof(f4890,plain,(
% 47.47/6.34    ( ! [X8] : (k2_zfmisc_1(k3_xboole_0(sK2,X8),sK3) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3)) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f4889,f3532])).
% 47.47/6.34  fof(f4889,plain,(
% 47.47/6.34    ( ! [X8] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,sK3)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3)) ) | ~spl8_23),
% 47.47/6.34    inference(forward_demodulation,[],[f4868,f879])).
% 47.47/6.34  fof(f879,plain,(
% 47.47/6.34    ( ! [X30,X33,X31,X32] : (k3_xboole_0(k2_zfmisc_1(X32,k3_xboole_0(X30,X31)),k2_zfmisc_1(X33,X31)) = k3_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X33,X31))) )),
% 47.47/6.34    inference(forward_demodulation,[],[f858,f72])).
% 47.47/6.34  fof(f858,plain,(
% 47.47/6.34    ( ! [X30,X33,X31,X32] : (k3_xboole_0(k2_zfmisc_1(X32,k3_xboole_0(X30,X31)),k2_zfmisc_1(X33,X31)) = k2_zfmisc_1(k3_xboole_0(X32,X33),k3_xboole_0(X30,X31))) )),
% 47.47/6.34    inference(superposition,[],[f72,f236])).
% 47.47/6.34  fof(f236,plain,(
% 47.47/6.34    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3)) )),
% 47.47/6.34    inference(resolution,[],[f232,f51])).
% 47.47/6.34  fof(f4868,plain,(
% 47.47/6.34    ( ! [X8] : (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),X8),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X8,sK3))) ) | ~spl8_23),
% 47.47/6.34    inference(superposition,[],[f850,f4855])).
% 47.47/6.34  fof(f5310,plain,(
% 47.47/6.34    k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(superposition,[],[f3538,f4855])).
% 47.47/6.34  fof(f4888,plain,(
% 47.47/6.34    ( ! [X7] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(sK0,k3_xboole_0(X7,sK1))) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f4887,f837])).
% 47.47/6.34  fof(f4887,plain,(
% 47.47/6.34    ( ! [X7] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK0,sK1))) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f4886,f103])).
% 47.47/6.34  fof(f4886,plain,(
% 47.47/6.34    ( ! [X7] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK2,sK3))) ) | ~spl8_23),
% 47.47/6.34    inference(forward_demodulation,[],[f4867,f72])).
% 47.47/6.34  fof(f4867,plain,(
% 47.47/6.34    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X7,sK3)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | ~spl8_23),
% 47.47/6.34    inference(superposition,[],[f837,f4855])).
% 47.47/6.34  fof(f14042,plain,(
% 47.47/6.34    ( ! [X7] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X7)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,sK1))) ) | (~spl8_5 | ~spl8_23 | ~spl8_25)),
% 47.47/6.34    inference(forward_demodulation,[],[f14041,f5400])).
% 47.47/6.34  fof(f5400,plain,(
% 47.47/6.34    ( ! [X6] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X6))) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f5399,f1207])).
% 47.47/6.34  fof(f5399,plain,(
% 47.47/6.34    ( ! [X6] : (k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6))) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f5376,f865])).
% 47.47/6.34  fof(f865,plain,(
% 47.47/6.34    ( ! [X17,X15,X18,X16] : (k3_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(k3_xboole_0(X15,X16),X18)) = k3_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18))) )),
% 47.47/6.34    inference(forward_demodulation,[],[f841,f72])).
% 47.47/6.34  fof(f841,plain,(
% 47.47/6.34    ( ! [X17,X15,X18,X16] : (k3_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(k3_xboole_0(X15,X16),X18)) = k2_zfmisc_1(k3_xboole_0(X15,X16),k3_xboole_0(X17,X18))) )),
% 47.47/6.34    inference(superposition,[],[f72,f281])).
% 47.47/6.34  fof(f5376,plain,(
% 47.47/6.34    ( ! [X6] : (k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6))) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(backward_demodulation,[],[f4885,f5366])).
% 47.47/6.34  fof(f4885,plain,(
% 47.47/6.34    ( ! [X6] : (k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6)) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X6))) ) | ~spl8_23),
% 47.47/6.34    inference(forward_demodulation,[],[f4866,f72])).
% 47.47/6.34  fof(f4866,plain,(
% 47.47/6.34    ( ! [X6] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6))) ) | ~spl8_23),
% 47.47/6.34    inference(superposition,[],[f837,f4855])).
% 47.47/6.34  fof(f14041,plain,(
% 47.47/6.34    ( ! [X7] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,X7))) ) | ~spl8_25),
% 47.47/6.34    inference(forward_demodulation,[],[f13878,f72])).
% 47.47/6.34  fof(f13878,plain,(
% 47.47/6.34    ( ! [X7] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X7))) ) | ~spl8_25),
% 47.47/6.34    inference(superposition,[],[f1217,f5433])).
% 47.47/6.34  fof(f35558,plain,(
% 47.47/6.34    ( ! [X19] : (k3_xboole_0(k2_zfmisc_1(sK2,X19),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,k3_xboole_0(X19,sK1))) ) | ~spl8_56),
% 47.47/6.34    inference(superposition,[],[f837,f35011])).
% 47.47/6.34  fof(f35011,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) | ~spl8_56),
% 47.47/6.34    inference(avatar_component_clause,[],[f35009])).
% 47.47/6.34  fof(f42508,plain,(
% 47.47/6.34    k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) | spl8_62),
% 47.47/6.34    inference(avatar_component_clause,[],[f42506])).
% 47.47/6.34  fof(f42509,plain,(
% 47.47/6.34    spl8_2 | spl8_61 | ~spl8_62 | ~spl8_18),
% 47.47/6.34    inference(avatar_split_clause,[],[f4039,f4031,f42506,f42502,f87])).
% 47.47/6.34  fof(f4039,plain,(
% 47.47/6.34    k1_xboole_0 != k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = sK1 | ~spl8_18),
% 47.47/6.34    inference(superposition,[],[f55,f4033])).
% 47.47/6.34  fof(f37002,plain,(
% 47.47/6.34    ~spl8_60 | ~spl8_56 | spl8_57),
% 47.47/6.34    inference(avatar_split_clause,[],[f35266,f35016,f35009,f36999])).
% 47.47/6.34  fof(f36999,plain,(
% 47.47/6.34    spl8_60 <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 47.47/6.34  fof(f35016,plain,(
% 47.47/6.34    spl8_57 <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 47.47/6.34  fof(f35266,plain,(
% 47.47/6.34    ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | (~spl8_56 | spl8_57)),
% 47.47/6.34    inference(backward_demodulation,[],[f35018,f35011])).
% 47.47/6.34  fof(f35018,plain,(
% 47.47/6.34    ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1)) | spl8_57),
% 47.47/6.34    inference(avatar_component_clause,[],[f35016])).
% 47.47/6.34  fof(f35720,plain,(
% 47.47/6.34    ~spl8_59 | spl8_55 | ~spl8_56),
% 47.47/6.34    inference(avatar_split_clause,[],[f35542,f35009,f35005,f35717])).
% 47.47/6.34  fof(f35717,plain,(
% 47.47/6.34    spl8_59 <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 47.47/6.34  fof(f35005,plain,(
% 47.47/6.34    spl8_55 <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 47.47/6.34  fof(f35542,plain,(
% 47.47/6.34    ~r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | (spl8_55 | ~spl8_56)),
% 47.47/6.34    inference(forward_demodulation,[],[f35006,f35011])).
% 47.47/6.34  fof(f35006,plain,(
% 47.47/6.34    ~r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | spl8_55),
% 47.47/6.34    inference(avatar_component_clause,[],[f35005])).
% 47.47/6.34  fof(f35024,plain,(
% 47.47/6.34    spl8_58 | ~spl8_55),
% 47.47/6.34    inference(avatar_split_clause,[],[f35014,f35005,f35021])).
% 47.47/6.34  fof(f35021,plain,(
% 47.47/6.34    spl8_58 <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 47.47/6.34  fof(f35014,plain,(
% 47.47/6.34    r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1)) | ~spl8_55),
% 47.47/6.34    inference(resolution,[],[f35007,f58])).
% 47.47/6.34  fof(f35007,plain,(
% 47.47/6.34    r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl8_55),
% 47.47/6.34    inference(avatar_component_clause,[],[f35005])).
% 47.47/6.34  fof(f35019,plain,(
% 47.47/6.34    ~spl8_57 | ~spl8_55),
% 47.47/6.34    inference(avatar_split_clause,[],[f35013,f35005,f35016])).
% 47.47/6.34  fof(f35013,plain,(
% 47.47/6.34    ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK0,sK1)) | ~spl8_55),
% 47.47/6.34    inference(resolution,[],[f35007,f59])).
% 47.47/6.34  fof(f35012,plain,(
% 47.47/6.34    spl8_55 | spl8_56 | ~spl8_35),
% 47.47/6.34    inference(avatar_split_clause,[],[f8757,f8753,f35009,f35005])).
% 47.47/6.34  fof(f8753,plain,(
% 47.47/6.34    spl8_35 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 47.47/6.34  fof(f8757,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) | r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl8_35),
% 47.47/6.34    inference(resolution,[],[f8755,f52])).
% 47.47/6.34  fof(f8755,plain,(
% 47.47/6.34    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl8_35),
% 47.47/6.34    inference(avatar_component_clause,[],[f8753])).
% 47.47/6.34  fof(f34059,plain,(
% 47.47/6.34    ~spl8_54 | ~spl8_53),
% 47.47/6.34    inference(avatar_split_clause,[],[f34053,f34046,f34056])).
% 47.47/6.34  fof(f34056,plain,(
% 47.47/6.34    spl8_54 <=> r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 47.47/6.34  fof(f34053,plain,(
% 47.47/6.34    ~r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0) | ~spl8_53),
% 47.47/6.34    inference(superposition,[],[f34052,f47])).
% 47.47/6.34  fof(f34052,plain,(
% 47.47/6.34    ( ! [X2] : (~r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k4_xboole_0(X2,k2_zfmisc_1(sK0,sK3)))) ) | ~spl8_53),
% 47.47/6.34    inference(resolution,[],[f34048,f76])).
% 47.47/6.34  fof(f34049,plain,(
% 47.47/6.34    spl8_8 | spl8_53 | ~spl8_25),
% 47.47/6.34    inference(avatar_split_clause,[],[f5526,f5431,f34046,f171])).
% 47.47/6.34  fof(f5526,plain,(
% 47.47/6.34    r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK3)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_25),
% 47.47/6.34    inference(resolution,[],[f5437,f143])).
% 47.47/6.34  fof(f33038,plain,(
% 47.47/6.34    ~spl8_52 | ~spl8_51),
% 47.47/6.34    inference(avatar_split_clause,[],[f33032,f33025,f33035])).
% 47.47/6.34  fof(f33025,plain,(
% 47.47/6.34    spl8_51 <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 47.47/6.34  fof(f33032,plain,(
% 47.47/6.34    ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k1_xboole_0) | ~spl8_51),
% 47.47/6.34    inference(superposition,[],[f33031,f47])).
% 47.47/6.34  fof(f33031,plain,(
% 47.47/6.34    ( ! [X2] : (~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k4_xboole_0(X2,k2_zfmisc_1(sK0,sK3)))) ) | ~spl8_51),
% 47.47/6.34    inference(resolution,[],[f33027,f76])).
% 47.47/6.34  fof(f33027,plain,(
% 47.47/6.34    r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3)) | ~spl8_51),
% 47.47/6.34    inference(avatar_component_clause,[],[f33025])).
% 47.47/6.34  fof(f33028,plain,(
% 47.47/6.34    spl8_51 | ~spl8_48),
% 47.47/6.34    inference(avatar_split_clause,[],[f33018,f33009,f33025])).
% 47.47/6.34  fof(f33009,plain,(
% 47.47/6.34    spl8_48 <=> r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 47.47/6.34  fof(f33018,plain,(
% 47.47/6.34    r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK3)) | ~spl8_48),
% 47.47/6.34    inference(resolution,[],[f33011,f58])).
% 47.47/6.34  fof(f33011,plain,(
% 47.47/6.34    r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl8_48),
% 47.47/6.34    inference(avatar_component_clause,[],[f33009])).
% 47.47/6.34  fof(f33023,plain,(
% 47.47/6.34    ~spl8_50 | ~spl8_48),
% 47.47/6.34    inference(avatar_split_clause,[],[f33017,f33009,f33020])).
% 47.47/6.34  fof(f33020,plain,(
% 47.47/6.34    spl8_50 <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 47.47/6.34  fof(f33017,plain,(
% 47.47/6.34    ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK0,sK1)) | ~spl8_48),
% 47.47/6.34    inference(resolution,[],[f33011,f59])).
% 47.47/6.34  fof(f33016,plain,(
% 47.47/6.34    spl8_48 | spl8_49 | ~spl8_26),
% 47.47/6.34    inference(avatar_split_clause,[],[f5484,f5480,f33013,f33009])).
% 47.47/6.34  fof(f5480,plain,(
% 47.47/6.34    spl8_26 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 47.47/6.34  fof(f5484,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) | r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl8_26),
% 47.47/6.34    inference(resolution,[],[f5482,f52])).
% 47.47/6.34  fof(f5482,plain,(
% 47.47/6.34    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl8_26),
% 47.47/6.34    inference(avatar_component_clause,[],[f5480])).
% 47.47/6.34  fof(f13062,plain,(
% 47.47/6.34    spl8_6 | spl8_47 | ~spl8_5 | ~spl8_41),
% 47.47/6.34    inference(avatar_split_clause,[],[f11936,f9274,f101,f13060,f163])).
% 47.47/6.34  fof(f13060,plain,(
% 47.47/6.34    spl8_47 <=> ! [X54] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X54,k3_xboole_0(sK0,sK2)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 47.47/6.34  fof(f9274,plain,(
% 47.47/6.34    spl8_41 <=> ! [X14] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 47.47/6.34  fof(f11936,plain,(
% 47.47/6.34    ( ! [X54] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X54,k3_xboole_0(sK0,sK2))) | k1_xboole_0 = sK3) ) | (~spl8_5 | ~spl8_41)),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f11910])).
% 47.47/6.34  fof(f11910,plain,(
% 47.47/6.34    ( ! [X54] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X54,k3_xboole_0(sK0,sK2))) | k1_xboole_0 = sK3) ) | (~spl8_5 | ~spl8_41)),
% 47.47/6.34    inference(superposition,[],[f55,f11857])).
% 47.47/6.34  fof(f11857,plain,(
% 47.47/6.34    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X3,k3_xboole_0(sK0,sK2))),sK3)) ) | (~spl8_5 | ~spl8_41)),
% 47.47/6.34    inference(forward_demodulation,[],[f11801,f50])).
% 47.47/6.34  fof(f11801,plain,(
% 47.47/6.34    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k4_xboole_0(X3,k3_xboole_0(sK0,sK2)),sK2),sK3)) ) | (~spl8_5 | ~spl8_41)),
% 47.47/6.34    inference(superposition,[],[f9335,f5318])).
% 47.47/6.34  fof(f5318,plain,(
% 47.47/6.34    ( ! [X4] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3)) = k2_zfmisc_1(k3_xboole_0(X4,sK2),sK3)) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f3538,f50])).
% 47.47/6.34  fof(f9335,plain,(
% 47.47/6.34    ( ! [X6,X4,X5] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X5),k2_zfmisc_1(k4_xboole_0(X4,k3_xboole_0(sK0,sK2)),X6))) ) | ~spl8_41),
% 47.47/6.34    inference(forward_demodulation,[],[f9296,f74])).
% 47.47/6.34  fof(f9296,plain,(
% 47.47/6.34    ( ! [X6,X4,X5] : (k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X5,X6)) = k3_xboole_0(k2_zfmisc_1(sK0,X5),k2_zfmisc_1(k4_xboole_0(X4,k3_xboole_0(sK0,sK2)),X6))) ) | ~spl8_41),
% 47.47/6.34    inference(superposition,[],[f72,f9275])).
% 47.47/6.34  fof(f9275,plain,(
% 47.47/6.34    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2)))) ) | ~spl8_41),
% 47.47/6.34    inference(avatar_component_clause,[],[f9274])).
% 47.47/6.34  fof(f12585,plain,(
% 47.47/6.34    spl8_46 | spl8_7 | ~spl8_5 | ~spl8_27),
% 47.47/6.34    inference(avatar_split_clause,[],[f9886,f5487,f101,f167,f12583])).
% 47.47/6.34  fof(f12583,plain,(
% 47.47/6.34    spl8_46 <=> ! [X51] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X51,k3_xboole_0(sK1,sK3)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 47.47/6.34  fof(f9886,plain,(
% 47.47/6.34    ( ! [X51] : (k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X51,k3_xboole_0(sK1,sK3)))) ) | (~spl8_5 | ~spl8_27)),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f9862])).
% 47.47/6.34  fof(f9862,plain,(
% 47.47/6.34    ( ! [X51] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X51,k3_xboole_0(sK1,sK3)))) ) | (~spl8_5 | ~spl8_27)),
% 47.47/6.34    inference(superposition,[],[f55,f9816])).
% 47.47/6.34  fof(f9816,plain,(
% 47.47/6.34    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X9,k3_xboole_0(sK1,sK3))))) ) | (~spl8_5 | ~spl8_27)),
% 47.47/6.34    inference(forward_demodulation,[],[f9767,f50])).
% 47.47/6.34  fof(f9767,plain,(
% 47.47/6.34    ( ! [X9] : (k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(k4_xboole_0(X9,k3_xboole_0(sK1,sK3)),sK3))) ) | (~spl8_5 | ~spl8_27)),
% 47.47/6.34    inference(superposition,[],[f5504,f2930])).
% 47.47/6.34  fof(f5504,plain,(
% 47.47/6.34    ( ! [X14,X15] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X14,k4_xboole_0(X15,k3_xboole_0(sK1,sK3))))) ) | ~spl8_27),
% 47.47/6.34    inference(superposition,[],[f876,f5489])).
% 47.47/6.34  fof(f12173,plain,(
% 47.47/6.34    spl8_6 | spl8_45 | ~spl8_44),
% 47.47/6.34    inference(avatar_split_clause,[],[f12125,f12007,f12170,f163])).
% 47.47/6.34  fof(f12007,plain,(
% 47.47/6.34    spl8_44 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 47.47/6.34  fof(f12125,plain,(
% 47.47/6.34    k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK3 | ~spl8_44),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f12099])).
% 47.47/6.34  fof(f12099,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK3 | ~spl8_44),
% 47.47/6.34    inference(superposition,[],[f55,f12009])).
% 47.47/6.34  fof(f12009,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3) | ~spl8_44),
% 47.47/6.34    inference(avatar_component_clause,[],[f12007])).
% 47.47/6.34  fof(f12010,plain,(
% 47.47/6.34    spl8_44 | ~spl8_5 | ~spl8_41),
% 47.47/6.34    inference(avatar_split_clause,[],[f11875,f9274,f101,f12007])).
% 47.47/6.34  fof(f11875,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3) | (~spl8_5 | ~spl8_41)),
% 47.47/6.34    inference(superposition,[],[f11857,f200])).
% 47.47/6.34  fof(f10045,plain,(
% 47.47/6.34    spl8_43 | spl8_7 | ~spl8_42),
% 47.47/6.34    inference(avatar_split_clause,[],[f10001,f9954,f167,f10042])).
% 47.47/6.34  fof(f9954,plain,(
% 47.47/6.34    spl8_42 <=> k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 47.47/6.34  fof(f10001,plain,(
% 47.47/6.34    k1_xboole_0 = sK2 | k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) | ~spl8_42),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f9977])).
% 47.47/6.34  fof(f9977,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) | ~spl8_42),
% 47.47/6.34    inference(superposition,[],[f55,f9956])).
% 47.47/6.34  fof(f9956,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))) | ~spl8_42),
% 47.47/6.34    inference(avatar_component_clause,[],[f9954])).
% 47.47/6.34  fof(f9957,plain,(
% 47.47/6.34    spl8_42 | ~spl8_5 | ~spl8_27),
% 47.47/6.34    inference(avatar_split_clause,[],[f9832,f5487,f101,f9954])).
% 47.47/6.34  fof(f9832,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))) | (~spl8_5 | ~spl8_27)),
% 47.47/6.34    inference(superposition,[],[f9816,f200])).
% 47.47/6.34  fof(f9276,plain,(
% 47.47/6.34    spl8_2 | spl8_41 | ~spl8_36),
% 47.47/6.34    inference(avatar_split_clause,[],[f9129,f8778,f9274,f87])).
% 47.47/6.34  fof(f9129,plain,(
% 47.47/6.34    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2))) | k1_xboole_0 = sK1) ) | ~spl8_36),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f9106])).
% 47.47/6.34  fof(f9106,plain,(
% 47.47/6.34    ( ! [X14] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X14,k3_xboole_0(sK0,sK2))) | k1_xboole_0 = sK1) ) | ~spl8_36),
% 47.47/6.34    inference(superposition,[],[f55,f9063])).
% 47.47/6.34  fof(f9063,plain,(
% 47.47/6.34    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,k3_xboole_0(sK0,sK2))),sK1)) ) | ~spl8_36),
% 47.47/6.34    inference(forward_demodulation,[],[f9025,f74])).
% 47.47/6.34  fof(f9025,plain,(
% 47.47/6.34    ( ! [X5] : (k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X5,k3_xboole_0(sK0,sK2))),sK1)) ) | ~spl8_36),
% 47.47/6.34    inference(superposition,[],[f8819,f581])).
% 47.47/6.34  fof(f9212,plain,(
% 47.47/6.34    spl8_2 | spl8_40 | ~spl8_39),
% 47.47/6.34    inference(avatar_split_clause,[],[f9187,f9154,f9209,f87])).
% 47.47/6.34  fof(f9154,plain,(
% 47.47/6.34    spl8_39 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 47.47/6.34  fof(f9187,plain,(
% 47.47/6.34    k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1 | ~spl8_39),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f9164])).
% 47.47/6.34  fof(f9164,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1 | ~spl8_39),
% 47.47/6.34    inference(superposition,[],[f55,f9156])).
% 47.47/6.34  fof(f9156,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl8_39),
% 47.47/6.34    inference(avatar_component_clause,[],[f9154])).
% 47.47/6.34  fof(f9157,plain,(
% 47.47/6.34    spl8_39 | ~spl8_36),
% 47.47/6.34    inference(avatar_split_clause,[],[f9097,f8778,f9154])).
% 47.47/6.34  fof(f9097,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl8_36),
% 47.47/6.34    inference(superposition,[],[f9063,f200])).
% 47.47/6.34  fof(f8906,plain,(
% 47.47/6.34    spl8_38 | ~spl8_37),
% 47.47/6.34    inference(avatar_split_clause,[],[f8872,f8843,f8903])).
% 47.47/6.34  fof(f8903,plain,(
% 47.47/6.34    spl8_38 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 47.47/6.34  fof(f8843,plain,(
% 47.47/6.34    spl8_37 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 47.47/6.34  fof(f8872,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) | ~spl8_37),
% 47.47/6.34    inference(superposition,[],[f261,f8845])).
% 47.47/6.34  fof(f8845,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl8_37),
% 47.47/6.34    inference(avatar_component_clause,[],[f8843])).
% 47.47/6.34  fof(f261,plain,(
% 47.47/6.34    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 47.47/6.34    inference(superposition,[],[f236,f50])).
% 47.47/6.34  fof(f8846,plain,(
% 47.47/6.34    spl8_37 | ~spl8_35),
% 47.47/6.34    inference(avatar_split_clause,[],[f8758,f8753,f8843])).
% 47.47/6.34  fof(f8758,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl8_35),
% 47.47/6.34    inference(resolution,[],[f8755,f51])).
% 47.47/6.34  fof(f8781,plain,(
% 47.47/6.34    spl8_36 | ~spl8_5 | ~spl8_18 | ~spl8_33),
% 47.47/6.34    inference(avatar_split_clause,[],[f8553,f7944,f4031,f101,f8778])).
% 47.47/6.34  fof(f7944,plain,(
% 47.47/6.34    spl8_33 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 47.47/6.34  fof(f8553,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | (~spl8_5 | ~spl8_18 | ~spl8_33)),
% 47.47/6.34    inference(backward_demodulation,[],[f4033,f8552])).
% 47.47/6.34  fof(f8552,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) | (~spl8_5 | ~spl8_33)),
% 47.47/6.34    inference(forward_demodulation,[],[f8551,f261])).
% 47.47/6.34  fof(f8551,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k3_xboole_0(sK1,sK3))) | (~spl8_5 | ~spl8_33)),
% 47.47/6.34    inference(forward_demodulation,[],[f8507,f50])).
% 47.47/6.34  fof(f8507,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(k3_xboole_0(sK1,sK3),sK3)) | (~spl8_5 | ~spl8_33)),
% 47.47/6.34    inference(superposition,[],[f7946,f2930])).
% 47.47/6.34  fof(f7946,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) | ~spl8_33),
% 47.47/6.34    inference(avatar_component_clause,[],[f7944])).
% 47.47/6.34  fof(f8756,plain,(
% 47.47/6.34    spl8_35 | ~spl8_34),
% 47.47/6.34    inference(avatar_split_clause,[],[f8670,f8638,f8753])).
% 47.47/6.34  fof(f8670,plain,(
% 47.47/6.34    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl8_34),
% 47.47/6.34    inference(superposition,[],[f1238,f8640])).
% 47.47/6.34  fof(f1238,plain,(
% 47.47/6.34    ( ! [X64,X62,X63] : (r1_tarski(k2_zfmisc_1(X62,k3_xboole_0(X63,X64)),k2_zfmisc_1(X62,X63))) )),
% 47.47/6.34    inference(superposition,[],[f238,f837])).
% 47.47/6.34  fof(f8641,plain,(
% 47.47/6.34    spl8_34 | ~spl8_5 | ~spl8_33),
% 47.47/6.34    inference(avatar_split_clause,[],[f8552,f7944,f101,f8638])).
% 47.47/6.34  fof(f7947,plain,(
% 47.47/6.34    spl8_33 | ~spl8_19),
% 47.47/6.34    inference(avatar_split_clause,[],[f4320,f4315,f7944])).
% 47.47/6.34  fof(f4315,plain,(
% 47.47/6.34    spl8_19 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 47.47/6.34  fof(f4320,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) | ~spl8_19),
% 47.47/6.34    inference(resolution,[],[f4317,f51])).
% 47.47/6.34  fof(f4317,plain,(
% 47.47/6.34    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) | ~spl8_19),
% 47.47/6.34    inference(avatar_component_clause,[],[f4315])).
% 47.47/6.34  fof(f6850,plain,(
% 47.47/6.34    spl8_32 | spl8_1 | ~spl8_27),
% 47.47/6.34    inference(avatar_split_clause,[],[f6724,f5487,f82,f6848])).
% 47.47/6.34  fof(f6848,plain,(
% 47.47/6.34    spl8_32 <=> ! [X15] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 47.47/6.34  fof(f6724,plain,(
% 47.47/6.34    ( ! [X15] : (k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3)))) ) | ~spl8_27),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f6707])).
% 47.47/6.34  fof(f6707,plain,(
% 47.47/6.34    ( ! [X15] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X15,k3_xboole_0(sK1,sK3)))) ) | ~spl8_27),
% 47.47/6.34    inference(superposition,[],[f55,f6671])).
% 47.47/6.34  fof(f6671,plain,(
% 47.47/6.34    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK1,sK3))))) ) | ~spl8_27),
% 47.47/6.34    inference(forward_demodulation,[],[f6638,f73])).
% 47.47/6.34  fof(f6638,plain,(
% 47.47/6.34    ( ! [X5] : (k2_zfmisc_1(sK0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK1,sK3))))) ) | ~spl8_27),
% 47.47/6.34    inference(superposition,[],[f5512,f581])).
% 47.47/6.34  fof(f6786,plain,(
% 47.47/6.34    spl8_31 | spl8_1 | ~spl8_30),
% 47.47/6.34    inference(avatar_split_clause,[],[f6769,f6741,f82,f6783])).
% 47.47/6.34  fof(f6741,plain,(
% 47.47/6.34    spl8_30 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 47.47/6.34  fof(f6769,plain,(
% 47.47/6.34    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl8_30),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f6752])).
% 47.47/6.34  fof(f6752,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl8_30),
% 47.47/6.34    inference(superposition,[],[f55,f6743])).
% 47.47/6.34  fof(f6743,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | ~spl8_30),
% 47.47/6.34    inference(avatar_component_clause,[],[f6741])).
% 47.47/6.34  fof(f6744,plain,(
% 47.47/6.34    spl8_30 | ~spl8_27),
% 47.47/6.34    inference(avatar_split_clause,[],[f6697,f5487,f6741])).
% 47.47/6.34  fof(f6697,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | ~spl8_27),
% 47.47/6.34    inference(superposition,[],[f6671,f200])).
% 47.47/6.34  fof(f5599,plain,(
% 47.47/6.34    spl8_29 | ~spl8_28),
% 47.47/6.34    inference(avatar_split_clause,[],[f5572,f5549,f5596])).
% 47.47/6.34  fof(f5596,plain,(
% 47.47/6.34    spl8_29 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 47.47/6.34  fof(f5549,plain,(
% 47.47/6.34    spl8_28 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 47.47/6.34  fof(f5572,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) | ~spl8_28),
% 47.47/6.34    inference(superposition,[],[f261,f5551])).
% 47.47/6.34  fof(f5551,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl8_28),
% 47.47/6.34    inference(avatar_component_clause,[],[f5549])).
% 47.47/6.34  fof(f5552,plain,(
% 47.47/6.34    spl8_28 | ~spl8_26),
% 47.47/6.34    inference(avatar_split_clause,[],[f5485,f5480,f5549])).
% 47.47/6.34  fof(f5485,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl8_26),
% 47.47/6.34    inference(resolution,[],[f5482,f51])).
% 47.47/6.34  fof(f5490,plain,(
% 47.47/6.34    spl8_27 | ~spl8_5 | ~spl8_23),
% 47.47/6.34    inference(avatar_split_clause,[],[f5366,f4853,f101,f5487])).
% 47.47/6.34  fof(f5483,plain,(
% 47.47/6.34    spl8_26 | ~spl8_25),
% 47.47/6.34    inference(avatar_split_clause,[],[f5439,f5431,f5480])).
% 47.47/6.34  fof(f5439,plain,(
% 47.47/6.34    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl8_25),
% 47.47/6.34    inference(superposition,[],[f3583,f5433])).
% 47.47/6.34  fof(f3583,plain,(
% 47.47/6.34    ( ! [X74,X72,X73] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X72,X74),X73),k2_zfmisc_1(X72,X73))) )),
% 47.47/6.34    inference(superposition,[],[f238,f850])).
% 47.47/6.34  fof(f5434,plain,(
% 47.47/6.34    spl8_25 | ~spl8_5 | ~spl8_23),
% 47.47/6.34    inference(avatar_split_clause,[],[f5367,f4853,f101,f5431])).
% 47.47/6.34  fof(f5367,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(backward_demodulation,[],[f4855,f5366])).
% 47.47/6.34  fof(f5202,plain,(
% 47.47/6.34    spl8_24 | ~spl8_5 | ~spl8_23),
% 47.47/6.34    inference(avatar_split_clause,[],[f5188,f4853,f101,f5199])).
% 47.47/6.34  fof(f5199,plain,(
% 47.47/6.34    spl8_24 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 47.47/6.34  fof(f5188,plain,(
% 47.47/6.34    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(superposition,[],[f4894,f49])).
% 47.47/6.34  fof(f4894,plain,(
% 47.47/6.34    ( ! [X18] : (r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(X18,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f4893,f837])).
% 47.47/6.34  fof(f4893,plain,(
% 47.47/6.34    ( ! [X18] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X18),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | (~spl8_5 | ~spl8_23)),
% 47.47/6.34    inference(forward_demodulation,[],[f4892,f103])).
% 47.47/6.34  fof(f4892,plain,(
% 47.47/6.34    ( ! [X18] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X18),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | ~spl8_23),
% 47.47/6.34    inference(forward_demodulation,[],[f4874,f72])).
% 47.47/6.34  fof(f4874,plain,(
% 47.47/6.34    ( ! [X18] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X18,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) ) | ~spl8_23),
% 47.47/6.34    inference(superposition,[],[f1235,f4855])).
% 47.47/6.34  fof(f4856,plain,(
% 47.47/6.34    spl8_23 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f4629,f101,f4853])).
% 47.47/6.34  fof(f4629,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) | ~spl8_5),
% 47.47/6.34    inference(forward_demodulation,[],[f4573,f50])).
% 47.47/6.34  fof(f4573,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f3532,f837])).
% 47.47/6.34  fof(f4785,plain,(
% 47.47/6.34    spl8_6 | spl8_22 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f4665,f101,f4783,f163])).
% 47.47/6.34  fof(f4783,plain,(
% 47.47/6.34    spl8_22 <=> ! [X14] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 47.47/6.34  fof(f4665,plain,(
% 47.47/6.34    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0)) | k1_xboole_0 = sK3) ) | ~spl8_5),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f4650])).
% 47.47/6.34  fof(f4650,plain,(
% 47.47/6.34    ( ! [X14] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X14,sK0)) | k1_xboole_0 = sK3) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f4576])).
% 47.47/6.34  fof(f4576,plain,(
% 47.47/6.34    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X3,sK0)),sK3)) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f3532,f866])).
% 47.47/6.34  fof(f866,plain,(
% 47.47/6.34    ( ! [X26,X24,X23,X25] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(k4_xboole_0(X24,X23),X26))) )),
% 47.47/6.34    inference(forward_demodulation,[],[f843,f74])).
% 47.47/6.34  fof(f843,plain,(
% 47.47/6.34    ( ! [X26,X24,X23,X25] : (k3_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(k4_xboole_0(X24,X23),X26)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X25,X26))) )),
% 47.47/6.34    inference(superposition,[],[f72,f581])).
% 47.47/6.34  fof(f4722,plain,(
% 47.47/6.34    spl8_6 | spl8_21 | ~spl8_20),
% 47.47/6.34    inference(avatar_split_clause,[],[f4708,f4681,f4719,f163])).
% 47.47/6.34  fof(f4681,plain,(
% 47.47/6.34    spl8_20 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 47.47/6.34  fof(f4708,plain,(
% 47.47/6.34    k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = sK3 | ~spl8_20),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f4693])).
% 47.47/6.34  fof(f4693,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = sK3 | ~spl8_20),
% 47.47/6.34    inference(superposition,[],[f55,f4683])).
% 47.47/6.34  fof(f4683,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) | ~spl8_20),
% 47.47/6.34    inference(avatar_component_clause,[],[f4681])).
% 47.47/6.34  fof(f4684,plain,(
% 47.47/6.34    spl8_20 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f4641,f101,f4681])).
% 47.47/6.34  fof(f4641,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f4576,f200])).
% 47.47/6.34  fof(f4318,plain,(
% 47.47/6.34    spl8_19 | ~spl8_5 | ~spl8_18),
% 47.47/6.34    inference(avatar_split_clause,[],[f4304,f4031,f101,f4315])).
% 47.47/6.34  fof(f4304,plain,(
% 47.47/6.34    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) | (~spl8_5 | ~spl8_18)),
% 47.47/6.34    inference(superposition,[],[f4064,f49])).
% 47.47/6.34  fof(f4064,plain,(
% 47.47/6.34    ( ! [X19] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X19,sK0),sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) ) | (~spl8_5 | ~spl8_18)),
% 47.47/6.34    inference(forward_demodulation,[],[f4051,f4060])).
% 47.47/6.34  fof(f4060,plain,(
% 47.47/6.34    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k2_zfmisc_1(k3_xboole_0(X7,sK0),sK1)) ) | (~spl8_5 | ~spl8_18)),
% 47.47/6.34    inference(forward_demodulation,[],[f4059,f850])).
% 47.47/6.34  fof(f4059,plain,(
% 47.47/6.34    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK0,sK1))) ) | (~spl8_5 | ~spl8_18)),
% 47.47/6.34    inference(forward_demodulation,[],[f4058,f103])).
% 47.47/6.34  fof(f4058,plain,(
% 47.47/6.34    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK2,sK3))) ) | ~spl8_18),
% 47.47/6.34    inference(forward_demodulation,[],[f4043,f875])).
% 47.47/6.34  fof(f4043,plain,(
% 47.47/6.34    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(X7,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X7,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) ) | ~spl8_18),
% 47.47/6.34    inference(superposition,[],[f850,f4033])).
% 47.47/6.34  fof(f4051,plain,(
% 47.47/6.34    ( ! [X19] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X19,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) ) | ~spl8_18),
% 47.47/6.34    inference(superposition,[],[f3580,f4033])).
% 47.47/6.34  fof(f4034,plain,(
% 47.47/6.34    spl8_18 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f3624,f101,f4031])).
% 47.47/6.34  fof(f3624,plain,(
% 47.47/6.34    k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl8_5),
% 47.47/6.34    inference(forward_demodulation,[],[f3548,f50])).
% 47.47/6.34  fof(f3548,plain,(
% 47.47/6.34    k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f850,f1211])).
% 47.47/6.34  fof(f3969,plain,(
% 47.47/6.34    spl8_2 | spl8_17 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f3854,f101,f3967,f87])).
% 47.47/6.34  fof(f3854,plain,(
% 47.47/6.34    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2)) | k1_xboole_0 = sK1) ) | ~spl8_5),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f3839])).
% 47.47/6.34  fof(f3839,plain,(
% 47.47/6.34    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X8,sK2)) | k1_xboole_0 = sK1) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f3544])).
% 47.47/6.34  fof(f3544,plain,(
% 47.47/6.34    ( ! [X11] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X11,sK2)),sK1)) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f850,f887])).
% 47.47/6.34  fof(f887,plain,(
% 47.47/6.34    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X12,sK2),X13))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f866,f103])).
% 47.47/6.34  fof(f3906,plain,(
% 47.47/6.34    spl8_2 | spl8_16 | ~spl8_15),
% 47.47/6.34    inference(avatar_split_clause,[],[f3893,f3867,f3903,f87])).
% 47.47/6.34  fof(f3867,plain,(
% 47.47/6.34    spl8_15 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 47.47/6.34  fof(f3893,plain,(
% 47.47/6.34    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1 | ~spl8_15),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f3878])).
% 47.47/6.34  fof(f3878,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1 | ~spl8_15),
% 47.47/6.34    inference(superposition,[],[f55,f3869])).
% 47.47/6.34  fof(f3869,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl8_15),
% 47.47/6.34    inference(avatar_component_clause,[],[f3867])).
% 47.47/6.34  fof(f3870,plain,(
% 47.47/6.34    spl8_15 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f3834,f101,f3867])).
% 47.47/6.34  fof(f3834,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f3544,f200])).
% 47.47/6.34  fof(f2468,plain,(
% 47.47/6.34    spl8_6 | spl8_7 | ~spl8_8 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f2166,f101,f171,f167,f163])).
% 47.47/6.34  fof(f2166,plain,(
% 47.47/6.34    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f103])).
% 47.47/6.34  fof(f2362,plain,(
% 47.47/6.34    spl8_2 | spl8_1 | ~spl8_8),
% 47.47/6.34    inference(avatar_split_clause,[],[f2357,f171,f82,f87])).
% 47.47/6.34  fof(f2357,plain,(
% 47.47/6.34    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_8),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f2347])).
% 47.47/6.34  fof(f2347,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_8),
% 47.47/6.34    inference(superposition,[],[f55,f172])).
% 47.47/6.34  fof(f172,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_8),
% 47.47/6.34    inference(avatar_component_clause,[],[f171])).
% 47.47/6.34  fof(f2239,plain,(
% 47.47/6.34    spl8_14 | spl8_7 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f1949,f101,f167,f2237])).
% 47.47/6.34  fof(f2237,plain,(
% 47.47/6.34    spl8_14 <=> ! [X8] : k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 47.47/6.34  fof(f1949,plain,(
% 47.47/6.34    ( ! [X8] : (k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1))) ) | ~spl8_5),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f1939])).
% 47.47/6.34  fof(f1939,plain,(
% 47.47/6.34    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK3,k4_xboole_0(X8,sK1))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f1886])).
% 47.47/6.34  fof(f1886,plain,(
% 47.47/6.34    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(sK2,k3_xboole_0(sK3,k4_xboole_0(X3,sK1)))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f1207,f876])).
% 47.47/6.34  fof(f2119,plain,(
% 47.47/6.34    spl8_8 | ~spl8_5 | ~spl8_7),
% 47.47/6.34    inference(avatar_split_clause,[],[f2031,f167,f101,f171])).
% 47.47/6.34  fof(f2031,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl8_5 | ~spl8_7)),
% 47.47/6.34    inference(forward_demodulation,[],[f1991,f74])).
% 47.47/6.34  fof(f1991,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3) | (~spl8_5 | ~spl8_7)),
% 47.47/6.34    inference(backward_demodulation,[],[f103,f169])).
% 47.47/6.34  fof(f169,plain,(
% 47.47/6.34    k1_xboole_0 = sK2 | ~spl8_7),
% 47.47/6.34    inference(avatar_component_clause,[],[f167])).
% 47.47/6.34  fof(f1989,plain,(
% 47.47/6.34    spl8_13 | spl8_7 | ~spl8_12),
% 47.47/6.34    inference(avatar_split_clause,[],[f1979,f1959,f167,f1986])).
% 47.47/6.34  fof(f1959,plain,(
% 47.47/6.34    spl8_12 <=> k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 47.47/6.34  fof(f1979,plain,(
% 47.47/6.34    k1_xboole_0 = sK2 | k1_xboole_0 = k4_xboole_0(sK3,sK1) | ~spl8_12),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f1969])).
% 47.47/6.34  fof(f1969,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k4_xboole_0(sK3,sK1) | ~spl8_12),
% 47.47/6.34    inference(superposition,[],[f55,f1961])).
% 47.47/6.34  fof(f1961,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) | ~spl8_12),
% 47.47/6.34    inference(avatar_component_clause,[],[f1959])).
% 47.47/6.34  fof(f1962,plain,(
% 47.47/6.34    spl8_12 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f1932,f101,f1959])).
% 47.47/6.34  fof(f1932,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f1886,f200])).
% 47.47/6.34  fof(f1508,plain,(
% 47.47/6.34    spl8_11 | spl8_1 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f1418,f101,f82,f1506])).
% 47.47/6.34  fof(f1418,plain,(
% 47.47/6.34    ( ! [X2] : (k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))) ) | ~spl8_5),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f1408])).
% 47.47/6.34  fof(f1408,plain,(
% 47.47/6.34    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(X2,sK3))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f1212])).
% 47.47/6.34  fof(f1212,plain,(
% 47.47/6.34    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X0,sK3)))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f837,f965])).
% 47.47/6.34  fof(f965,plain,(
% 47.47/6.34    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)))) ) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f876,f103])).
% 47.47/6.34  fof(f1454,plain,(
% 47.47/6.34    spl8_10 | spl8_1 | ~spl8_9),
% 47.47/6.34    inference(avatar_split_clause,[],[f1445,f1426,f82,f1451])).
% 47.47/6.34  fof(f1426,plain,(
% 47.47/6.34    spl8_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 47.47/6.34    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 47.47/6.34  fof(f1445,plain,(
% 47.47/6.34    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl8_9),
% 47.47/6.34    inference(trivial_inequality_removal,[],[f1435])).
% 47.47/6.34  fof(f1435,plain,(
% 47.47/6.34    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl8_9),
% 47.47/6.34    inference(superposition,[],[f55,f1428])).
% 47.47/6.34  fof(f1428,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | ~spl8_9),
% 47.47/6.34    inference(avatar_component_clause,[],[f1426])).
% 47.47/6.34  fof(f1429,plain,(
% 47.47/6.34    spl8_9 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f1405,f101,f1426])).
% 47.47/6.34  fof(f1405,plain,(
% 47.47/6.34    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f1212,f200])).
% 47.47/6.34  fof(f174,plain,(
% 47.47/6.34    spl8_6 | spl8_7 | ~spl8_8 | ~spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f161,f101,f171,f167,f163])).
% 47.47/6.34  fof(f161,plain,(
% 47.47/6.34    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl8_5),
% 47.47/6.34    inference(superposition,[],[f55,f103])).
% 47.47/6.34  fof(f104,plain,(
% 47.47/6.34    spl8_5),
% 47.47/6.34    inference(avatar_split_clause,[],[f43,f101])).
% 47.47/6.34  fof(f43,plain,(
% 47.47/6.34    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 47.47/6.34    inference(cnf_transformation,[],[f26])).
% 47.47/6.34  fof(f26,plain,(
% 47.47/6.34    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 47.47/6.34    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).
% 47.47/6.34  fof(f25,plain,(
% 47.47/6.34    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 47.47/6.34    introduced(choice_axiom,[])).
% 47.47/6.34  fof(f19,plain,(
% 47.47/6.34    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 47.47/6.34    inference(flattening,[],[f18])).
% 47.47/6.34  fof(f18,plain,(
% 47.47/6.34    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 47.47/6.34    inference(ennf_transformation,[],[f14])).
% 47.47/6.34  fof(f14,negated_conjecture,(
% 47.47/6.34    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 47.47/6.34    inference(negated_conjecture,[],[f13])).
% 47.47/6.34  fof(f13,conjecture,(
% 47.47/6.34    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 47.47/6.34    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 47.47/6.34  fof(f99,plain,(
% 47.47/6.34    ~spl8_3 | ~spl8_4),
% 47.47/6.34    inference(avatar_split_clause,[],[f46,f96,f92])).
% 47.47/6.34  fof(f46,plain,(
% 47.47/6.34    sK1 != sK3 | sK0 != sK2),
% 47.47/6.34    inference(cnf_transformation,[],[f26])).
% 47.47/6.34  fof(f90,plain,(
% 47.47/6.34    ~spl8_2),
% 47.47/6.34    inference(avatar_split_clause,[],[f45,f87])).
% 47.47/6.34  fof(f45,plain,(
% 47.47/6.34    k1_xboole_0 != sK1),
% 47.47/6.34    inference(cnf_transformation,[],[f26])).
% 47.47/6.34  fof(f85,plain,(
% 47.47/6.34    ~spl8_1),
% 47.47/6.34    inference(avatar_split_clause,[],[f44,f82])).
% 47.47/6.34  fof(f44,plain,(
% 47.47/6.34    k1_xboole_0 != sK0),
% 47.47/6.34    inference(cnf_transformation,[],[f26])).
% 47.47/6.34  % SZS output end Proof for theBenchmark
% 47.47/6.34  % (5182)------------------------------
% 47.47/6.34  % (5182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 47.47/6.34  % (5182)Termination reason: Refutation
% 47.47/6.34  
% 47.47/6.34  % (5182)Memory used [KB]: 100041
% 47.47/6.34  % (5182)Time elapsed: 5.208 s
% 47.47/6.34  % (5182)------------------------------
% 47.47/6.34  % (5182)------------------------------
% 47.47/6.35  % (5131)Success in time 5.99 s
%------------------------------------------------------------------------------
