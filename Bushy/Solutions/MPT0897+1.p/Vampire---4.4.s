%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t57_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 351 expanded)
%              Number of leaves         :   27 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  567 (1244 expanded)
%              Number of equality atoms :  266 ( 749 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f54,f79,f127,f132,f140,f144,f152,f156,f164,f172,f173,f183,f190,f194,f196,f200,f203,f246,f247,f257,f301,f302,f312,f359])).

fof(f359,plain,
    ( spl8_5
    | spl8_13
    | spl8_23
    | spl8_25
    | spl8_29
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_13
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f357,f60])).

fof(f60,plain,
    ( sK3 != sK7
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl8_5
  <=> sK3 != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f357,plain,
    ( sK3 = sK7
    | ~ spl8_13
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(equality_resolution,[],[f351])).

fof(f351,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK7 = X31 )
    | ~ spl8_13
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f350,f102])).

fof(f102,plain,
    ( k1_xboole_0 != sK7
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_13
  <=> k1_xboole_0 != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f350,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK7
        | sK7 = X31 )
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f349,f139])).

fof(f139,plain,
    ( k1_xboole_0 != sK2
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_23
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f349,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK7
        | sK7 = X31 )
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f348,f151])).

fof(f151,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_25
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f348,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK7
        | sK7 = X31 )
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f337,f189])).

fof(f189,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl8_29
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f337,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK7
        | sK7 = X31 )
    | ~ spl8_32 ),
    inference(superposition,[],[f30,f311])).

fof(f311,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK2,sK7)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl8_32
  <=> k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK2,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | X3 = X7 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t57_mcart_1.p',t56_mcart_1)).

fof(f312,plain,
    ( spl8_32
    | ~ spl8_6
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f304,f255,f62,f310])).

fof(f62,plain,
    ( spl8_6
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f255,plain,
    ( spl8_30
  <=> k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f304,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK2,sK7)
    | ~ spl8_6
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f63,f256])).

fof(f256,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK6,sK7)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f255])).

fof(f63,plain,
    ( sK2 = sK6
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f302,plain,
    ( spl8_6
    | spl8_13
    | spl8_15
    | spl8_25
    | spl8_29
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f299,f255,f188,f150,f107,f101,f62])).

fof(f107,plain,
    ( spl8_15
  <=> k1_xboole_0 != sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f299,plain,
    ( sK2 = sK6
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(equality_resolution,[],[f293])).

fof(f293,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK6 = X30 )
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f292,f102])).

fof(f292,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK7
        | sK6 = X30 )
    | ~ spl8_15
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f291,f108])).

fof(f108,plain,
    ( k1_xboole_0 != sK6
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f291,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK6 = X30 )
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f290,f151])).

fof(f290,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK6 = X30 )
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f279,f189])).

fof(f279,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK6 = X30 )
    | ~ spl8_30 ),
    inference(superposition,[],[f29,f256])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | X2 = X6 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f301,plain,
    ( spl8_7
    | spl8_13
    | spl8_15
    | spl8_25
    | spl8_29
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_25
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f299,f66])).

fof(f66,plain,
    ( sK2 != sK6
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl8_7
  <=> sK2 != sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f257,plain,
    ( spl8_30
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f249,f181,f68,f255])).

fof(f68,plain,
    ( spl8_8
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f181,plain,
    ( spl8_26
  <=> k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f249,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK6,sK7)
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(backward_demodulation,[],[f69,f182])).

fof(f182,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK5,sK6,sK7)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f181])).

fof(f69,plain,
    ( sK1 = sK5
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f247,plain,
    ( spl8_8
    | spl8_13
    | spl8_15
    | spl8_17
    | ~ spl8_26
    | spl8_29 ),
    inference(avatar_split_clause,[],[f244,f188,f181,f113,f107,f101,f68])).

fof(f113,plain,
    ( spl8_17
  <=> k1_xboole_0 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f244,plain,
    ( sK1 = sK5
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(equality_resolution,[],[f238])).

fof(f238,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK5 = X29 )
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f237,f102])).

fof(f237,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK7
        | sK5 = X29 )
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f236,f108])).

fof(f236,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK5 = X29 )
    | ~ spl8_17
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f235,f114])).

fof(f114,plain,
    ( k1_xboole_0 != sK5
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f235,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK5 = X29 )
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f224,f189])).

fof(f224,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK5 = X29 )
    | ~ spl8_26 ),
    inference(superposition,[],[f28,f182])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | X1 = X5 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f246,plain,
    ( spl8_9
    | spl8_13
    | spl8_15
    | spl8_17
    | ~ spl8_26
    | spl8_29 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f244,f72])).

fof(f72,plain,
    ( sK1 != sK5
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_9
  <=> sK1 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f203,plain,
    ( spl8_26
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f202,f74,f52,f181])).

fof(f52,plain,
    ( spl8_2
  <=> k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f74,plain,
    ( spl8_10
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f202,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK5,sK6,sK7)
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f53,f75])).

fof(f75,plain,
    ( sK0 = sK4
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f53,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f200,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f198,f46])).

fof(f46,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl8_1
  <=> k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f198,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f197,f40])).

fof(f40,plain,(
    ! [X2,X3,X1] : k4_zfmisc_1(k1_xboole_0,X1,X2,X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t57_mcart_1.p',t55_mcart_1)).

fof(f197,plain,
    ( k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f53,f123])).

fof(f123,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_18
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f196,plain,
    ( ~ spl8_29
    | spl8_11
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f195,f122,f77,f188])).

fof(f77,plain,
    ( spl8_11
  <=> sK0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f195,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f123,f78])).

fof(f78,plain,
    ( sK0 != sK4
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f194,plain,
    ( spl8_18
    | spl8_20
    | ~ spl8_2
    | spl8_13
    | spl8_15
    | spl8_17 ),
    inference(avatar_split_clause,[],[f193,f113,f107,f101,f52,f125,f122])).

fof(f125,plain,
    ( spl8_20
  <=> ! [X1,X3,X0,X2] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X0,X1,X2,X3)
        | sK4 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f193,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK4
        | sK4 = X4 )
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f192,f102])).

fof(f192,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK7
        | sK4 = X4 )
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f191,f108])).

fof(f191,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK4 = X4 )
    | ~ spl8_2
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f158,f114])).

fof(f158,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK4 = X4 )
    | ~ spl8_2 ),
    inference(superposition,[],[f27,f53])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f190,plain,
    ( ~ spl8_29
    | ~ spl8_10
    | spl8_19 ),
    inference(avatar_split_clause,[],[f176,f119,f74,f188])).

fof(f119,plain,
    ( spl8_19
  <=> k1_xboole_0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f176,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_10
    | ~ spl8_19 ),
    inference(superposition,[],[f120,f75])).

fof(f120,plain,
    ( k1_xboole_0 != sK4
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f119])).

fof(f183,plain,
    ( spl8_26
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f175,f74,f52,f181])).

fof(f175,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK5,sK6,sK7)
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f75,f53])).

fof(f173,plain,
    ( spl8_10
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f170,f125,f74])).

fof(f170,plain,
    ( sK0 = sK4
    | ~ spl8_20 ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X0,X1,X2,X3)
        | sK4 = X0 )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f125])).

fof(f172,plain,
    ( spl8_11
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f170,f78])).

fof(f164,plain,
    ( spl8_20
    | ~ spl8_2
    | spl8_13
    | spl8_15
    | spl8_17
    | spl8_19 ),
    inference(avatar_split_clause,[],[f163,f119,f113,f107,f101,f52,f125])).

fof(f163,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X4,X5,X6,X7)
        | sK4 = X4 )
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f162,f102])).

fof(f162,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK7
        | sK4 = X4 )
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f161,f108])).

fof(f161,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK4 = X4 )
    | ~ spl8_2
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f160,f114])).

fof(f160,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK4 = X4 )
    | ~ spl8_2
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f158,f120])).

fof(f156,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f154,f46])).

fof(f154,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f153,f39])).

fof(f39,plain,(
    ! [X2,X0,X3] : k4_zfmisc_1(X0,k1_xboole_0,X2,X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f153,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,k1_xboole_0,sK6,sK7)
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f53,f117])).

fof(f117,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_16
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f152,plain,
    ( ~ spl8_25
    | spl8_9
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f145,f116,f71,f150])).

fof(f145,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_9
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f117,f72])).

fof(f144,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f142,f46])).

fof(f142,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f141,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] : k4_zfmisc_1(X0,X1,k1_xboole_0,X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f141,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,k1_xboole_0,sK7)
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f53,f111])).

fof(f111,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_14
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f140,plain,
    ( ~ spl8_23
    | spl8_7
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f133,f110,f65,f138])).

fof(f133,plain,
    ( k1_xboole_0 != sK2
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f111,f66])).

fof(f132,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f130,f46])).

fof(f130,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f128,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_zfmisc_1(X0,X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f128,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f105,f53])).

fof(f105,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_12
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f127,plain,
    ( spl8_12
    | spl8_14
    | spl8_16
    | spl8_18
    | spl8_20
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f85,f52,f125,f122,f116,f110,f104])).

fof(f85,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK7
        | sK4 = X0 )
    | ~ spl8_2 ),
    inference(superposition,[],[f27,f53])).

fof(f79,plain,
    ( ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f23,f77,f71,f65,f59])).

fof(f23,plain,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t57_mcart_1.p',t57_mcart_1)).

fof(f54,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
