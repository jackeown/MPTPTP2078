%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:35 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 318 expanded)
%              Number of leaves         :   56 ( 156 expanded)
%              Depth                    :    8
%              Number of atoms          :  473 ( 761 expanded)
%              Number of equality atoms :   93 ( 167 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f62,f66,f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f110,f128,f141,f159,f173,f177,f182,f239,f268,f306,f311,f316,f352,f360,f376,f412,f502,f770,f801,f1233,f2131,f2148,f2454,f2918,f3335,f3364])).

fof(f3364,plain,
    ( ~ spl5_9
    | spl5_22
    | ~ spl5_110
    | ~ spl5_133
    | ~ spl5_146 ),
    inference(avatar_contradiction_clause,[],[f3363])).

fof(f3363,plain,
    ( $false
    | ~ spl5_9
    | spl5_22
    | ~ spl5_110
    | ~ spl5_133
    | ~ spl5_146 ),
    inference(subsumption_resolution,[],[f181,f3362])).

fof(f3362,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_9
    | ~ spl5_110
    | ~ spl5_133
    | ~ spl5_146 ),
    inference(forward_demodulation,[],[f3361,f2917])).

fof(f2917,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_133 ),
    inference(avatar_component_clause,[],[f2916])).

fof(f2916,plain,
    ( spl5_133
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f3361,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl5_9
    | ~ spl5_110
    | ~ spl5_146 ),
    inference(forward_demodulation,[],[f3349,f85])).

fof(f85,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f3349,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_110
    | ~ spl5_146 ),
    inference(superposition,[],[f2453,f3334])).

fof(f3334,plain,
    ( ! [X37,X35] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X37),X35)
    | ~ spl5_146 ),
    inference(avatar_component_clause,[],[f3333])).

fof(f3333,plain,
    ( spl5_146
  <=> ! [X35,X37] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X37),X35) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f2453,plain,
    ( ! [X1] : k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)) = k4_xboole_0(sK0,X1)
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f2452])).

fof(f2452,plain,
    ( spl5_110
  <=> ! [X1] : k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)) = k4_xboole_0(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f181,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_22
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f3335,plain,
    ( spl5_146
    | ~ spl5_37
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f786,f768,f358,f3333])).

fof(f358,plain,
    ( spl5_37
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f768,plain,
    ( spl5_59
  <=> ! [X9,X11,X10] : k3_xboole_0(X9,k4_xboole_0(k2_xboole_0(X9,X10),X11)) = k4_xboole_0(X9,X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f786,plain,
    ( ! [X37,X35] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X37),X35)
    | ~ spl5_37
    | ~ spl5_59 ),
    inference(superposition,[],[f359,f769])).

fof(f769,plain,
    ( ! [X10,X11,X9] : k3_xboole_0(X9,k4_xboole_0(k2_xboole_0(X9,X10),X11)) = k4_xboole_0(X9,X11)
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f768])).

fof(f359,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f358])).

fof(f2918,plain,
    ( spl5_133
    | ~ spl5_32
    | ~ spl5_33
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f404,f374,f314,f309,f2916])).

fof(f309,plain,
    ( spl5_32
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f314,plain,
    ( spl5_33
  <=> ! [X1] : r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f374,plain,
    ( spl5_38
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f404,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_32
    | ~ spl5_33
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f379,f380])).

fof(f380,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f310,f375])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f374])).

fof(f310,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f309])).

fof(f379,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)
    | ~ spl5_33
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f315,f375])).

fof(f315,plain,
    ( ! [X1] : r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f314])).

fof(f2454,plain,
    ( spl5_110
    | ~ spl5_20
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f251,f236,f171,f2452])).

fof(f171,plain,
    ( spl5_20
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f236,plain,
    ( spl5_25
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f251,plain,
    ( ! [X1] : k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)) = k4_xboole_0(sK0,X1)
    | ~ spl5_20
    | ~ spl5_25 ),
    inference(superposition,[],[f172,f238])).

fof(f238,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f236])).

fof(f172,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f2148,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_21
    | ~ spl5_36
    | spl5_44
    | ~ spl5_60
    | ~ spl5_102 ),
    inference(avatar_contradiction_clause,[],[f2147])).

fof(f2147,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_21
    | ~ spl5_36
    | spl5_44
    | ~ spl5_60
    | ~ spl5_102 ),
    inference(subsumption_resolution,[],[f501,f2146])).

fof(f2146,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_60
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f2145,f69])).

fof(f69,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_5
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f2145,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK0,k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_60
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f2144,f65])).

fof(f65,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_4
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2144,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK2,sK2)))
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_60
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f2137,f814])).

fof(f814,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl5_21
    | ~ spl5_60 ),
    inference(superposition,[],[f800,f176])).

fof(f176,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f800,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f799])).

fof(f799,plain,
    ( spl5_60
  <=> ! [X3,X2,X4] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f2137,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK0,sK2)))
    | ~ spl5_36
    | ~ spl5_102 ),
    inference(superposition,[],[f351,f2130])).

fof(f2130,plain,
    ( k5_xboole_0(sK0,sK2) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f2128])).

fof(f2128,plain,
    ( spl5_102
  <=> k5_xboole_0(sK0,sK2) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f351,plain,
    ( ! [X4,X5] : r1_xboole_0(X4,k5_xboole_0(X4,k2_xboole_0(X4,X5)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl5_36
  <=> ! [X5,X4] : r1_xboole_0(X4,k5_xboole_0(X4,k2_xboole_0(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f501,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl5_44 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl5_44
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f2131,plain,
    ( spl5_102
    | ~ spl5_8
    | ~ spl5_25
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f1282,f1231,f236,f80,f2128])).

fof(f80,plain,
    ( spl5_8
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1231,plain,
    ( spl5_68
  <=> ! [X1,X0,X2] : k2_xboole_0(X2,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f1282,plain,
    ( k5_xboole_0(sK0,sK2) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl5_8
    | ~ spl5_25
    | ~ spl5_68 ),
    inference(forward_demodulation,[],[f1248,f81])).

fof(f81,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1248,plain,
    ( k5_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl5_25
    | ~ spl5_68 ),
    inference(superposition,[],[f1232,f238])).

fof(f1232,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X2,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1233,plain,
    ( spl5_68
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f194,f171,f126,f1231])).

fof(f126,plain,
    ( spl5_16
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f194,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X2,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(superposition,[],[f127,f172])).

fof(f127,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f801,plain,
    ( spl5_60
    | ~ spl5_8
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f198,f175,f80,f799])).

fof(f198,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)
    | ~ spl5_8
    | ~ spl5_21 ),
    inference(superposition,[],[f176,f81])).

fof(f770,plain,
    ( spl5_59
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f192,f171,f88,f768])).

fof(f88,plain,
    ( spl5_10
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f192,plain,
    ( ! [X10,X11,X9] : k3_xboole_0(X9,k4_xboole_0(k2_xboole_0(X9,X10),X11)) = k4_xboole_0(X9,X11)
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(superposition,[],[f172,f89])).

fof(f89,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f502,plain,
    ( ~ spl5_44
    | ~ spl5_28
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f422,f410,f265,f499])).

fof(f265,plain,
    ( spl5_28
  <=> r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f410,plain,
    ( spl5_39
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f422,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | ~ spl5_28
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f267,f411])).

fof(f411,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f410])).

fof(f267,plain,
    ( r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f265])).

fof(f412,plain,
    ( spl5_39
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f135,f96,f84,f410])).

fof(f96,plain,
    ( spl5_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(superposition,[],[f97,f85])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f376,plain,
    ( spl5_38
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f134,f96,f76,f374])).

fof(f76,plain,
    ( spl5_7
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(resolution,[],[f97,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f360,plain,
    ( spl5_37
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f153,f108,f72,f358])).

fof(f72,plain,
    ( spl5_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f108,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f153,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f73,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f73,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f352,plain,
    ( spl5_36
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f120,f92,f88,f350])).

fof(f92,plain,
    ( spl5_11
  <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f120,plain,
    ( ! [X4,X5] : r1_xboole_0(X4,k5_xboole_0(X4,k2_xboole_0(X4,X5)))
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(superposition,[],[f93,f89])).

fof(f93,plain,
    ( ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f316,plain,
    ( spl5_33
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f122,f92,f68,f314])).

fof(f122,plain,
    ( ! [X1] : r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(superposition,[],[f93,f69])).

fof(f311,plain,
    ( spl5_32
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f307,f304,f139,f100,f309])).

fof(f100,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f139,plain,
    ( spl5_18
  <=> ! [X4] : r1_tarski(X4,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f304,plain,
    ( spl5_31
  <=> ! [X0] : r1_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f307,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f305,f273])).

fof(f273,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f140,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f140,plain,
    ( ! [X4] : r1_tarski(X4,X4)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f139])).

fof(f305,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f304])).

fof(f306,plain,
    ( spl5_31
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f121,f92,f64,f304])).

fof(f121,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(superposition,[],[f93,f65])).

fof(f268,plain,
    ( spl5_28
    | spl5_3
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f183,f157,f59,f265])).

fof(f59,plain,
    ( spl5_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f157,plain,
    ( spl5_19
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f183,plain,
    ( r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2))
    | spl5_3
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f61,f158])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f157])).

fof(f61,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f239,plain,
    ( spl5_25
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f142,f100,f50,f236])).

fof(f50,plain,
    ( spl5_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f142,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f52,f101])).

fof(f52,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f182,plain,
    ( ~ spl5_22
    | spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f151,f104,f55,f179])).

fof(f55,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f151,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl5_2
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f57,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,X1)
        | r1_tarski(X0,X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f57,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f177,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f48,f175])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f173,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f47,f171])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f159,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f42,f157])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f141,plain,
    ( spl5_18
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f117,f88,f72,f139])).

fof(f117,plain,
    ( ! [X4] : r1_tarski(X4,X4)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(superposition,[],[f73,f89])).

fof(f128,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f40,f126])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f110,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f46,f108])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f106,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f45,f104])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f44,f100])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f98,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f39,f92])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f90,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f86,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f82,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f78,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f74,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f70,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f66,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f62,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f59,f55])).

fof(f31,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f53,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f30,f50])).

fof(f30,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:49:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (17740)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (17739)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (17728)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (17741)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (17738)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (17734)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (17744)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (17732)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (17745)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (17733)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (17742)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (17735)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (17730)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (17731)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (17743)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (17729)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.53  % (17736)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (17737)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 2.19/0.66  % (17733)Refutation found. Thanks to Tanya!
% 2.19/0.66  % SZS status Theorem for theBenchmark
% 2.19/0.66  % SZS output start Proof for theBenchmark
% 2.19/0.66  fof(f3373,plain,(
% 2.19/0.66    $false),
% 2.19/0.66    inference(avatar_sat_refutation,[],[f53,f62,f66,f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f110,f128,f141,f159,f173,f177,f182,f239,f268,f306,f311,f316,f352,f360,f376,f412,f502,f770,f801,f1233,f2131,f2148,f2454,f2918,f3335,f3364])).
% 2.19/0.66  fof(f3364,plain,(
% 2.19/0.66    ~spl5_9 | spl5_22 | ~spl5_110 | ~spl5_133 | ~spl5_146),
% 2.19/0.66    inference(avatar_contradiction_clause,[],[f3363])).
% 2.19/0.66  fof(f3363,plain,(
% 2.19/0.66    $false | (~spl5_9 | spl5_22 | ~spl5_110 | ~spl5_133 | ~spl5_146)),
% 2.19/0.66    inference(subsumption_resolution,[],[f181,f3362])).
% 2.19/0.66  fof(f3362,plain,(
% 2.19/0.66    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl5_9 | ~spl5_110 | ~spl5_133 | ~spl5_146)),
% 2.19/0.66    inference(forward_demodulation,[],[f3361,f2917])).
% 2.19/0.66  fof(f2917,plain,(
% 2.19/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl5_133),
% 2.19/0.66    inference(avatar_component_clause,[],[f2916])).
% 2.19/0.66  fof(f2916,plain,(
% 2.19/0.66    spl5_133 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).
% 2.19/0.66  fof(f3361,plain,(
% 2.19/0.66    k4_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) | (~spl5_9 | ~spl5_110 | ~spl5_146)),
% 2.19/0.66    inference(forward_demodulation,[],[f3349,f85])).
% 2.19/0.66  fof(f85,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl5_9),
% 2.19/0.66    inference(avatar_component_clause,[],[f84])).
% 2.19/0.66  fof(f84,plain,(
% 2.19/0.66    spl5_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.19/0.66  fof(f3349,plain,(
% 2.19/0.66    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) | (~spl5_110 | ~spl5_146)),
% 2.19/0.66    inference(superposition,[],[f2453,f3334])).
% 2.19/0.66  fof(f3334,plain,(
% 2.19/0.66    ( ! [X37,X35] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X37),X35)) ) | ~spl5_146),
% 2.19/0.66    inference(avatar_component_clause,[],[f3333])).
% 2.19/0.66  fof(f3333,plain,(
% 2.19/0.66    spl5_146 <=> ! [X35,X37] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X37),X35)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).
% 2.19/0.66  fof(f2453,plain,(
% 2.19/0.66    ( ! [X1] : (k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)) = k4_xboole_0(sK0,X1)) ) | ~spl5_110),
% 2.19/0.66    inference(avatar_component_clause,[],[f2452])).
% 2.19/0.66  fof(f2452,plain,(
% 2.19/0.66    spl5_110 <=> ! [X1] : k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)) = k4_xboole_0(sK0,X1)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 2.19/0.66  fof(f181,plain,(
% 2.19/0.66    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl5_22),
% 2.19/0.66    inference(avatar_component_clause,[],[f179])).
% 2.19/0.66  fof(f179,plain,(
% 2.19/0.66    spl5_22 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.19/0.66  fof(f3335,plain,(
% 2.19/0.66    spl5_146 | ~spl5_37 | ~spl5_59),
% 2.19/0.66    inference(avatar_split_clause,[],[f786,f768,f358,f3333])).
% 2.19/0.66  fof(f358,plain,(
% 2.19/0.66    spl5_37 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.19/0.66  fof(f768,plain,(
% 2.19/0.66    spl5_59 <=> ! [X9,X11,X10] : k3_xboole_0(X9,k4_xboole_0(k2_xboole_0(X9,X10),X11)) = k4_xboole_0(X9,X11)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 2.19/0.66  fof(f786,plain,(
% 2.19/0.66    ( ! [X37,X35] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X37),X35)) ) | (~spl5_37 | ~spl5_59)),
% 2.19/0.66    inference(superposition,[],[f359,f769])).
% 2.19/0.66  fof(f769,plain,(
% 2.19/0.66    ( ! [X10,X11,X9] : (k3_xboole_0(X9,k4_xboole_0(k2_xboole_0(X9,X10),X11)) = k4_xboole_0(X9,X11)) ) | ~spl5_59),
% 2.19/0.66    inference(avatar_component_clause,[],[f768])).
% 2.19/0.66  fof(f359,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) ) | ~spl5_37),
% 2.19/0.66    inference(avatar_component_clause,[],[f358])).
% 2.19/0.66  fof(f2918,plain,(
% 2.19/0.66    spl5_133 | ~spl5_32 | ~spl5_33 | ~spl5_38),
% 2.19/0.66    inference(avatar_split_clause,[],[f404,f374,f314,f309,f2916])).
% 2.19/0.66  fof(f309,plain,(
% 2.19/0.66    spl5_32 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.19/0.66  fof(f314,plain,(
% 2.19/0.66    spl5_33 <=> ! [X1] : r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 2.19/0.66  fof(f374,plain,(
% 2.19/0.66    spl5_38 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.19/0.66  fof(f404,plain,(
% 2.19/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl5_32 | ~spl5_33 | ~spl5_38)),
% 2.19/0.66    inference(forward_demodulation,[],[f379,f380])).
% 2.19/0.66  fof(f380,plain,(
% 2.19/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl5_32 | ~spl5_38)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f310,f375])).
% 2.19/0.66  fof(f375,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl5_38),
% 2.19/0.66    inference(avatar_component_clause,[],[f374])).
% 2.19/0.66  fof(f310,plain,(
% 2.19/0.66    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl5_32),
% 2.19/0.66    inference(avatar_component_clause,[],[f309])).
% 2.19/0.66  fof(f379,plain,(
% 2.19/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) ) | (~spl5_33 | ~spl5_38)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f315,f375])).
% 2.19/0.66  fof(f315,plain,(
% 2.19/0.66    ( ! [X1] : (r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) ) | ~spl5_33),
% 2.19/0.66    inference(avatar_component_clause,[],[f314])).
% 2.19/0.66  fof(f2454,plain,(
% 2.19/0.66    spl5_110 | ~spl5_20 | ~spl5_25),
% 2.19/0.66    inference(avatar_split_clause,[],[f251,f236,f171,f2452])).
% 2.19/0.66  fof(f171,plain,(
% 2.19/0.66    spl5_20 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.19/0.66  fof(f236,plain,(
% 2.19/0.66    spl5_25 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.19/0.66  fof(f251,plain,(
% 2.19/0.66    ( ! [X1] : (k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)) = k4_xboole_0(sK0,X1)) ) | (~spl5_20 | ~spl5_25)),
% 2.19/0.66    inference(superposition,[],[f172,f238])).
% 2.19/0.66  fof(f238,plain,(
% 2.19/0.66    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl5_25),
% 2.19/0.66    inference(avatar_component_clause,[],[f236])).
% 2.19/0.66  fof(f172,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl5_20),
% 2.19/0.66    inference(avatar_component_clause,[],[f171])).
% 2.19/0.66  fof(f2148,plain,(
% 2.19/0.66    ~spl5_4 | ~spl5_5 | ~spl5_21 | ~spl5_36 | spl5_44 | ~spl5_60 | ~spl5_102),
% 2.19/0.66    inference(avatar_contradiction_clause,[],[f2147])).
% 2.19/0.66  fof(f2147,plain,(
% 2.19/0.66    $false | (~spl5_4 | ~spl5_5 | ~spl5_21 | ~spl5_36 | spl5_44 | ~spl5_60 | ~spl5_102)),
% 2.19/0.66    inference(subsumption_resolution,[],[f501,f2146])).
% 2.19/0.66  fof(f2146,plain,(
% 2.19/0.66    r1_xboole_0(sK2,sK0) | (~spl5_4 | ~spl5_5 | ~spl5_21 | ~spl5_36 | ~spl5_60 | ~spl5_102)),
% 2.19/0.66    inference(forward_demodulation,[],[f2145,f69])).
% 2.19/0.66  fof(f69,plain,(
% 2.19/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_5),
% 2.19/0.66    inference(avatar_component_clause,[],[f68])).
% 2.19/0.66  fof(f68,plain,(
% 2.19/0.66    spl5_5 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.19/0.66  fof(f2145,plain,(
% 2.19/0.66    r1_xboole_0(sK2,k5_xboole_0(sK0,k1_xboole_0)) | (~spl5_4 | ~spl5_21 | ~spl5_36 | ~spl5_60 | ~spl5_102)),
% 2.19/0.66    inference(forward_demodulation,[],[f2144,f65])).
% 2.19/0.66  fof(f65,plain,(
% 2.19/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl5_4),
% 2.19/0.66    inference(avatar_component_clause,[],[f64])).
% 2.19/0.66  fof(f64,plain,(
% 2.19/0.66    spl5_4 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.19/0.66  fof(f2144,plain,(
% 2.19/0.66    r1_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK2,sK2))) | (~spl5_21 | ~spl5_36 | ~spl5_60 | ~spl5_102)),
% 2.19/0.66    inference(forward_demodulation,[],[f2137,f814])).
% 2.19/0.66  fof(f814,plain,(
% 2.19/0.66    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | (~spl5_21 | ~spl5_60)),
% 2.19/0.66    inference(superposition,[],[f800,f176])).
% 2.19/0.66  fof(f176,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl5_21),
% 2.19/0.66    inference(avatar_component_clause,[],[f175])).
% 2.19/0.66  fof(f175,plain,(
% 2.19/0.66    spl5_21 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.19/0.66  fof(f800,plain,(
% 2.19/0.66    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)) ) | ~spl5_60),
% 2.19/0.66    inference(avatar_component_clause,[],[f799])).
% 2.19/0.66  fof(f799,plain,(
% 2.19/0.66    spl5_60 <=> ! [X3,X2,X4] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 2.19/0.66  fof(f2137,plain,(
% 2.19/0.66    r1_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK0,sK2))) | (~spl5_36 | ~spl5_102)),
% 2.19/0.66    inference(superposition,[],[f351,f2130])).
% 2.19/0.66  fof(f2130,plain,(
% 2.19/0.66    k5_xboole_0(sK0,sK2) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl5_102),
% 2.19/0.66    inference(avatar_component_clause,[],[f2128])).
% 2.19/0.66  fof(f2128,plain,(
% 2.19/0.66    spl5_102 <=> k5_xboole_0(sK0,sK2) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 2.19/0.66  fof(f351,plain,(
% 2.19/0.66    ( ! [X4,X5] : (r1_xboole_0(X4,k5_xboole_0(X4,k2_xboole_0(X4,X5)))) ) | ~spl5_36),
% 2.19/0.66    inference(avatar_component_clause,[],[f350])).
% 2.19/0.66  fof(f350,plain,(
% 2.19/0.66    spl5_36 <=> ! [X5,X4] : r1_xboole_0(X4,k5_xboole_0(X4,k2_xboole_0(X4,X5)))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.19/0.66  fof(f501,plain,(
% 2.19/0.66    ~r1_xboole_0(sK2,sK0) | spl5_44),
% 2.19/0.66    inference(avatar_component_clause,[],[f499])).
% 2.19/0.66  fof(f499,plain,(
% 2.19/0.66    spl5_44 <=> r1_xboole_0(sK2,sK0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 2.19/0.66  fof(f2131,plain,(
% 2.19/0.66    spl5_102 | ~spl5_8 | ~spl5_25 | ~spl5_68),
% 2.19/0.66    inference(avatar_split_clause,[],[f1282,f1231,f236,f80,f2128])).
% 2.19/0.66  fof(f80,plain,(
% 2.19/0.66    spl5_8 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.19/0.66  fof(f1231,plain,(
% 2.19/0.66    spl5_68 <=> ! [X1,X0,X2] : k2_xboole_0(X2,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 2.19/0.66  fof(f1282,plain,(
% 2.19/0.66    k5_xboole_0(sK0,sK2) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | (~spl5_8 | ~spl5_25 | ~spl5_68)),
% 2.19/0.66    inference(forward_demodulation,[],[f1248,f81])).
% 2.19/0.66  fof(f81,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl5_8),
% 2.19/0.66    inference(avatar_component_clause,[],[f80])).
% 2.19/0.66  fof(f1248,plain,(
% 2.19/0.66    k5_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | (~spl5_25 | ~spl5_68)),
% 2.19/0.66    inference(superposition,[],[f1232,f238])).
% 2.19/0.66  fof(f1232,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | ~spl5_68),
% 2.19/0.66    inference(avatar_component_clause,[],[f1231])).
% 2.19/0.66  fof(f1233,plain,(
% 2.19/0.66    spl5_68 | ~spl5_16 | ~spl5_20),
% 2.19/0.66    inference(avatar_split_clause,[],[f194,f171,f126,f1231])).
% 2.19/0.66  fof(f126,plain,(
% 2.19/0.66    spl5_16 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.19/0.66  fof(f194,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | (~spl5_16 | ~spl5_20)),
% 2.19/0.66    inference(superposition,[],[f127,f172])).
% 2.19/0.66  fof(f127,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl5_16),
% 2.19/0.66    inference(avatar_component_clause,[],[f126])).
% 2.19/0.66  fof(f801,plain,(
% 2.19/0.66    spl5_60 | ~spl5_8 | ~spl5_21),
% 2.19/0.66    inference(avatar_split_clause,[],[f198,f175,f80,f799])).
% 2.19/0.66  fof(f198,plain,(
% 2.19/0.66    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)) ) | (~spl5_8 | ~spl5_21)),
% 2.19/0.66    inference(superposition,[],[f176,f81])).
% 2.19/0.66  fof(f770,plain,(
% 2.19/0.66    spl5_59 | ~spl5_10 | ~spl5_20),
% 2.19/0.66    inference(avatar_split_clause,[],[f192,f171,f88,f768])).
% 2.19/0.66  fof(f88,plain,(
% 2.19/0.66    spl5_10 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.19/0.66  fof(f192,plain,(
% 2.19/0.66    ( ! [X10,X11,X9] : (k3_xboole_0(X9,k4_xboole_0(k2_xboole_0(X9,X10),X11)) = k4_xboole_0(X9,X11)) ) | (~spl5_10 | ~spl5_20)),
% 2.19/0.66    inference(superposition,[],[f172,f89])).
% 2.19/0.66  fof(f89,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl5_10),
% 2.19/0.66    inference(avatar_component_clause,[],[f88])).
% 2.19/0.66  fof(f502,plain,(
% 2.19/0.66    ~spl5_44 | ~spl5_28 | ~spl5_39),
% 2.19/0.66    inference(avatar_split_clause,[],[f422,f410,f265,f499])).
% 2.19/0.66  fof(f265,plain,(
% 2.19/0.66    spl5_28 <=> r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.19/0.66  fof(f410,plain,(
% 2.19/0.66    spl5_39 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.19/0.66  fof(f422,plain,(
% 2.19/0.66    ~r1_xboole_0(sK2,sK0) | (~spl5_28 | ~spl5_39)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f267,f411])).
% 2.19/0.66  fof(f411,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_39),
% 2.19/0.66    inference(avatar_component_clause,[],[f410])).
% 2.19/0.66  fof(f267,plain,(
% 2.19/0.66    r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) | ~spl5_28),
% 2.19/0.66    inference(avatar_component_clause,[],[f265])).
% 2.19/0.66  fof(f412,plain,(
% 2.19/0.66    spl5_39 | ~spl5_9 | ~spl5_12),
% 2.19/0.66    inference(avatar_split_clause,[],[f135,f96,f84,f410])).
% 2.19/0.66  fof(f96,plain,(
% 2.19/0.66    spl5_12 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.19/0.66  fof(f135,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) ) | (~spl5_9 | ~spl5_12)),
% 2.19/0.66    inference(superposition,[],[f97,f85])).
% 2.19/0.66  fof(f97,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_12),
% 2.19/0.66    inference(avatar_component_clause,[],[f96])).
% 2.19/0.66  fof(f376,plain,(
% 2.19/0.66    spl5_38 | ~spl5_7 | ~spl5_12),
% 2.19/0.66    inference(avatar_split_clause,[],[f134,f96,f76,f374])).
% 2.19/0.66  fof(f76,plain,(
% 2.19/0.66    spl5_7 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.19/0.66  fof(f134,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | (~spl5_7 | ~spl5_12)),
% 2.19/0.66    inference(resolution,[],[f97,f77])).
% 2.19/0.66  fof(f77,plain,(
% 2.19/0.66    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_7),
% 2.19/0.66    inference(avatar_component_clause,[],[f76])).
% 2.19/0.66  fof(f360,plain,(
% 2.19/0.66    spl5_37 | ~spl5_6 | ~spl5_15),
% 2.19/0.66    inference(avatar_split_clause,[],[f153,f108,f72,f358])).
% 2.19/0.66  fof(f72,plain,(
% 2.19/0.66    spl5_6 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.19/0.66  fof(f108,plain,(
% 2.19/0.66    spl5_15 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.19/0.66  fof(f153,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) ) | (~spl5_6 | ~spl5_15)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f73,f109])).
% 2.19/0.66  fof(f109,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) ) | ~spl5_15),
% 2.19/0.66    inference(avatar_component_clause,[],[f108])).
% 2.19/0.66  fof(f73,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl5_6),
% 2.19/0.66    inference(avatar_component_clause,[],[f72])).
% 2.19/0.66  fof(f352,plain,(
% 2.19/0.66    spl5_36 | ~spl5_10 | ~spl5_11),
% 2.19/0.66    inference(avatar_split_clause,[],[f120,f92,f88,f350])).
% 2.19/0.66  fof(f92,plain,(
% 2.19/0.66    spl5_11 <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.19/0.66  fof(f120,plain,(
% 2.19/0.66    ( ! [X4,X5] : (r1_xboole_0(X4,k5_xboole_0(X4,k2_xboole_0(X4,X5)))) ) | (~spl5_10 | ~spl5_11)),
% 2.19/0.66    inference(superposition,[],[f93,f89])).
% 2.19/0.66  fof(f93,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl5_11),
% 2.19/0.66    inference(avatar_component_clause,[],[f92])).
% 2.19/0.66  fof(f316,plain,(
% 2.19/0.66    spl5_33 | ~spl5_5 | ~spl5_11),
% 2.19/0.66    inference(avatar_split_clause,[],[f122,f92,f68,f314])).
% 2.19/0.66  fof(f122,plain,(
% 2.19/0.66    ( ! [X1] : (r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) ) | (~spl5_5 | ~spl5_11)),
% 2.19/0.66    inference(superposition,[],[f93,f69])).
% 2.19/0.66  fof(f311,plain,(
% 2.19/0.66    spl5_32 | ~spl5_13 | ~spl5_18 | ~spl5_31),
% 2.19/0.66    inference(avatar_split_clause,[],[f307,f304,f139,f100,f309])).
% 2.19/0.66  fof(f100,plain,(
% 2.19/0.66    spl5_13 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.19/0.66  fof(f139,plain,(
% 2.19/0.66    spl5_18 <=> ! [X4] : r1_tarski(X4,X4)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.19/0.66  fof(f304,plain,(
% 2.19/0.66    spl5_31 <=> ! [X0] : r1_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.19/0.66  fof(f307,plain,(
% 2.19/0.66    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl5_13 | ~spl5_18 | ~spl5_31)),
% 2.19/0.66    inference(forward_demodulation,[],[f305,f273])).
% 2.19/0.66  fof(f273,plain,(
% 2.19/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | (~spl5_13 | ~spl5_18)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f140,f101])).
% 2.19/0.66  fof(f101,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl5_13),
% 2.19/0.66    inference(avatar_component_clause,[],[f100])).
% 2.19/0.66  fof(f140,plain,(
% 2.19/0.66    ( ! [X4] : (r1_tarski(X4,X4)) ) | ~spl5_18),
% 2.19/0.66    inference(avatar_component_clause,[],[f139])).
% 2.19/0.66  fof(f305,plain,(
% 2.19/0.66    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) ) | ~spl5_31),
% 2.19/0.66    inference(avatar_component_clause,[],[f304])).
% 2.19/0.66  fof(f306,plain,(
% 2.19/0.66    spl5_31 | ~spl5_4 | ~spl5_11),
% 2.19/0.66    inference(avatar_split_clause,[],[f121,f92,f64,f304])).
% 2.19/0.66  fof(f121,plain,(
% 2.19/0.66    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) ) | (~spl5_4 | ~spl5_11)),
% 2.19/0.66    inference(superposition,[],[f93,f65])).
% 2.19/0.66  fof(f268,plain,(
% 2.19/0.66    spl5_28 | spl5_3 | ~spl5_19),
% 2.19/0.66    inference(avatar_split_clause,[],[f183,f157,f59,f265])).
% 2.19/0.66  fof(f59,plain,(
% 2.19/0.66    spl5_3 <=> r1_xboole_0(sK0,sK2)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.19/0.66  fof(f157,plain,(
% 2.19/0.66    spl5_19 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.19/0.66  fof(f183,plain,(
% 2.19/0.66    r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) | (spl5_3 | ~spl5_19)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f61,f158])).
% 2.19/0.66  fof(f158,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl5_19),
% 2.19/0.66    inference(avatar_component_clause,[],[f157])).
% 2.19/0.66  fof(f61,plain,(
% 2.19/0.66    ~r1_xboole_0(sK0,sK2) | spl5_3),
% 2.19/0.66    inference(avatar_component_clause,[],[f59])).
% 2.19/0.66  fof(f239,plain,(
% 2.19/0.66    spl5_25 | ~spl5_1 | ~spl5_13),
% 2.19/0.66    inference(avatar_split_clause,[],[f142,f100,f50,f236])).
% 2.19/0.66  fof(f50,plain,(
% 2.19/0.66    spl5_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.19/0.66  fof(f142,plain,(
% 2.19/0.66    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl5_1 | ~spl5_13)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f52,f101])).
% 2.19/0.66  fof(f52,plain,(
% 2.19/0.66    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl5_1),
% 2.19/0.66    inference(avatar_component_clause,[],[f50])).
% 2.19/0.66  fof(f182,plain,(
% 2.19/0.66    ~spl5_22 | spl5_2 | ~spl5_14),
% 2.19/0.66    inference(avatar_split_clause,[],[f151,f104,f55,f179])).
% 2.19/0.66  fof(f55,plain,(
% 2.19/0.66    spl5_2 <=> r1_tarski(sK0,sK1)),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.19/0.66  fof(f104,plain,(
% 2.19/0.66    spl5_14 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 2.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.19/0.66  fof(f151,plain,(
% 2.19/0.66    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl5_2 | ~spl5_14)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f57,f105])).
% 2.19/0.66  fof(f105,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) ) | ~spl5_14),
% 2.19/0.66    inference(avatar_component_clause,[],[f104])).
% 2.19/0.66  fof(f57,plain,(
% 2.19/0.66    ~r1_tarski(sK0,sK1) | spl5_2),
% 2.19/0.66    inference(avatar_component_clause,[],[f55])).
% 2.19/0.66  fof(f177,plain,(
% 2.19/0.66    spl5_21),
% 2.19/0.66    inference(avatar_split_clause,[],[f48,f175])).
% 2.19/0.66  fof(f48,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f13])).
% 2.19/0.66  fof(f13,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.19/0.66  fof(f173,plain,(
% 2.19/0.66    spl5_20),
% 2.19/0.66    inference(avatar_split_clause,[],[f47,f171])).
% 2.19/0.66  fof(f47,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f11])).
% 2.19/0.66  fof(f11,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.19/0.66  fof(f159,plain,(
% 2.19/0.66    spl5_19),
% 2.19/0.66    inference(avatar_split_clause,[],[f42,f157])).
% 2.19/0.66  fof(f42,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f28])).
% 2.19/0.66  fof(f28,plain,(
% 2.19/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.19/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).
% 2.19/0.66  fof(f27,plain,(
% 2.19/0.66    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.19/0.66    introduced(choice_axiom,[])).
% 2.19/0.66  fof(f21,plain,(
% 2.19/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.19/0.66    inference(ennf_transformation,[],[f18])).
% 2.19/0.66  fof(f18,plain,(
% 2.19/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.66    inference(rectify,[],[f3])).
% 2.19/0.66  fof(f3,axiom,(
% 2.19/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.19/0.66  fof(f141,plain,(
% 2.19/0.66    spl5_18 | ~spl5_6 | ~spl5_10),
% 2.19/0.66    inference(avatar_split_clause,[],[f117,f88,f72,f139])).
% 2.19/0.66  fof(f117,plain,(
% 2.19/0.66    ( ! [X4] : (r1_tarski(X4,X4)) ) | (~spl5_6 | ~spl5_10)),
% 2.19/0.66    inference(superposition,[],[f73,f89])).
% 2.19/0.66  fof(f128,plain,(
% 2.19/0.66    spl5_16),
% 2.19/0.66    inference(avatar_split_clause,[],[f40,f126])).
% 2.19/0.66  fof(f40,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f15])).
% 2.19/0.66  fof(f15,axiom,(
% 2.19/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.19/0.66  fof(f110,plain,(
% 2.19/0.66    spl5_15),
% 2.19/0.66    inference(avatar_split_clause,[],[f46,f108])).
% 2.19/0.66  fof(f46,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f29])).
% 2.19/0.66  fof(f29,plain,(
% 2.19/0.66    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.19/0.66    inference(nnf_transformation,[],[f5])).
% 2.19/0.66  fof(f5,axiom,(
% 2.19/0.66    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.19/0.66  fof(f106,plain,(
% 2.19/0.66    spl5_14),
% 2.19/0.66    inference(avatar_split_clause,[],[f45,f104])).
% 2.19/0.66  fof(f45,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f29])).
% 2.19/0.66  fof(f102,plain,(
% 2.19/0.66    spl5_13),
% 2.19/0.66    inference(avatar_split_clause,[],[f44,f100])).
% 2.19/0.66  fof(f44,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f22])).
% 2.19/0.66  fof(f22,plain,(
% 2.19/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.19/0.66    inference(ennf_transformation,[],[f10])).
% 2.19/0.66  fof(f10,axiom,(
% 2.19/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.19/0.66  fof(f98,plain,(
% 2.19/0.66    spl5_12),
% 2.19/0.66    inference(avatar_split_clause,[],[f43,f96])).
% 2.19/0.66  fof(f43,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f28])).
% 2.19/0.66  fof(f94,plain,(
% 2.19/0.66    spl5_11),
% 2.19/0.66    inference(avatar_split_clause,[],[f39,f92])).
% 2.19/0.66  fof(f39,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f6])).
% 2.19/0.66  fof(f6,axiom,(
% 2.19/0.66    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 2.19/0.66  fof(f90,plain,(
% 2.19/0.66    spl5_10),
% 2.19/0.66    inference(avatar_split_clause,[],[f38,f88])).
% 2.19/0.66  fof(f38,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.19/0.66    inference(cnf_transformation,[],[f9])).
% 2.19/0.66  fof(f9,axiom,(
% 2.19/0.66    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.19/0.66  fof(f86,plain,(
% 2.19/0.66    spl5_9),
% 2.19/0.66    inference(avatar_split_clause,[],[f37,f84])).
% 2.19/0.66  fof(f37,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f1])).
% 2.19/0.66  fof(f1,axiom,(
% 2.19/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.19/0.66  fof(f82,plain,(
% 2.19/0.66    spl5_8),
% 2.19/0.66    inference(avatar_split_clause,[],[f36,f80])).
% 2.19/0.66  fof(f36,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f2])).
% 2.19/0.66  fof(f2,axiom,(
% 2.19/0.66    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.19/0.66  fof(f78,plain,(
% 2.19/0.66    spl5_7),
% 2.19/0.66    inference(avatar_split_clause,[],[f34,f76])).
% 2.19/0.66  fof(f34,plain,(
% 2.19/0.66    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.19/0.66    inference(cnf_transformation,[],[f26])).
% 2.19/0.66  fof(f26,plain,(
% 2.19/0.66    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.19/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f25])).
% 2.19/0.66  fof(f25,plain,(
% 2.19/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.19/0.66    introduced(choice_axiom,[])).
% 2.19/0.66  fof(f20,plain,(
% 2.19/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.19/0.66    inference(ennf_transformation,[],[f4])).
% 2.19/0.66  fof(f4,axiom,(
% 2.19/0.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.19/0.66  fof(f74,plain,(
% 2.19/0.66    spl5_6),
% 2.19/0.66    inference(avatar_split_clause,[],[f35,f72])).
% 2.19/0.66  fof(f35,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f8])).
% 2.19/0.66  fof(f8,axiom,(
% 2.19/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.19/0.66  fof(f70,plain,(
% 2.19/0.66    spl5_5),
% 2.19/0.66    inference(avatar_split_clause,[],[f33,f68])).
% 2.19/0.66  fof(f33,plain,(
% 2.19/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.66    inference(cnf_transformation,[],[f12])).
% 2.19/0.66  fof(f12,axiom,(
% 2.19/0.66    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.19/0.66  fof(f66,plain,(
% 2.19/0.66    spl5_4),
% 2.19/0.66    inference(avatar_split_clause,[],[f32,f64])).
% 2.19/0.66  fof(f32,plain,(
% 2.19/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f14])).
% 2.19/0.66  fof(f14,axiom,(
% 2.19/0.66    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.19/0.66  fof(f62,plain,(
% 2.19/0.66    ~spl5_2 | ~spl5_3),
% 2.19/0.66    inference(avatar_split_clause,[],[f31,f59,f55])).
% 2.19/0.66  fof(f31,plain,(
% 2.19/0.66    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 2.19/0.66    inference(cnf_transformation,[],[f24])).
% 2.19/0.66  fof(f24,plain,(
% 2.19/0.66    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.19/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).
% 2.19/0.66  fof(f23,plain,(
% 2.19/0.66    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 2.19/0.66    introduced(choice_axiom,[])).
% 2.19/0.66  fof(f19,plain,(
% 2.19/0.66    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.19/0.66    inference(ennf_transformation,[],[f17])).
% 2.19/0.66  fof(f17,negated_conjecture,(
% 2.19/0.66    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.19/0.66    inference(negated_conjecture,[],[f16])).
% 2.19/0.66  fof(f16,conjecture,(
% 2.19/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.19/0.66  fof(f53,plain,(
% 2.19/0.66    spl5_1),
% 2.19/0.66    inference(avatar_split_clause,[],[f30,f50])).
% 2.19/0.66  fof(f30,plain,(
% 2.19/0.66    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.19/0.66    inference(cnf_transformation,[],[f24])).
% 2.19/0.66  % SZS output end Proof for theBenchmark
% 2.19/0.66  % (17733)------------------------------
% 2.19/0.66  % (17733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (17733)Termination reason: Refutation
% 2.19/0.66  
% 2.19/0.66  % (17733)Memory used [KB]: 8827
% 2.19/0.66  % (17733)Time elapsed: 0.236 s
% 2.19/0.66  % (17733)------------------------------
% 2.19/0.66  % (17733)------------------------------
% 2.19/0.66  % (17725)Success in time 0.296 s
%------------------------------------------------------------------------------
