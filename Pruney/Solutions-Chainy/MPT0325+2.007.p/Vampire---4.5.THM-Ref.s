%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:38 EST 2020

% Result     : Theorem 29.56s
% Output     : Refutation 29.56s
% Verified   : 
% Statistics : Number of formulae       :  248 ( 433 expanded)
%              Number of leaves         :   68 ( 211 expanded)
%              Depth                    :    7
%              Number of atoms          :  601 (1030 expanded)
%              Number of equality atoms :  192 ( 398 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23496,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f80,f84,f88,f92,f96,f100,f104,f113,f117,f121,f134,f144,f148,f155,f163,f179,f232,f253,f261,f363,f399,f411,f488,f526,f575,f615,f704,f1672,f2815,f3349,f6155,f8577,f8694,f8909,f9020,f9096,f9203,f9437,f9693,f9845,f9881,f18295,f18436,f22921,f23306,f23437])).

fof(f23437,plain,
    ( spl6_3
    | ~ spl6_17
    | ~ spl6_334 ),
    inference(avatar_contradiction_clause,[],[f23436])).

fof(f23436,plain,
    ( $false
    | spl6_3
    | ~ spl6_17
    | ~ spl6_334 ),
    inference(subsumption_resolution,[],[f23329,f75])).

fof(f75,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f23329,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_17
    | ~ spl6_334 ),
    inference(superposition,[],[f143,f23305])).

fof(f23305,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl6_334 ),
    inference(avatar_component_clause,[],[f23304])).

fof(f23304,plain,
    ( spl6_334
  <=> sK1 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_334])])).

fof(f143,plain,
    ( ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_17
  <=> ! [X1,X2] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f23306,plain,
    ( spl6_334
    | ~ spl6_6
    | ~ spl6_54
    | ~ spl6_326 ),
    inference(avatar_split_clause,[],[f23294,f22919,f702,f86,f23304])).

fof(f86,plain,
    ( spl6_6
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f702,plain,
    ( spl6_54
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f22919,plain,
    ( spl6_326
  <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_326])])).

fof(f23294,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl6_6
    | ~ spl6_54
    | ~ spl6_326 ),
    inference(forward_demodulation,[],[f23280,f87])).

fof(f87,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f23280,plain,
    ( k3_xboole_0(sK1,sK3) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl6_54
    | ~ spl6_326 ),
    inference(superposition,[],[f703,f22920])).

fof(f22920,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl6_326 ),
    inference(avatar_component_clause,[],[f22919])).

fof(f703,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f702])).

fof(f22921,plain,
    ( spl6_326
    | ~ spl6_29
    | ~ spl6_189
    | spl6_208 ),
    inference(avatar_split_clause,[],[f18992,f9879,f8907,f230,f22919])).

fof(f230,plain,
    ( spl6_29
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f8907,plain,
    ( spl6_189
  <=> k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_189])])).

fof(f9879,plain,
    ( spl6_208
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_208])])).

fof(f18992,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | ~ spl6_29
    | ~ spl6_189
    | spl6_208 ),
    inference(unit_resulting_resolution,[],[f8908,f9880,f231])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f230])).

fof(f9880,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl6_208 ),
    inference(avatar_component_clause,[],[f9879])).

fof(f8908,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl6_189 ),
    inference(avatar_component_clause,[],[f8907])).

fof(f18436,plain,
    ( spl6_1
    | ~ spl6_10
    | ~ spl6_212 ),
    inference(avatar_contradiction_clause,[],[f18435])).

fof(f18435,plain,
    ( $false
    | spl6_1
    | ~ spl6_10
    | ~ spl6_212 ),
    inference(subsumption_resolution,[],[f18305,f103])).

fof(f103,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_10
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f18305,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl6_1
    | ~ spl6_212 ),
    inference(superposition,[],[f68,f18294])).

fof(f18294,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_212 ),
    inference(avatar_component_clause,[],[f10204])).

fof(f10204,plain,
    ( spl6_212
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_212])])).

fof(f68,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f18295,plain,
    ( spl6_212
    | ~ spl6_12
    | ~ spl6_203 ),
    inference(avatar_split_clause,[],[f18252,f9843,f111,f10204])).

fof(f111,plain,
    ( spl6_12
  <=> ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f9843,plain,
    ( spl6_203
  <=> ! [X5] : ~ r2_hidden(X5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_203])])).

fof(f18252,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_12
    | ~ spl6_203 ),
    inference(unit_resulting_resolution,[],[f9844,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f9844,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK0)
    | ~ spl6_203 ),
    inference(avatar_component_clause,[],[f9843])).

fof(f9881,plain,
    ( ~ spl6_208
    | ~ spl6_21
    | spl6_202 ),
    inference(avatar_split_clause,[],[f9850,f9840,f161,f9879])).

fof(f161,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f9840,plain,
    ( spl6_202
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_202])])).

fof(f9850,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | ~ spl6_21
    | spl6_202 ),
    inference(unit_resulting_resolution,[],[f9841,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f9841,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl6_202 ),
    inference(avatar_component_clause,[],[f9840])).

fof(f9845,plain,
    ( ~ spl6_202
    | spl6_203
    | ~ spl6_18
    | ~ spl6_198 ),
    inference(avatar_split_clause,[],[f9514,f9435,f146,f9843,f9840])).

fof(f146,plain,
    ( spl6_18
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f9435,plain,
    ( spl6_198
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_198])])).

fof(f9514,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK0)
        | ~ r1_xboole_0(sK0,sK2) )
    | ~ spl6_18
    | ~ spl6_198 ),
    inference(superposition,[],[f147,f9436])).

fof(f9436,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_198 ),
    inference(avatar_component_clause,[],[f9435])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f9693,plain,
    ( spl6_2
    | ~ spl6_17
    | ~ spl6_198 ),
    inference(avatar_split_clause,[],[f9513,f9435,f142,f71])).

fof(f71,plain,
    ( spl6_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f9513,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_17
    | ~ spl6_198 ),
    inference(superposition,[],[f143,f9436])).

fof(f9437,plain,
    ( spl6_198
    | ~ spl6_6
    | ~ spl6_54
    | ~ spl6_196 ),
    inference(avatar_split_clause,[],[f9428,f9094,f702,f86,f9435])).

fof(f9094,plain,
    ( spl6_196
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_196])])).

fof(f9428,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_6
    | ~ spl6_54
    | ~ spl6_196 ),
    inference(forward_demodulation,[],[f9418,f87])).

fof(f9418,plain,
    ( k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_54
    | ~ spl6_196 ),
    inference(superposition,[],[f703,f9095])).

fof(f9095,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl6_196 ),
    inference(avatar_component_clause,[],[f9094])).

fof(f9203,plain,
    ( spl6_1
    | ~ spl6_9
    | ~ spl6_195 ),
    inference(avatar_contradiction_clause,[],[f9202])).

fof(f9202,plain,
    ( $false
    | spl6_1
    | ~ spl6_9
    | ~ spl6_195 ),
    inference(subsumption_resolution,[],[f9098,f99])).

fof(f99,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_9
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f9098,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl6_1
    | ~ spl6_195 ),
    inference(superposition,[],[f68,f9092])).

fof(f9092,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_195 ),
    inference(avatar_component_clause,[],[f9091])).

fof(f9091,plain,
    ( spl6_195
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_195])])).

fof(f9096,plain,
    ( spl6_195
    | spl6_196
    | ~ spl6_29
    | ~ spl6_193 ),
    inference(avatar_split_clause,[],[f9044,f9018,f230,f9094,f9091])).

fof(f9018,plain,
    ( spl6_193
  <=> k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_193])])).

fof(f9044,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1
    | ~ spl6_29
    | ~ spl6_193 ),
    inference(trivial_inequality_removal,[],[f9025])).

fof(f9025,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1
    | ~ spl6_29
    | ~ spl6_193 ),
    inference(superposition,[],[f231,f9019])).

fof(f9019,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl6_193 ),
    inference(avatar_component_clause,[],[f9018])).

fof(f9020,plain,
    ( spl6_193
    | ~ spl6_183
    | ~ spl6_189 ),
    inference(avatar_split_clause,[],[f8919,f8907,f8575,f9018])).

fof(f8575,plain,
    ( spl6_183
  <=> k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_183])])).

fof(f8919,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl6_183
    | ~ spl6_189 ),
    inference(superposition,[],[f8908,f8576])).

fof(f8576,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl6_183 ),
    inference(avatar_component_clause,[],[f8575])).

fof(f8909,plain,
    ( spl6_189
    | ~ spl6_7
    | ~ spl6_187 ),
    inference(avatar_split_clause,[],[f8750,f8692,f90,f8907])).

fof(f90,plain,
    ( spl6_7
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f8692,plain,
    ( spl6_187
  <=> ! [X7] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_187])])).

fof(f8750,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl6_7
    | ~ spl6_187 ),
    inference(superposition,[],[f8693,f91])).

fof(f91,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f8693,plain,
    ( ! [X7] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)),X7))
    | ~ spl6_187 ),
    inference(avatar_component_clause,[],[f8692])).

fof(f8694,plain,
    ( spl6_187
    | ~ spl6_10
    | ~ spl6_92
    | ~ spl6_104
    | ~ spl6_114
    | ~ spl6_183 ),
    inference(avatar_split_clause,[],[f8671,f8575,f3347,f2813,f1670,f102,f8692])).

fof(f1670,plain,
    ( spl6_92
  <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f2813,plain,
    ( spl6_104
  <=> ! [X1,X0,X2] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f3347,plain,
    ( spl6_114
  <=> ! [X3,X5,X4,X6] : k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f8671,plain,
    ( ! [X7] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)),X7))
    | ~ spl6_10
    | ~ spl6_92
    | ~ spl6_104
    | ~ spl6_114
    | ~ spl6_183 ),
    inference(forward_demodulation,[],[f8650,f3447])).

fof(f3447,plain,
    ( ! [X47,X48,X46,X49] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X46,k3_xboole_0(X46,X47)),X48),k2_zfmisc_1(k3_xboole_0(X46,X47),X49))
    | ~ spl6_10
    | ~ spl6_92
    | ~ spl6_114 ),
    inference(forward_demodulation,[],[f3393,f103])).

fof(f3393,plain,
    ( ! [X47,X48,X46,X49] : k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X46,k3_xboole_0(X46,X47)),X48),k2_zfmisc_1(k3_xboole_0(X46,X47),X49)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X48,X49))
    | ~ spl6_92
    | ~ spl6_114 ),
    inference(superposition,[],[f3348,f1671])).

fof(f1671,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f1670])).

fof(f3348,plain,
    ( ! [X6,X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6))
    | ~ spl6_114 ),
    inference(avatar_component_clause,[],[f3347])).

fof(f8650,plain,
    ( ! [X7] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)),X7)) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7))
    | ~ spl6_104
    | ~ spl6_183 ),
    inference(superposition,[],[f2814,f8576])).

fof(f2814,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f2813])).

fof(f8577,plain,
    ( spl6_183
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_158 ),
    inference(avatar_split_clause,[],[f6851,f6153,f613,f177,f115,f8575])).

fof(f115,plain,
    ( spl6_13
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f177,plain,
    ( spl6_22
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f613,plain,
    ( spl6_52
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f6153,plain,
    ( spl6_158
  <=> ! [X3,X5,X2,X4] : k2_zfmisc_1(k3_xboole_0(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X2,X3),X4),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_158])])).

fof(f6851,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_158 ),
    inference(forward_demodulation,[],[f6850,f614])).

fof(f614,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f613])).

fof(f6850,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1))
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_158 ),
    inference(forward_demodulation,[],[f6729,f116])).

fof(f116,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f6729,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_22
    | ~ spl6_158 ),
    inference(superposition,[],[f6154,f178])).

fof(f178,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f177])).

fof(f6154,plain,
    ( ! [X4,X2,X5,X3] : k2_zfmisc_1(k3_xboole_0(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X2,X3),X4),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5)))
    | ~ spl6_158 ),
    inference(avatar_component_clause,[],[f6153])).

fof(f6155,plain,
    ( spl6_158
    | ~ spl6_36
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f546,f524,f361,f6153])).

fof(f361,plain,
    ( spl6_36
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f524,plain,
    ( spl6_47
  <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f546,plain,
    ( ! [X4,X2,X5,X3] : k2_zfmisc_1(k3_xboole_0(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X2,X3),X4),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5)))
    | ~ spl6_36
    | ~ spl6_47 ),
    inference(superposition,[],[f525,f362])).

fof(f362,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f361])).

fof(f525,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f524])).

fof(f3349,plain,
    ( spl6_114
    | ~ spl6_14
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f373,f361,f119,f3347])).

fof(f119,plain,
    ( spl6_14
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f373,plain,
    ( ! [X6,X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6))
    | ~ spl6_14
    | ~ spl6_36 ),
    inference(superposition,[],[f362,f120])).

fof(f120,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f2815,plain,
    ( spl6_104
    | ~ spl6_7
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f372,f361,f90,f2813])).

fof(f372,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))
    | ~ spl6_7
    | ~ spl6_36 ),
    inference(superposition,[],[f362,f91])).

fof(f1672,plain,
    ( spl6_92
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f474,f409,f259,f119,f90,f82,f1670])).

fof(f82,plain,
    ( spl6_5
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f259,plain,
    ( spl6_32
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f409,plain,
    ( spl6_42
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f474,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f473,f83])).

fof(f83,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f473,plain,
    ( ! [X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl6_7
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f472,f314])).

fof(f314,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(superposition,[],[f260,f91])).

fof(f260,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f259])).

fof(f472,plain,
    ( ! [X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))
    | ~ spl6_7
    | ~ spl6_14
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f458,f120])).

fof(f458,plain,
    ( ! [X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1))
    | ~ spl6_7
    | ~ spl6_42 ),
    inference(superposition,[],[f410,f91])).

fof(f410,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f409])).

fof(f704,plain,
    ( spl6_54
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f303,f251,f132,f82,f702])).

fof(f132,plain,
    ( spl6_16
  <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f251,plain,
    ( spl6_31
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f303,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f289,f133])).

fof(f133,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f289,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl6_5
    | ~ spl6_31 ),
    inference(superposition,[],[f252,f83])).

fof(f252,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f251])).

fof(f615,plain,
    ( spl6_52
    | ~ spl6_7
    | ~ spl6_36
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f576,f573,f361,f90,f613])).

fof(f573,plain,
    ( spl6_50
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f576,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))
    | ~ spl6_7
    | ~ spl6_36
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f574,f377])).

fof(f377,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)
    | ~ spl6_7
    | ~ spl6_36 ),
    inference(superposition,[],[f362,f91])).

fof(f574,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f573])).

fof(f575,plain,(
    spl6_50 ),
    inference(avatar_split_clause,[],[f63,f573])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f58,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f526,plain,
    ( spl6_47
    | ~ spl6_7
    | ~ spl6_36
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f489,f486,f361,f90,f524])).

fof(f486,plain,
    ( spl6_45
  <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f489,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))
    | ~ spl6_7
    | ~ spl6_36
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f487,f372])).

fof(f487,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f486])).

fof(f488,plain,(
    spl6_45 ),
    inference(avatar_split_clause,[],[f62,f486])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f59,f46,f46])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f411,plain,
    ( spl6_42
    | ~ spl6_32
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f400,f397,f259,f409])).

fof(f397,plain,
    ( spl6_40
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f400,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))
    | ~ spl6_32
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f398,f260])).

fof(f398,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f397])).

fof(f399,plain,(
    spl6_40 ),
    inference(avatar_split_clause,[],[f61,f397])).

fof(f61,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f56,f46,f46])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f363,plain,(
    spl6_36 ),
    inference(avatar_split_clause,[],[f60,f361])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f261,plain,(
    spl6_32 ),
    inference(avatar_split_clause,[],[f57,f259])).

fof(f57,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f253,plain,(
    spl6_31 ),
    inference(avatar_split_clause,[],[f55,f251])).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f232,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f52,f230])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f179,plain,
    ( spl6_22
    | ~ spl6_4
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f168,f153,f78,f177])).

fof(f78,plain,
    ( spl6_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f153,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f168,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_4
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f79,f154])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f79,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f163,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f51,f161])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f155,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f49,f153])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f148,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f48,f146])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f144,plain,
    ( spl6_17
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f135,f119,f94,f142])).

fof(f94,plain,
    ( spl6_8
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f135,plain,
    ( ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1)
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(superposition,[],[f95,f120])).

fof(f95,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f134,plain,
    ( spl6_16
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f127,f115,f86,f132])).

fof(f127,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(superposition,[],[f116,f87])).

fof(f121,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f45,f119])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f117,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f44,f115])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f113,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f41,f111])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f104,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f65,f102])).

fof(f65,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f64,f98])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f92,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f42,f90])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f88,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f84,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f80,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f76,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f38,f74,f71])).

fof(f38,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f67])).

fof(f37,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (32682)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (32690)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (32693)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (32680)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (32710)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  % (32695)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (32707)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (32683)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (32687)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (32698)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.59  % (32703)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (32692)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (32704)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (32703)Refutation not found, incomplete strategy% (32703)------------------------------
% 0.21/0.59  % (32703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (32703)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (32703)Memory used [KB]: 10746
% 0.21/0.59  % (32703)Time elapsed: 0.182 s
% 0.21/0.59  % (32703)------------------------------
% 0.21/0.59  % (32703)------------------------------
% 1.94/0.61  % (32684)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.94/0.62  % (32709)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.94/0.62  % (32681)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.94/0.62  % (32697)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.94/0.63  % (32702)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.94/0.63  % (32706)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.94/0.63  % (32688)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.94/0.63  % (32697)Refutation not found, incomplete strategy% (32697)------------------------------
% 1.94/0.63  % (32697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.63  % (32697)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.63  
% 1.94/0.63  % (32697)Memory used [KB]: 10618
% 1.94/0.63  % (32697)Time elapsed: 0.140 s
% 1.94/0.63  % (32697)------------------------------
% 1.94/0.63  % (32697)------------------------------
% 2.13/0.63  % (32694)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.13/0.64  % (32700)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.13/0.64  % (32708)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.13/0.64  % (32679)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.13/0.65  % (32678)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.21/0.65  % (32691)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.21/0.67  % (32705)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.21/0.68  % (32699)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.21/0.69  % (32696)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.21/0.69  % (32686)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 3.03/0.82  % (32724)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.68/0.85  % (32683)Time limit reached!
% 3.68/0.85  % (32683)------------------------------
% 3.68/0.85  % (32683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.87  % (32683)Termination reason: Time limit
% 3.68/0.87  % (32683)Termination phase: Saturation
% 3.68/0.87  
% 3.68/0.87  % (32683)Memory used [KB]: 9083
% 3.68/0.87  % (32683)Time elapsed: 0.400 s
% 3.68/0.87  % (32683)------------------------------
% 3.68/0.87  % (32683)------------------------------
% 3.68/0.88  % (32725)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.91/0.93  % (32690)Time limit reached!
% 3.91/0.93  % (32690)------------------------------
% 3.91/0.93  % (32690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.93  % (32690)Termination reason: Time limit
% 3.91/0.93  
% 3.91/0.93  % (32690)Memory used [KB]: 15479
% 3.91/0.93  % (32690)Time elapsed: 0.522 s
% 3.91/0.93  % (32690)------------------------------
% 3.91/0.93  % (32690)------------------------------
% 4.17/0.94  % (32678)Time limit reached!
% 4.17/0.94  % (32678)------------------------------
% 4.17/0.94  % (32678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.94  % (32678)Termination reason: Time limit
% 4.17/0.94  
% 4.17/0.94  % (32678)Memory used [KB]: 2686
% 4.17/0.94  % (32678)Time elapsed: 0.504 s
% 4.17/0.94  % (32678)------------------------------
% 4.17/0.94  % (32678)------------------------------
% 4.41/0.96  % (32692)Time limit reached!
% 4.41/0.96  % (32692)------------------------------
% 4.41/0.96  % (32692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.96  % (32692)Termination reason: Time limit
% 4.41/0.96  % (32692)Termination phase: Saturation
% 4.41/0.96  
% 4.41/0.96  % (32692)Memory used [KB]: 9338
% 4.41/0.96  % (32692)Time elapsed: 0.500 s
% 4.41/0.96  % (32692)------------------------------
% 4.41/0.96  % (32692)------------------------------
% 4.41/1.01  % (32679)Time limit reached!
% 4.41/1.01  % (32679)------------------------------
% 4.41/1.01  % (32679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/1.01  % (32679)Termination reason: Time limit
% 4.41/1.01  
% 4.41/1.01  % (32679)Memory used [KB]: 7675
% 4.41/1.01  % (32679)Time elapsed: 0.520 s
% 4.41/1.01  % (32679)------------------------------
% 4.41/1.01  % (32679)------------------------------
% 4.84/1.03  % (32726)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.84/1.04  % (32709)Time limit reached!
% 4.84/1.04  % (32709)------------------------------
% 4.84/1.04  % (32709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.04  % (32709)Termination reason: Time limit
% 4.84/1.04  
% 4.84/1.04  % (32709)Memory used [KB]: 7547
% 4.84/1.04  % (32709)Time elapsed: 0.609 s
% 4.84/1.04  % (32709)------------------------------
% 4.84/1.04  % (32709)------------------------------
% 4.84/1.04  % (32696)Time limit reached!
% 4.84/1.04  % (32696)------------------------------
% 4.84/1.04  % (32696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.04  % (32696)Termination reason: Time limit
% 4.84/1.04  % (32696)Termination phase: Saturation
% 4.84/1.04  
% 4.84/1.04  % (32696)Memory used [KB]: 12920
% 4.84/1.04  % (32696)Time elapsed: 0.613 s
% 4.84/1.04  % (32696)------------------------------
% 4.84/1.04  % (32696)------------------------------
% 4.84/1.05  % (32686)Time limit reached!
% 4.84/1.05  % (32686)------------------------------
% 4.84/1.05  % (32686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.05  % (32686)Termination reason: Time limit
% 4.84/1.05  
% 4.84/1.05  % (32686)Memory used [KB]: 8315
% 4.84/1.05  % (32686)Time elapsed: 0.614 s
% 4.84/1.05  % (32686)------------------------------
% 4.84/1.05  % (32686)------------------------------
% 5.15/1.14  % (32729)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.15/1.14  % (32728)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.15/1.15  % (32727)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 6.69/1.25  % (32730)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.69/1.25  % (32732)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.69/1.26  % (32731)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 7.09/1.27  % (32733)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.09/1.27  % (32702)Time limit reached!
% 7.09/1.27  % (32702)------------------------------
% 7.09/1.27  % (32702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.09/1.27  % (32702)Termination reason: Time limit
% 7.09/1.27  % (32702)Termination phase: Saturation
% 7.09/1.27  
% 7.09/1.27  % (32702)Memory used [KB]: 6396
% 7.09/1.27  % (32702)Time elapsed: 0.800 s
% 7.09/1.27  % (32702)------------------------------
% 7.09/1.27  % (32702)------------------------------
% 7.95/1.39  % (32728)Time limit reached!
% 7.95/1.39  % (32728)------------------------------
% 7.95/1.39  % (32728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.39  % (32728)Termination reason: Time limit
% 7.95/1.39  
% 7.95/1.39  % (32728)Memory used [KB]: 12281
% 7.95/1.39  % (32728)Time elapsed: 0.403 s
% 7.95/1.39  % (32728)------------------------------
% 7.95/1.39  % (32728)------------------------------
% 7.95/1.40  % (32727)Time limit reached!
% 7.95/1.40  % (32727)------------------------------
% 7.95/1.40  % (32727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.40  % (32727)Termination reason: Time limit
% 7.95/1.40  % (32727)Termination phase: Saturation
% 7.95/1.40  
% 7.95/1.40  % (32727)Memory used [KB]: 6268
% 7.95/1.40  % (32727)Time elapsed: 0.400 s
% 7.95/1.40  % (32727)------------------------------
% 7.95/1.40  % (32727)------------------------------
% 7.95/1.43  % (32680)Time limit reached!
% 7.95/1.43  % (32680)------------------------------
% 7.95/1.43  % (32680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.43  % (32680)Termination reason: Time limit
% 7.95/1.43  
% 7.95/1.43  % (32680)Memory used [KB]: 15351
% 7.95/1.43  % (32680)Time elapsed: 1.020 s
% 7.95/1.43  % (32680)------------------------------
% 7.95/1.43  % (32680)------------------------------
% 8.49/1.48  % (32734)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 9.33/1.61  % (32735)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.33/1.62  % (32736)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.33/1.64  % (32707)Time limit reached!
% 9.33/1.64  % (32707)------------------------------
% 9.33/1.64  % (32707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.33/1.65  % (32737)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.89/1.66  % (32707)Termination reason: Time limit
% 9.89/1.66  
% 9.89/1.66  % (32707)Memory used [KB]: 17782
% 9.89/1.66  % (32707)Time elapsed: 1.227 s
% 9.89/1.66  % (32707)------------------------------
% 9.89/1.66  % (32707)------------------------------
% 10.11/1.74  % (32705)Time limit reached!
% 10.11/1.74  % (32705)------------------------------
% 10.11/1.74  % (32705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.11/1.74  % (32705)Termination reason: Time limit
% 10.11/1.74  
% 10.11/1.74  % (32705)Memory used [KB]: 14328
% 10.11/1.74  % (32705)Time elapsed: 1.306 s
% 10.11/1.74  % (32705)------------------------------
% 10.11/1.74  % (32705)------------------------------
% 11.16/1.78  % (32695)Time limit reached!
% 11.16/1.78  % (32695)------------------------------
% 11.16/1.78  % (32695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.16/1.78  % (32695)Termination reason: Time limit
% 11.16/1.78  
% 11.16/1.78  % (32695)Memory used [KB]: 14072
% 11.16/1.78  % (32695)Time elapsed: 1.329 s
% 11.16/1.78  % (32695)------------------------------
% 11.16/1.78  % (32695)------------------------------
% 11.83/1.88  % (32738)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 12.43/1.96  % (32739)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 12.43/1.96  % (32708)Time limit reached!
% 12.43/1.96  % (32708)------------------------------
% 12.43/1.96  % (32708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.43/1.96  % (32708)Termination reason: Time limit
% 12.43/1.96  
% 12.43/1.96  % (32708)Memory used [KB]: 14583
% 12.43/1.96  % (32708)Time elapsed: 1.509 s
% 12.43/1.96  % (32708)------------------------------
% 12.43/1.96  % (32708)------------------------------
% 12.43/1.98  % (32682)Time limit reached!
% 12.43/1.98  % (32682)------------------------------
% 12.43/1.98  % (32682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.43/1.98  % (32682)Termination reason: Time limit
% 12.43/1.98  
% 12.43/1.98  % (32682)Memory used [KB]: 16375
% 12.43/1.98  % (32682)Time elapsed: 1.512 s
% 12.43/1.98  % (32682)------------------------------
% 12.43/1.98  % (32682)------------------------------
% 12.43/1.98  % (32736)Time limit reached!
% 12.43/1.98  % (32736)------------------------------
% 12.43/1.98  % (32736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.43/1.98  % (32736)Termination reason: Time limit
% 12.43/1.98  
% 12.43/1.98  % (32736)Memory used [KB]: 2686
% 12.43/1.98  % (32736)Time elapsed: 0.528 s
% 12.43/1.98  % (32736)------------------------------
% 12.43/1.98  % (32736)------------------------------
% 12.43/2.00  % (32740)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 13.02/2.06  % (32691)Time limit reached!
% 13.02/2.06  % (32691)------------------------------
% 13.02/2.06  % (32691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.02/2.06  % (32691)Termination reason: Time limit
% 13.02/2.06  % (32691)Termination phase: Saturation
% 13.02/2.06  
% 13.02/2.06  % (32691)Memory used [KB]: 20340
% 13.02/2.06  % (32691)Time elapsed: 1.600 s
% 13.02/2.06  % (32691)------------------------------
% 13.02/2.06  % (32691)------------------------------
% 13.32/2.13  % (32741)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.92/2.18  % (32742)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.92/2.19  % (32743)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 14.28/2.25  % (32740)Time limit reached!
% 14.28/2.25  % (32740)------------------------------
% 14.28/2.25  % (32740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.28/2.25  % (32740)Termination reason: Time limit
% 14.28/2.25  % (32740)Termination phase: Saturation
% 14.28/2.25  
% 14.28/2.25  % (32740)Memory used [KB]: 3582
% 14.28/2.25  % (32740)Time elapsed: 0.400 s
% 14.28/2.25  % (32740)------------------------------
% 14.28/2.25  % (32740)------------------------------
% 14.28/2.27  % (32744)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.28/2.28  % (32694)Time limit reached!
% 14.28/2.28  % (32694)------------------------------
% 14.28/2.28  % (32694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.28/2.28  % (32694)Termination reason: Time limit
% 14.28/2.28  % (32694)Termination phase: Saturation
% 14.28/2.28  
% 14.28/2.28  % (32694)Memory used [KB]: 5245
% 14.28/2.28  % (32694)Time elapsed: 1.800 s
% 14.28/2.28  % (32694)------------------------------
% 14.28/2.28  % (32694)------------------------------
% 15.16/2.31  % (32730)Time limit reached!
% 15.16/2.31  % (32730)------------------------------
% 15.16/2.31  % (32730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.16/2.31  % (32730)Termination reason: Time limit
% 15.16/2.31  
% 15.16/2.31  % (32730)Memory used [KB]: 8059
% 15.16/2.31  % (32730)Time elapsed: 1.229 s
% 15.16/2.31  % (32730)------------------------------
% 15.16/2.31  % (32730)------------------------------
% 16.10/2.43  % (32743)Time limit reached!
% 16.10/2.43  % (32743)------------------------------
% 16.10/2.43  % (32743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.10/2.43  % (32743)Termination reason: Time limit
% 16.10/2.43  
% 16.10/2.43  % (32743)Memory used [KB]: 1663
% 16.10/2.43  % (32743)Time elapsed: 0.403 s
% 16.10/2.43  % (32743)------------------------------
% 16.10/2.43  % (32743)------------------------------
% 16.10/2.43  % (32745)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 16.10/2.44  % (32684)Time limit reached!
% 16.10/2.44  % (32684)------------------------------
% 16.10/2.44  % (32684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.10/2.44  % (32684)Termination reason: Time limit
% 16.10/2.44  
% 16.10/2.44  % (32684)Memory used [KB]: 18421
% 16.10/2.44  % (32684)Time elapsed: 2.006 s
% 16.10/2.44  % (32684)------------------------------
% 16.10/2.44  % (32684)------------------------------
% 16.43/2.49  % (32698)Time limit reached!
% 16.43/2.49  % (32698)------------------------------
% 16.43/2.49  % (32698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.43/2.49  % (32698)Termination reason: Time limit
% 16.43/2.49  
% 16.43/2.49  % (32698)Memory used [KB]: 18166
% 16.43/2.49  % (32698)Time elapsed: 2.067 s
% 16.43/2.49  % (32698)------------------------------
% 16.43/2.49  % (32698)------------------------------
% 16.43/2.49  % (32746)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 16.43/2.53  % (32747)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 17.85/2.67  % (32748)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.85/2.67  % (32726)Time limit reached!
% 17.85/2.67  % (32726)------------------------------
% 17.85/2.67  % (32726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.85/2.67  % (32726)Termination reason: Time limit
% 17.85/2.67  
% 17.85/2.67  % (32726)Memory used [KB]: 15351
% 17.85/2.67  % (32726)Time elapsed: 1.704 s
% 17.85/2.67  % (32726)------------------------------
% 17.85/2.67  % (32726)------------------------------
% 17.85/2.68  % (32749)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 18.16/2.73  % (32750)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.43/2.79  % (32732)Time limit reached!
% 18.43/2.79  % (32732)------------------------------
% 18.43/2.79  % (32732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.43/2.79  % (32732)Termination reason: Time limit
% 18.43/2.79  % (32732)Termination phase: Saturation
% 18.43/2.79  
% 18.43/2.79  % (32732)Memory used [KB]: 14583
% 18.43/2.79  % (32732)Time elapsed: 1.700 s
% 18.43/2.79  % (32732)------------------------------
% 18.43/2.79  % (32732)------------------------------
% 19.07/2.88  % (32748)Time limit reached!
% 19.07/2.88  % (32748)------------------------------
% 19.07/2.88  % (32748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.07/2.88  % (32748)Termination reason: Time limit
% 19.07/2.88  
% 19.07/2.88  % (32748)Memory used [KB]: 8059
% 19.07/2.88  % (32748)Time elapsed: 0.403 s
% 19.07/2.88  % (32748)------------------------------
% 19.07/2.88  % (32748)------------------------------
% 19.07/2.90  % (32751)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 20.22/2.95  % (32687)Time limit reached!
% 20.22/2.95  % (32687)------------------------------
% 20.22/2.95  % (32687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.22/2.95  % (32687)Termination reason: Time limit
% 20.22/2.95  % (32687)Termination phase: Saturation
% 20.22/2.95  
% 20.22/2.95  % (32687)Memory used [KB]: 25713
% 20.22/2.95  % (32687)Time elapsed: 2.500 s
% 20.22/2.95  % (32687)------------------------------
% 20.22/2.95  % (32687)------------------------------
% 20.71/2.98  % (32750)Time limit reached!
% 20.71/2.98  % (32750)------------------------------
% 20.71/2.98  % (32750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.71/2.98  % (32750)Termination reason: Time limit
% 20.71/2.98  
% 20.71/2.98  % (32750)Memory used [KB]: 8187
% 20.71/2.98  % (32750)Time elapsed: 0.414 s
% 20.71/2.98  % (32750)------------------------------
% 20.71/2.98  % (32750)------------------------------
% 20.71/2.98  % (32739)Time limit reached!
% 20.71/2.98  % (32739)------------------------------
% 20.71/2.98  % (32739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.71/2.98  % (32739)Termination reason: Time limit
% 20.71/2.98  % (32739)Termination phase: Saturation
% 20.71/2.98  
% 20.71/2.98  % (32739)Memory used [KB]: 12281
% 20.71/2.98  % (32739)Time elapsed: 1.200 s
% 20.71/2.98  % (32739)------------------------------
% 20.71/2.98  % (32739)------------------------------
% 21.07/3.04  % (32699)Time limit reached!
% 21.07/3.04  % (32699)------------------------------
% 21.07/3.04  % (32699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.07/3.04  % (32699)Termination reason: Time limit
% 21.07/3.04  
% 21.07/3.04  % (32699)Memory used [KB]: 34541
% 21.07/3.04  % (32699)Time elapsed: 2.604 s
% 21.07/3.04  % (32699)------------------------------
% 21.07/3.04  % (32699)------------------------------
% 23.51/3.34  % (32742)Time limit reached!
% 23.51/3.34  % (32742)------------------------------
% 23.51/3.34  % (32742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.51/3.34  % (32742)Termination reason: Time limit
% 23.51/3.34  
% 23.51/3.34  % (32742)Memory used [KB]: 11897
% 23.51/3.34  % (32742)Time elapsed: 1.318 s
% 23.51/3.34  % (32742)------------------------------
% 23.51/3.34  % (32742)------------------------------
% 23.51/3.44  % (32693)Time limit reached!
% 23.51/3.44  % (32693)------------------------------
% 23.51/3.44  % (32693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.51/3.44  % (32693)Termination reason: Time limit
% 23.51/3.44  % (32693)Termination phase: Saturation
% 23.51/3.44  
% 23.51/3.44  % (32693)Memory used [KB]: 16375
% 23.51/3.44  % (32693)Time elapsed: 3.0000 s
% 23.51/3.44  % (32693)------------------------------
% 23.51/3.44  % (32693)------------------------------
% 24.42/3.51  % (32725)Time limit reached!
% 24.42/3.51  % (32725)------------------------------
% 24.42/3.51  % (32725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.42/3.51  % (32725)Termination reason: Time limit
% 24.42/3.51  % (32725)Termination phase: Saturation
% 24.42/3.51  
% 24.42/3.51  % (32725)Memory used [KB]: 13560
% 24.42/3.51  % (32725)Time elapsed: 2.824 s
% 24.42/3.51  % (32725)------------------------------
% 24.42/3.51  % (32725)------------------------------
% 29.56/4.12  % (32738)Refutation found. Thanks to Tanya!
% 29.56/4.12  % SZS status Theorem for theBenchmark
% 29.56/4.13  % SZS output start Proof for theBenchmark
% 29.56/4.13  fof(f23496,plain,(
% 29.56/4.13    $false),
% 29.56/4.13    inference(avatar_sat_refutation,[],[f69,f76,f80,f84,f88,f92,f96,f100,f104,f113,f117,f121,f134,f144,f148,f155,f163,f179,f232,f253,f261,f363,f399,f411,f488,f526,f575,f615,f704,f1672,f2815,f3349,f6155,f8577,f8694,f8909,f9020,f9096,f9203,f9437,f9693,f9845,f9881,f18295,f18436,f22921,f23306,f23437])).
% 29.56/4.13  fof(f23437,plain,(
% 29.56/4.13    spl6_3 | ~spl6_17 | ~spl6_334),
% 29.56/4.13    inference(avatar_contradiction_clause,[],[f23436])).
% 29.56/4.13  fof(f23436,plain,(
% 29.56/4.13    $false | (spl6_3 | ~spl6_17 | ~spl6_334)),
% 29.56/4.13    inference(subsumption_resolution,[],[f23329,f75])).
% 29.56/4.13  fof(f75,plain,(
% 29.56/4.13    ~r1_tarski(sK1,sK3) | spl6_3),
% 29.56/4.13    inference(avatar_component_clause,[],[f74])).
% 29.56/4.13  fof(f74,plain,(
% 29.56/4.13    spl6_3 <=> r1_tarski(sK1,sK3)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 29.56/4.13  fof(f23329,plain,(
% 29.56/4.13    r1_tarski(sK1,sK3) | (~spl6_17 | ~spl6_334)),
% 29.56/4.13    inference(superposition,[],[f143,f23305])).
% 29.56/4.13  fof(f23305,plain,(
% 29.56/4.13    sK1 = k3_xboole_0(sK1,sK3) | ~spl6_334),
% 29.56/4.13    inference(avatar_component_clause,[],[f23304])).
% 29.56/4.13  fof(f23304,plain,(
% 29.56/4.13    spl6_334 <=> sK1 = k3_xboole_0(sK1,sK3)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_334])])).
% 29.56/4.13  fof(f143,plain,(
% 29.56/4.13    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) ) | ~spl6_17),
% 29.56/4.13    inference(avatar_component_clause,[],[f142])).
% 29.56/4.13  fof(f142,plain,(
% 29.56/4.13    spl6_17 <=> ! [X1,X2] : r1_tarski(k3_xboole_0(X2,X1),X1)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 29.56/4.13  fof(f23306,plain,(
% 29.56/4.13    spl6_334 | ~spl6_6 | ~spl6_54 | ~spl6_326),
% 29.56/4.13    inference(avatar_split_clause,[],[f23294,f22919,f702,f86,f23304])).
% 29.56/4.13  fof(f86,plain,(
% 29.56/4.13    spl6_6 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 29.56/4.13  fof(f702,plain,(
% 29.56/4.13    spl6_54 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 29.56/4.13  fof(f22919,plain,(
% 29.56/4.13    spl6_326 <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_326])])).
% 29.56/4.13  fof(f23294,plain,(
% 29.56/4.13    sK1 = k3_xboole_0(sK1,sK3) | (~spl6_6 | ~spl6_54 | ~spl6_326)),
% 29.56/4.13    inference(forward_demodulation,[],[f23280,f87])).
% 29.56/4.13  fof(f87,plain,(
% 29.56/4.13    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl6_6),
% 29.56/4.13    inference(avatar_component_clause,[],[f86])).
% 29.56/4.13  fof(f23280,plain,(
% 29.56/4.13    k3_xboole_0(sK1,sK3) = k5_xboole_0(sK1,k1_xboole_0) | (~spl6_54 | ~spl6_326)),
% 29.56/4.13    inference(superposition,[],[f703,f22920])).
% 29.56/4.13  fof(f22920,plain,(
% 29.56/4.13    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | ~spl6_326),
% 29.56/4.13    inference(avatar_component_clause,[],[f22919])).
% 29.56/4.13  fof(f703,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl6_54),
% 29.56/4.13    inference(avatar_component_clause,[],[f702])).
% 29.56/4.13  fof(f22921,plain,(
% 29.56/4.13    spl6_326 | ~spl6_29 | ~spl6_189 | spl6_208),
% 29.56/4.13    inference(avatar_split_clause,[],[f18992,f9879,f8907,f230,f22919])).
% 29.56/4.13  fof(f230,plain,(
% 29.56/4.13    spl6_29 <=> ! [X1,X0] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 29.56/4.13  fof(f8907,plain,(
% 29.56/4.13    spl6_189 <=> k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_189])])).
% 29.56/4.13  fof(f9879,plain,(
% 29.56/4.13    spl6_208 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_208])])).
% 29.56/4.13  fof(f18992,plain,(
% 29.56/4.13    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | (~spl6_29 | ~spl6_189 | spl6_208)),
% 29.56/4.13    inference(unit_resulting_resolution,[],[f8908,f9880,f231])).
% 29.56/4.13  fof(f231,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) ) | ~spl6_29),
% 29.56/4.13    inference(avatar_component_clause,[],[f230])).
% 29.56/4.13  fof(f9880,plain,(
% 29.56/4.13    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl6_208),
% 29.56/4.13    inference(avatar_component_clause,[],[f9879])).
% 29.56/4.13  fof(f8908,plain,(
% 29.56/4.13    k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | ~spl6_189),
% 29.56/4.13    inference(avatar_component_clause,[],[f8907])).
% 29.56/4.13  fof(f18436,plain,(
% 29.56/4.13    spl6_1 | ~spl6_10 | ~spl6_212),
% 29.56/4.13    inference(avatar_contradiction_clause,[],[f18435])).
% 29.56/4.13  fof(f18435,plain,(
% 29.56/4.13    $false | (spl6_1 | ~spl6_10 | ~spl6_212)),
% 29.56/4.13    inference(subsumption_resolution,[],[f18305,f103])).
% 29.56/4.13  fof(f103,plain,(
% 29.56/4.13    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl6_10),
% 29.56/4.13    inference(avatar_component_clause,[],[f102])).
% 29.56/4.13  fof(f102,plain,(
% 29.56/4.13    spl6_10 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 29.56/4.13  fof(f18305,plain,(
% 29.56/4.13    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl6_1 | ~spl6_212)),
% 29.56/4.13    inference(superposition,[],[f68,f18294])).
% 29.56/4.13  fof(f18294,plain,(
% 29.56/4.13    k1_xboole_0 = sK0 | ~spl6_212),
% 29.56/4.13    inference(avatar_component_clause,[],[f10204])).
% 29.56/4.13  fof(f10204,plain,(
% 29.56/4.13    spl6_212 <=> k1_xboole_0 = sK0),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_212])])).
% 29.56/4.13  fof(f68,plain,(
% 29.56/4.13    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl6_1),
% 29.56/4.13    inference(avatar_component_clause,[],[f67])).
% 29.56/4.13  fof(f67,plain,(
% 29.56/4.13    spl6_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 29.56/4.13  fof(f18295,plain,(
% 29.56/4.13    spl6_212 | ~spl6_12 | ~spl6_203),
% 29.56/4.13    inference(avatar_split_clause,[],[f18252,f9843,f111,f10204])).
% 29.56/4.13  fof(f111,plain,(
% 29.56/4.13    spl6_12 <=> ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 29.56/4.13  fof(f9843,plain,(
% 29.56/4.13    spl6_203 <=> ! [X5] : ~r2_hidden(X5,sK0)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_203])])).
% 29.56/4.13  fof(f18252,plain,(
% 29.56/4.13    k1_xboole_0 = sK0 | (~spl6_12 | ~spl6_203)),
% 29.56/4.13    inference(unit_resulting_resolution,[],[f9844,f112])).
% 29.56/4.13  fof(f112,plain,(
% 29.56/4.13    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) ) | ~spl6_12),
% 29.56/4.13    inference(avatar_component_clause,[],[f111])).
% 29.56/4.13  fof(f9844,plain,(
% 29.56/4.13    ( ! [X5] : (~r2_hidden(X5,sK0)) ) | ~spl6_203),
% 29.56/4.13    inference(avatar_component_clause,[],[f9843])).
% 29.56/4.13  fof(f9881,plain,(
% 29.56/4.13    ~spl6_208 | ~spl6_21 | spl6_202),
% 29.56/4.13    inference(avatar_split_clause,[],[f9850,f9840,f161,f9879])).
% 29.56/4.13  fof(f161,plain,(
% 29.56/4.13    spl6_21 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 29.56/4.13  fof(f9840,plain,(
% 29.56/4.13    spl6_202 <=> r1_xboole_0(sK0,sK2)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_202])])).
% 29.56/4.13  fof(f9850,plain,(
% 29.56/4.13    k1_xboole_0 != k3_xboole_0(sK0,sK2) | (~spl6_21 | spl6_202)),
% 29.56/4.13    inference(unit_resulting_resolution,[],[f9841,f162])).
% 29.56/4.13  fof(f162,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl6_21),
% 29.56/4.13    inference(avatar_component_clause,[],[f161])).
% 29.56/4.13  fof(f9841,plain,(
% 29.56/4.13    ~r1_xboole_0(sK0,sK2) | spl6_202),
% 29.56/4.13    inference(avatar_component_clause,[],[f9840])).
% 29.56/4.13  fof(f9845,plain,(
% 29.56/4.13    ~spl6_202 | spl6_203 | ~spl6_18 | ~spl6_198),
% 29.56/4.13    inference(avatar_split_clause,[],[f9514,f9435,f146,f9843,f9840])).
% 29.56/4.13  fof(f146,plain,(
% 29.56/4.13    spl6_18 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 29.56/4.13  fof(f9435,plain,(
% 29.56/4.13    spl6_198 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_198])])).
% 29.56/4.13  fof(f9514,plain,(
% 29.56/4.13    ( ! [X5] : (~r2_hidden(X5,sK0) | ~r1_xboole_0(sK0,sK2)) ) | (~spl6_18 | ~spl6_198)),
% 29.56/4.13    inference(superposition,[],[f147,f9436])).
% 29.56/4.13  fof(f9436,plain,(
% 29.56/4.13    sK0 = k3_xboole_0(sK0,sK2) | ~spl6_198),
% 29.56/4.13    inference(avatar_component_clause,[],[f9435])).
% 29.56/4.13  fof(f147,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl6_18),
% 29.56/4.13    inference(avatar_component_clause,[],[f146])).
% 29.56/4.13  fof(f9693,plain,(
% 29.56/4.13    spl6_2 | ~spl6_17 | ~spl6_198),
% 29.56/4.13    inference(avatar_split_clause,[],[f9513,f9435,f142,f71])).
% 29.56/4.13  fof(f71,plain,(
% 29.56/4.13    spl6_2 <=> r1_tarski(sK0,sK2)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 29.56/4.13  fof(f9513,plain,(
% 29.56/4.13    r1_tarski(sK0,sK2) | (~spl6_17 | ~spl6_198)),
% 29.56/4.13    inference(superposition,[],[f143,f9436])).
% 29.56/4.13  fof(f9437,plain,(
% 29.56/4.13    spl6_198 | ~spl6_6 | ~spl6_54 | ~spl6_196),
% 29.56/4.13    inference(avatar_split_clause,[],[f9428,f9094,f702,f86,f9435])).
% 29.56/4.13  fof(f9094,plain,(
% 29.56/4.13    spl6_196 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_196])])).
% 29.56/4.13  fof(f9428,plain,(
% 29.56/4.13    sK0 = k3_xboole_0(sK0,sK2) | (~spl6_6 | ~spl6_54 | ~spl6_196)),
% 29.56/4.13    inference(forward_demodulation,[],[f9418,f87])).
% 29.56/4.13  fof(f9418,plain,(
% 29.56/4.13    k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k1_xboole_0) | (~spl6_54 | ~spl6_196)),
% 29.56/4.13    inference(superposition,[],[f703,f9095])).
% 29.56/4.13  fof(f9095,plain,(
% 29.56/4.13    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl6_196),
% 29.56/4.13    inference(avatar_component_clause,[],[f9094])).
% 29.56/4.13  fof(f9203,plain,(
% 29.56/4.13    spl6_1 | ~spl6_9 | ~spl6_195),
% 29.56/4.13    inference(avatar_contradiction_clause,[],[f9202])).
% 29.56/4.13  fof(f9202,plain,(
% 29.56/4.13    $false | (spl6_1 | ~spl6_9 | ~spl6_195)),
% 29.56/4.13    inference(subsumption_resolution,[],[f9098,f99])).
% 29.56/4.13  fof(f99,plain,(
% 29.56/4.13    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl6_9),
% 29.56/4.13    inference(avatar_component_clause,[],[f98])).
% 29.56/4.13  fof(f98,plain,(
% 29.56/4.13    spl6_9 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 29.56/4.13  fof(f9098,plain,(
% 29.56/4.13    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl6_1 | ~spl6_195)),
% 29.56/4.13    inference(superposition,[],[f68,f9092])).
% 29.56/4.13  fof(f9092,plain,(
% 29.56/4.13    k1_xboole_0 = sK1 | ~spl6_195),
% 29.56/4.13    inference(avatar_component_clause,[],[f9091])).
% 29.56/4.13  fof(f9091,plain,(
% 29.56/4.13    spl6_195 <=> k1_xboole_0 = sK1),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_195])])).
% 29.56/4.13  fof(f9096,plain,(
% 29.56/4.13    spl6_195 | spl6_196 | ~spl6_29 | ~spl6_193),
% 29.56/4.13    inference(avatar_split_clause,[],[f9044,f9018,f230,f9094,f9091])).
% 29.56/4.13  fof(f9018,plain,(
% 29.56/4.13    spl6_193 <=> k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_193])])).
% 29.56/4.13  fof(f9044,plain,(
% 29.56/4.13    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1 | (~spl6_29 | ~spl6_193)),
% 29.56/4.13    inference(trivial_inequality_removal,[],[f9025])).
% 29.56/4.13  fof(f9025,plain,(
% 29.56/4.13    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1 | (~spl6_29 | ~spl6_193)),
% 29.56/4.13    inference(superposition,[],[f231,f9019])).
% 29.56/4.13  fof(f9019,plain,(
% 29.56/4.13    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl6_193),
% 29.56/4.13    inference(avatar_component_clause,[],[f9018])).
% 29.56/4.13  fof(f9020,plain,(
% 29.56/4.13    spl6_193 | ~spl6_183 | ~spl6_189),
% 29.56/4.13    inference(avatar_split_clause,[],[f8919,f8907,f8575,f9018])).
% 29.56/4.13  fof(f8575,plain,(
% 29.56/4.13    spl6_183 <=> k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_183])])).
% 29.56/4.13  fof(f8919,plain,(
% 29.56/4.13    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | (~spl6_183 | ~spl6_189)),
% 29.56/4.13    inference(superposition,[],[f8908,f8576])).
% 29.56/4.13  fof(f8576,plain,(
% 29.56/4.13    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl6_183),
% 29.56/4.13    inference(avatar_component_clause,[],[f8575])).
% 29.56/4.13  fof(f8909,plain,(
% 29.56/4.13    spl6_189 | ~spl6_7 | ~spl6_187),
% 29.56/4.13    inference(avatar_split_clause,[],[f8750,f8692,f90,f8907])).
% 29.56/4.13  fof(f90,plain,(
% 29.56/4.13    spl6_7 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 29.56/4.13  fof(f8692,plain,(
% 29.56/4.13    spl6_187 <=> ! [X7] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)),X7))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_187])])).
% 29.56/4.13  fof(f8750,plain,(
% 29.56/4.13    k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | (~spl6_7 | ~spl6_187)),
% 29.56/4.13    inference(superposition,[],[f8693,f91])).
% 29.56/4.13  fof(f91,plain,(
% 29.56/4.13    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl6_7),
% 29.56/4.13    inference(avatar_component_clause,[],[f90])).
% 29.56/4.13  fof(f8693,plain,(
% 29.56/4.13    ( ! [X7] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)),X7))) ) | ~spl6_187),
% 29.56/4.13    inference(avatar_component_clause,[],[f8692])).
% 29.56/4.13  fof(f8694,plain,(
% 29.56/4.13    spl6_187 | ~spl6_10 | ~spl6_92 | ~spl6_104 | ~spl6_114 | ~spl6_183),
% 29.56/4.13    inference(avatar_split_clause,[],[f8671,f8575,f3347,f2813,f1670,f102,f8692])).
% 29.56/4.13  fof(f1670,plain,(
% 29.56/4.13    spl6_92 <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 29.56/4.13  fof(f2813,plain,(
% 29.56/4.13    spl6_104 <=> ! [X1,X0,X2] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).
% 29.56/4.13  fof(f3347,plain,(
% 29.56/4.13    spl6_114 <=> ! [X3,X5,X4,X6] : k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).
% 29.56/4.13  fof(f8671,plain,(
% 29.56/4.13    ( ! [X7] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)),X7))) ) | (~spl6_10 | ~spl6_92 | ~spl6_104 | ~spl6_114 | ~spl6_183)),
% 29.56/4.13    inference(forward_demodulation,[],[f8650,f3447])).
% 29.56/4.13  fof(f3447,plain,(
% 29.56/4.13    ( ! [X47,X48,X46,X49] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X46,k3_xboole_0(X46,X47)),X48),k2_zfmisc_1(k3_xboole_0(X46,X47),X49))) ) | (~spl6_10 | ~spl6_92 | ~spl6_114)),
% 29.56/4.13    inference(forward_demodulation,[],[f3393,f103])).
% 29.56/4.13  fof(f3393,plain,(
% 29.56/4.13    ( ! [X47,X48,X46,X49] : (k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X46,k3_xboole_0(X46,X47)),X48),k2_zfmisc_1(k3_xboole_0(X46,X47),X49)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X48,X49))) ) | (~spl6_92 | ~spl6_114)),
% 29.56/4.13    inference(superposition,[],[f3348,f1671])).
% 29.56/4.13  fof(f1671,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | ~spl6_92),
% 29.56/4.13    inference(avatar_component_clause,[],[f1670])).
% 29.56/4.13  fof(f3348,plain,(
% 29.56/4.13    ( ! [X6,X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6))) ) | ~spl6_114),
% 29.56/4.13    inference(avatar_component_clause,[],[f3347])).
% 29.56/4.13  fof(f8650,plain,(
% 29.56/4.13    ( ! [X7] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)),X7)) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X7))) ) | (~spl6_104 | ~spl6_183)),
% 29.56/4.13    inference(superposition,[],[f2814,f8576])).
% 29.56/4.13  fof(f2814,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) ) | ~spl6_104),
% 29.56/4.13    inference(avatar_component_clause,[],[f2813])).
% 29.56/4.13  fof(f8577,plain,(
% 29.56/4.13    spl6_183 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_158),
% 29.56/4.13    inference(avatar_split_clause,[],[f6851,f6153,f613,f177,f115,f8575])).
% 29.56/4.13  fof(f115,plain,(
% 29.56/4.13    spl6_13 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 29.56/4.13  fof(f177,plain,(
% 29.56/4.13    spl6_22 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 29.56/4.13  fof(f613,plain,(
% 29.56/4.13    spl6_52 <=> ! [X1,X0,X2] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 29.56/4.13  fof(f6153,plain,(
% 29.56/4.13    spl6_158 <=> ! [X3,X5,X2,X4] : k2_zfmisc_1(k3_xboole_0(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X2,X3),X4),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5)))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_158])])).
% 29.56/4.13  fof(f6851,plain,(
% 29.56/4.13    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | (~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_158)),
% 29.56/4.13    inference(forward_demodulation,[],[f6850,f614])).
% 29.56/4.13  fof(f614,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))) ) | ~spl6_52),
% 29.56/4.13    inference(avatar_component_clause,[],[f613])).
% 29.56/4.13  fof(f6850,plain,(
% 29.56/4.13    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)) | (~spl6_13 | ~spl6_22 | ~spl6_158)),
% 29.56/4.13    inference(forward_demodulation,[],[f6729,f116])).
% 29.56/4.13  fof(f116,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl6_13),
% 29.56/4.13    inference(avatar_component_clause,[],[f115])).
% 29.56/4.13  fof(f6729,plain,(
% 29.56/4.13    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) | (~spl6_22 | ~spl6_158)),
% 29.56/4.13    inference(superposition,[],[f6154,f178])).
% 29.56/4.13  fof(f178,plain,(
% 29.56/4.13    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_22),
% 29.56/4.13    inference(avatar_component_clause,[],[f177])).
% 29.56/4.13  fof(f6154,plain,(
% 29.56/4.13    ( ! [X4,X2,X5,X3] : (k2_zfmisc_1(k3_xboole_0(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X2,X3),X4),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5)))) ) | ~spl6_158),
% 29.56/4.13    inference(avatar_component_clause,[],[f6153])).
% 29.56/4.13  fof(f6155,plain,(
% 29.56/4.13    spl6_158 | ~spl6_36 | ~spl6_47),
% 29.56/4.13    inference(avatar_split_clause,[],[f546,f524,f361,f6153])).
% 29.56/4.13  fof(f361,plain,(
% 29.56/4.13    spl6_36 <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 29.56/4.13  fof(f524,plain,(
% 29.56/4.13    spl6_47 <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 29.56/4.13  fof(f546,plain,(
% 29.56/4.13    ( ! [X4,X2,X5,X3] : (k2_zfmisc_1(k3_xboole_0(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X2,X3),X4),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5)))) ) | (~spl6_36 | ~spl6_47)),
% 29.56/4.13    inference(superposition,[],[f525,f362])).
% 29.56/4.13  fof(f362,plain,(
% 29.56/4.13    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ) | ~spl6_36),
% 29.56/4.13    inference(avatar_component_clause,[],[f361])).
% 29.56/4.13  fof(f525,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))) ) | ~spl6_47),
% 29.56/4.13    inference(avatar_component_clause,[],[f524])).
% 29.56/4.13  fof(f3349,plain,(
% 29.56/4.13    spl6_114 | ~spl6_14 | ~spl6_36),
% 29.56/4.13    inference(avatar_split_clause,[],[f373,f361,f119,f3347])).
% 29.56/4.13  fof(f119,plain,(
% 29.56/4.13    spl6_14 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 29.56/4.13  fof(f373,plain,(
% 29.56/4.13    ( ! [X6,X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6))) ) | (~spl6_14 | ~spl6_36)),
% 29.56/4.13    inference(superposition,[],[f362,f120])).
% 29.56/4.13  fof(f120,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl6_14),
% 29.56/4.13    inference(avatar_component_clause,[],[f119])).
% 29.56/4.13  fof(f2815,plain,(
% 29.56/4.13    spl6_104 | ~spl6_7 | ~spl6_36),
% 29.56/4.13    inference(avatar_split_clause,[],[f372,f361,f90,f2813])).
% 29.56/4.13  fof(f372,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) ) | (~spl6_7 | ~spl6_36)),
% 29.56/4.13    inference(superposition,[],[f362,f91])).
% 29.56/4.13  fof(f1672,plain,(
% 29.56/4.13    spl6_92 | ~spl6_5 | ~spl6_7 | ~spl6_14 | ~spl6_32 | ~spl6_42),
% 29.56/4.13    inference(avatar_split_clause,[],[f474,f409,f259,f119,f90,f82,f1670])).
% 29.56/4.13  fof(f82,plain,(
% 29.56/4.13    spl6_5 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 29.56/4.13  fof(f259,plain,(
% 29.56/4.13    spl6_32 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 29.56/4.13  fof(f409,plain,(
% 29.56/4.13    spl6_42 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 29.56/4.13  fof(f474,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | (~spl6_5 | ~spl6_7 | ~spl6_14 | ~spl6_32 | ~spl6_42)),
% 29.56/4.13    inference(forward_demodulation,[],[f473,f83])).
% 29.56/4.13  fof(f83,plain,(
% 29.56/4.13    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl6_5),
% 29.56/4.13    inference(avatar_component_clause,[],[f82])).
% 29.56/4.13  fof(f473,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | (~spl6_7 | ~spl6_14 | ~spl6_32 | ~spl6_42)),
% 29.56/4.13    inference(forward_demodulation,[],[f472,f314])).
% 29.56/4.13  fof(f314,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl6_7 | ~spl6_32)),
% 29.56/4.13    inference(superposition,[],[f260,f91])).
% 29.56/4.13  fof(f260,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl6_32),
% 29.56/4.13    inference(avatar_component_clause,[],[f259])).
% 29.56/4.13  fof(f472,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) ) | (~spl6_7 | ~spl6_14 | ~spl6_42)),
% 29.56/4.13    inference(forward_demodulation,[],[f458,f120])).
% 29.56/4.13  fof(f458,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1))) ) | (~spl6_7 | ~spl6_42)),
% 29.56/4.13    inference(superposition,[],[f410,f91])).
% 29.56/4.13  fof(f410,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) ) | ~spl6_42),
% 29.56/4.13    inference(avatar_component_clause,[],[f409])).
% 29.56/4.13  fof(f704,plain,(
% 29.56/4.13    spl6_54 | ~spl6_5 | ~spl6_16 | ~spl6_31),
% 29.56/4.13    inference(avatar_split_clause,[],[f303,f251,f132,f82,f702])).
% 29.56/4.13  fof(f132,plain,(
% 29.56/4.13    spl6_16 <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 29.56/4.13  fof(f251,plain,(
% 29.56/4.13    spl6_31 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 29.56/4.13  fof(f303,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl6_5 | ~spl6_16 | ~spl6_31)),
% 29.56/4.13    inference(forward_demodulation,[],[f289,f133])).
% 29.56/4.13  fof(f133,plain,(
% 29.56/4.13    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl6_16),
% 29.56/4.13    inference(avatar_component_clause,[],[f132])).
% 29.56/4.13  fof(f289,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl6_5 | ~spl6_31)),
% 29.56/4.13    inference(superposition,[],[f252,f83])).
% 29.56/4.13  fof(f252,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl6_31),
% 29.56/4.13    inference(avatar_component_clause,[],[f251])).
% 29.56/4.13  fof(f615,plain,(
% 29.56/4.13    spl6_52 | ~spl6_7 | ~spl6_36 | ~spl6_50),
% 29.56/4.13    inference(avatar_split_clause,[],[f576,f573,f361,f90,f613])).
% 29.56/4.13  fof(f573,plain,(
% 29.56/4.13    spl6_50 <=> ! [X1,X0,X2] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 29.56/4.13  fof(f576,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))) ) | (~spl6_7 | ~spl6_36 | ~spl6_50)),
% 29.56/4.13    inference(forward_demodulation,[],[f574,f377])).
% 29.56/4.13  fof(f377,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) ) | (~spl6_7 | ~spl6_36)),
% 29.56/4.13    inference(superposition,[],[f362,f91])).
% 29.56/4.13  fof(f574,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ) | ~spl6_50),
% 29.56/4.13    inference(avatar_component_clause,[],[f573])).
% 29.56/4.13  fof(f575,plain,(
% 29.56/4.13    spl6_50),
% 29.56/4.13    inference(avatar_split_clause,[],[f63,f573])).
% 29.56/4.13  fof(f63,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 29.56/4.13    inference(definition_unfolding,[],[f58,f46,f46])).
% 29.56/4.13  fof(f46,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 29.56/4.13    inference(cnf_transformation,[],[f7])).
% 29.56/4.13  fof(f7,axiom,(
% 29.56/4.13    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 29.56/4.13  fof(f58,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 29.56/4.13    inference(cnf_transformation,[],[f17])).
% 29.56/4.13  fof(f17,axiom,(
% 29.56/4.13    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 29.56/4.13  fof(f526,plain,(
% 29.56/4.13    spl6_47 | ~spl6_7 | ~spl6_36 | ~spl6_45),
% 29.56/4.13    inference(avatar_split_clause,[],[f489,f486,f361,f90,f524])).
% 29.56/4.13  fof(f486,plain,(
% 29.56/4.13    spl6_45 <=> ! [X1,X0,X2] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 29.56/4.13  fof(f489,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))) ) | (~spl6_7 | ~spl6_36 | ~spl6_45)),
% 29.56/4.13    inference(forward_demodulation,[],[f487,f372])).
% 29.56/4.13  fof(f487,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ) | ~spl6_45),
% 29.56/4.13    inference(avatar_component_clause,[],[f486])).
% 29.56/4.13  fof(f488,plain,(
% 29.56/4.13    spl6_45),
% 29.56/4.13    inference(avatar_split_clause,[],[f62,f486])).
% 29.56/4.13  fof(f62,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 29.56/4.13    inference(definition_unfolding,[],[f59,f46,f46])).
% 29.56/4.13  fof(f59,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 29.56/4.13    inference(cnf_transformation,[],[f17])).
% 29.56/4.13  fof(f411,plain,(
% 29.56/4.13    spl6_42 | ~spl6_32 | ~spl6_40),
% 29.56/4.13    inference(avatar_split_clause,[],[f400,f397,f259,f409])).
% 29.56/4.13  fof(f397,plain,(
% 29.56/4.13    spl6_40 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 29.56/4.13  fof(f400,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) ) | (~spl6_32 | ~spl6_40)),
% 29.56/4.13    inference(forward_demodulation,[],[f398,f260])).
% 29.56/4.13  fof(f398,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) ) | ~spl6_40),
% 29.56/4.13    inference(avatar_component_clause,[],[f397])).
% 29.56/4.13  fof(f399,plain,(
% 29.56/4.13    spl6_40),
% 29.56/4.13    inference(avatar_split_clause,[],[f61,f397])).
% 29.56/4.13  fof(f61,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 29.56/4.13    inference(definition_unfolding,[],[f56,f46,f46])).
% 29.56/4.13  fof(f56,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 29.56/4.13    inference(cnf_transformation,[],[f11])).
% 29.56/4.13  fof(f11,axiom,(
% 29.56/4.13    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 29.56/4.13  fof(f363,plain,(
% 29.56/4.13    spl6_36),
% 29.56/4.13    inference(avatar_split_clause,[],[f60,f361])).
% 29.56/4.13  fof(f60,plain,(
% 29.56/4.13    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 29.56/4.13    inference(cnf_transformation,[],[f16])).
% 29.56/4.13  fof(f16,axiom,(
% 29.56/4.13    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 29.56/4.13  fof(f261,plain,(
% 29.56/4.13    spl6_32),
% 29.56/4.13    inference(avatar_split_clause,[],[f57,f259])).
% 29.56/4.13  fof(f57,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 29.56/4.13    inference(cnf_transformation,[],[f8])).
% 29.56/4.13  fof(f8,axiom,(
% 29.56/4.13    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 29.56/4.13  fof(f253,plain,(
% 29.56/4.13    spl6_31),
% 29.56/4.13    inference(avatar_split_clause,[],[f55,f251])).
% 29.56/4.13  fof(f55,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 29.56/4.13    inference(cnf_transformation,[],[f13])).
% 29.56/4.13  fof(f13,axiom,(
% 29.56/4.13    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 29.56/4.13  fof(f232,plain,(
% 29.56/4.13    spl6_29),
% 29.56/4.13    inference(avatar_split_clause,[],[f52,f230])).
% 29.56/4.13  fof(f52,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 29.56/4.13    inference(cnf_transformation,[],[f35])).
% 29.56/4.13  fof(f35,plain,(
% 29.56/4.13    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 29.56/4.13    inference(flattening,[],[f34])).
% 29.56/4.13  fof(f34,plain,(
% 29.56/4.13    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 29.56/4.13    inference(nnf_transformation,[],[f15])).
% 29.56/4.13  fof(f15,axiom,(
% 29.56/4.13    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 29.56/4.13  fof(f179,plain,(
% 29.56/4.13    spl6_22 | ~spl6_4 | ~spl6_19),
% 29.56/4.13    inference(avatar_split_clause,[],[f168,f153,f78,f177])).
% 29.56/4.13  fof(f78,plain,(
% 29.56/4.13    spl6_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 29.56/4.13  fof(f153,plain,(
% 29.56/4.13    spl6_19 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 29.56/4.13  fof(f168,plain,(
% 29.56/4.13    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | (~spl6_4 | ~spl6_19)),
% 29.56/4.13    inference(unit_resulting_resolution,[],[f79,f154])).
% 29.56/4.13  fof(f154,plain,(
% 29.56/4.13    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl6_19),
% 29.56/4.13    inference(avatar_component_clause,[],[f153])).
% 29.56/4.13  fof(f79,plain,(
% 29.56/4.13    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_4),
% 29.56/4.13    inference(avatar_component_clause,[],[f78])).
% 29.56/4.13  fof(f163,plain,(
% 29.56/4.13    spl6_21),
% 29.56/4.13    inference(avatar_split_clause,[],[f51,f161])).
% 29.56/4.13  fof(f51,plain,(
% 29.56/4.13    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 29.56/4.13    inference(cnf_transformation,[],[f33])).
% 29.56/4.13  fof(f33,plain,(
% 29.56/4.13    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 29.56/4.13    inference(nnf_transformation,[],[f3])).
% 29.56/4.13  fof(f3,axiom,(
% 29.56/4.13    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 29.56/4.13  fof(f155,plain,(
% 29.56/4.13    spl6_19),
% 29.56/4.13    inference(avatar_split_clause,[],[f49,f153])).
% 29.56/4.13  fof(f49,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 29.56/4.13    inference(cnf_transformation,[],[f26])).
% 29.56/4.13  fof(f26,plain,(
% 29.56/4.13    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 29.56/4.13    inference(ennf_transformation,[],[f10])).
% 29.56/4.13  fof(f10,axiom,(
% 29.56/4.13    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 29.56/4.13  fof(f148,plain,(
% 29.56/4.13    spl6_18),
% 29.56/4.13    inference(avatar_split_clause,[],[f48,f146])).
% 29.56/4.13  fof(f48,plain,(
% 29.56/4.13    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 29.56/4.13    inference(cnf_transformation,[],[f32])).
% 29.56/4.13  fof(f32,plain,(
% 29.56/4.13    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 29.56/4.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f31])).
% 29.56/4.13  fof(f31,plain,(
% 29.56/4.13    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 29.56/4.13    introduced(choice_axiom,[])).
% 29.56/4.13  fof(f25,plain,(
% 29.56/4.13    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 29.56/4.13    inference(ennf_transformation,[],[f21])).
% 29.56/4.13  fof(f21,plain,(
% 29.56/4.13    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 29.56/4.13    inference(rectify,[],[f5])).
% 29.56/4.13  fof(f5,axiom,(
% 29.56/4.13    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 29.56/4.13  fof(f144,plain,(
% 29.56/4.13    spl6_17 | ~spl6_8 | ~spl6_14),
% 29.56/4.13    inference(avatar_split_clause,[],[f135,f119,f94,f142])).
% 29.56/4.13  fof(f94,plain,(
% 29.56/4.13    spl6_8 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 29.56/4.13    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 29.56/4.13  fof(f135,plain,(
% 29.56/4.13    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) ) | (~spl6_8 | ~spl6_14)),
% 29.56/4.13    inference(superposition,[],[f95,f120])).
% 29.56/4.13  fof(f95,plain,(
% 29.56/4.13    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl6_8),
% 29.56/4.13    inference(avatar_component_clause,[],[f94])).
% 29.56/4.13  fof(f134,plain,(
% 29.56/4.13    spl6_16 | ~spl6_6 | ~spl6_13),
% 29.56/4.13    inference(avatar_split_clause,[],[f127,f115,f86,f132])).
% 29.56/4.13  fof(f127,plain,(
% 29.56/4.13    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl6_6 | ~spl6_13)),
% 29.56/4.13    inference(superposition,[],[f116,f87])).
% 29.56/4.13  fof(f121,plain,(
% 29.56/4.13    spl6_14),
% 29.56/4.13    inference(avatar_split_clause,[],[f45,f119])).
% 29.56/4.13  fof(f45,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 29.56/4.13    inference(cnf_transformation,[],[f1])).
% 29.56/4.13  fof(f1,axiom,(
% 29.56/4.13    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 29.56/4.13  fof(f117,plain,(
% 29.56/4.13    spl6_13),
% 29.56/4.13    inference(avatar_split_clause,[],[f44,f115])).
% 29.56/4.13  fof(f44,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 29.56/4.13    inference(cnf_transformation,[],[f2])).
% 29.56/4.13  fof(f2,axiom,(
% 29.56/4.13    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 29.56/4.13  fof(f113,plain,(
% 29.56/4.13    spl6_12),
% 29.56/4.13    inference(avatar_split_clause,[],[f41,f111])).
% 29.56/4.13  fof(f41,plain,(
% 29.56/4.13    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 29.56/4.13    inference(cnf_transformation,[],[f30])).
% 29.56/4.13  fof(f30,plain,(
% 29.56/4.13    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 29.56/4.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f29])).
% 29.56/4.13  fof(f29,plain,(
% 29.56/4.13    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 29.56/4.13    introduced(choice_axiom,[])).
% 29.56/4.13  fof(f24,plain,(
% 29.56/4.13    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 29.56/4.13    inference(ennf_transformation,[],[f6])).
% 29.56/4.13  fof(f6,axiom,(
% 29.56/4.13    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 29.56/4.13  fof(f104,plain,(
% 29.56/4.13    spl6_10),
% 29.56/4.13    inference(avatar_split_clause,[],[f65,f102])).
% 29.56/4.13  fof(f65,plain,(
% 29.56/4.13    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 29.56/4.13    inference(equality_resolution,[],[f53])).
% 29.56/4.13  fof(f53,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 29.56/4.13    inference(cnf_transformation,[],[f35])).
% 29.56/4.13  fof(f100,plain,(
% 29.56/4.13    spl6_9),
% 29.56/4.13    inference(avatar_split_clause,[],[f64,f98])).
% 29.56/4.13  fof(f64,plain,(
% 29.56/4.13    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 29.56/4.13    inference(equality_resolution,[],[f54])).
% 29.56/4.13  fof(f54,plain,(
% 29.56/4.13    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 29.56/4.13    inference(cnf_transformation,[],[f35])).
% 29.56/4.13  fof(f96,plain,(
% 29.56/4.13    spl6_8),
% 29.56/4.13    inference(avatar_split_clause,[],[f43,f94])).
% 29.56/4.13  fof(f43,plain,(
% 29.56/4.13    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 29.56/4.13    inference(cnf_transformation,[],[f9])).
% 29.56/4.13  fof(f9,axiom,(
% 29.56/4.13    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 29.56/4.13  fof(f92,plain,(
% 29.56/4.13    spl6_7),
% 29.56/4.13    inference(avatar_split_clause,[],[f42,f90])).
% 29.56/4.13  fof(f42,plain,(
% 29.56/4.13    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 29.56/4.13    inference(cnf_transformation,[],[f20])).
% 29.56/4.13  fof(f20,plain,(
% 29.56/4.13    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 29.56/4.13    inference(rectify,[],[f4])).
% 29.56/4.13  fof(f4,axiom,(
% 29.56/4.13    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 29.56/4.13  fof(f88,plain,(
% 29.56/4.13    spl6_6),
% 29.56/4.13    inference(avatar_split_clause,[],[f40,f86])).
% 29.56/4.13  fof(f40,plain,(
% 29.56/4.13    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 29.56/4.13    inference(cnf_transformation,[],[f12])).
% 29.56/4.13  fof(f12,axiom,(
% 29.56/4.13    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 29.56/4.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 29.56/4.13  fof(f84,plain,(
% 29.56/4.13    spl6_5),
% 29.56/4.13    inference(avatar_split_clause,[],[f39,f82])).
% 29.56/4.13  fof(f39,plain,(
% 29.56/4.13    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 29.56/4.13    inference(cnf_transformation,[],[f14])).
% 29.56/4.14  fof(f14,axiom,(
% 29.56/4.14    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 29.56/4.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 29.56/4.14  fof(f80,plain,(
% 29.56/4.14    spl6_4),
% 29.56/4.14    inference(avatar_split_clause,[],[f36,f78])).
% 29.56/4.14  fof(f36,plain,(
% 29.56/4.14    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 29.56/4.14    inference(cnf_transformation,[],[f28])).
% 29.56/4.14  fof(f28,plain,(
% 29.56/4.14    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 29.56/4.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27])).
% 29.56/4.14  fof(f27,plain,(
% 29.56/4.14    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 29.56/4.14    introduced(choice_axiom,[])).
% 29.56/4.14  fof(f23,plain,(
% 29.56/4.14    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 29.56/4.14    inference(flattening,[],[f22])).
% 29.56/4.14  fof(f22,plain,(
% 29.56/4.14    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 29.56/4.14    inference(ennf_transformation,[],[f19])).
% 29.56/4.14  fof(f19,negated_conjecture,(
% 29.56/4.14    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 29.56/4.14    inference(negated_conjecture,[],[f18])).
% 29.56/4.14  fof(f18,conjecture,(
% 29.56/4.14    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 29.56/4.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 29.56/4.14  fof(f76,plain,(
% 29.56/4.14    ~spl6_2 | ~spl6_3),
% 29.56/4.14    inference(avatar_split_clause,[],[f38,f74,f71])).
% 29.56/4.14  fof(f38,plain,(
% 29.56/4.14    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 29.56/4.14    inference(cnf_transformation,[],[f28])).
% 29.56/4.14  fof(f69,plain,(
% 29.56/4.14    ~spl6_1),
% 29.56/4.14    inference(avatar_split_clause,[],[f37,f67])).
% 29.56/4.14  fof(f37,plain,(
% 29.56/4.14    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 29.56/4.14    inference(cnf_transformation,[],[f28])).
% 29.56/4.14  % SZS output end Proof for theBenchmark
% 29.56/4.14  % (32738)------------------------------
% 29.56/4.14  % (32738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.56/4.14  % (32738)Termination reason: Refutation
% 29.56/4.14  
% 29.56/4.14  % (32738)Memory used [KB]: 29167
% 29.56/4.14  % (32738)Time elapsed: 2.410 s
% 29.56/4.14  % (32738)------------------------------
% 29.56/4.14  % (32738)------------------------------
% 29.56/4.14  % (32670)Success in time 3.784 s
%------------------------------------------------------------------------------
