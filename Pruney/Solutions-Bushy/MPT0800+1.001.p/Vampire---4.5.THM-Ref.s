%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0800+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 233 expanded)
%              Number of leaves         :   32 ( 110 expanded)
%              Depth                    :    7
%              Number of atoms          :  679 (1428 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f67,f71,f75,f79,f83,f87,f91,f96,f100,f106,f112,f118,f124,f134,f142,f152,f160,f170,f176])).

fof(f176,plain,
    ( ~ spl4_2
    | ~ spl4_5
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f171,f168,f54,f59,f44])).

fof(f44,plain,
    ( spl4_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,
    ( spl4_5
  <=> r4_wellord1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f54,plain,
    ( spl4_4
  <=> r4_wellord1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f168,plain,
    ( spl4_26
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r4_wellord1(X0,sK2)
        | ~ r4_wellord1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f171,plain,
    ( ~ r4_wellord1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(resolution,[],[f169,f56])).

fof(f56,plain,
    ( r4_wellord1(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(sK0,X0)
        | ~ r4_wellord1(X0,sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( ~ spl4_3
    | spl4_26
    | ~ spl4_11
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f162,f158,f85,f168,f49])).

fof(f49,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( r3_wellord1(X0,X1,sK3(X0,X1))
        | ~ r4_wellord1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f158,plain,
    ( spl4_24
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,sK3(X1,X2))
        | ~ r4_wellord1(sK0,X0)
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r4_wellord1(sK0,X0)
        | ~ r4_wellord1(X0,sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_11
    | ~ spl4_24 ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r4_wellord1(sK0,X0)
        | ~ r4_wellord1(X0,sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ r4_wellord1(X0,sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl4_11
    | ~ spl4_24 ),
    inference(resolution,[],[f159,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( r3_wellord1(X0,X1,sK3(X0,X1))
        | ~ r4_wellord1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_wellord1(X0,sK2,sK3(X1,X2))
        | ~ v1_relat_1(X0)
        | ~ r4_wellord1(sK0,X0)
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f158])).

fof(f160,plain,
    ( spl4_24
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f154,f150,f73,f158])).

fof(f73,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( v1_relat_1(sK3(X0,X1))
        | ~ r4_wellord1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f150,plain,
    ( spl4_23
  <=> ! [X1,X0,X2] :
        ( ~ r4_wellord1(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,sK3(X1,X2))
        | ~ v1_relat_1(sK3(X1,X2))
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,sK3(X1,X2))
        | ~ r4_wellord1(sK0,X0)
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,sK3(X1,X2))
        | ~ r4_wellord1(sK0,X0)
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(resolution,[],[f151,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(sK3(X0,X1))
        | ~ r4_wellord1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(sK3(X1,X2))
        | ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,sK3(X1,X2))
        | ~ r4_wellord1(sK0,X0)
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl4_23
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f143,f140,f77,f150])).

fof(f77,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( v1_funct_1(sK3(X0,X1))
        | ~ r4_wellord1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f140,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ r4_wellord1(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( ~ r4_wellord1(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,sK3(X1,X2))
        | ~ v1_relat_1(sK3(X1,X2))
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(resolution,[],[f141,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(sK3(X0,X1))
        | ~ r4_wellord1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r4_wellord1(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( ~ spl4_1
    | spl4_21
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f136,f132,f85,f140,f39])).

fof(f39,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f132,plain,
    ( spl4_20
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,sK3(X2,X3))
        | ~ r4_wellord1(X2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X0)
        | ~ r4_wellord1(sK0,X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X0)
        | ~ r4_wellord1(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0)
        | ~ r4_wellord1(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(resolution,[],[f133,f86])).

fof(f133,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r3_wellord1(sK0,X0,sK3(X2,X3))
        | ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X0)
        | ~ r4_wellord1(X2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl4_20
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f126,f122,f73,f132])).

fof(f122,plain,
    ( spl4_18
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK3(X1,X2))
        | ~ r3_wellord1(X0,sK2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ r3_wellord1(sK0,X0,sK3(X1,X2))
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f126,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,sK3(X2,X3))
        | ~ r4_wellord1(X2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,sK3(X2,X3))
        | ~ r4_wellord1(X2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2)
        | ~ r4_wellord1(X2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(resolution,[],[f123,f74])).

fof(f123,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(sK3(X1,X2))
        | ~ v1_relat_1(X0)
        | ~ r3_wellord1(X0,sK2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ r3_wellord1(sK0,X0,sK3(X1,X2))
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( spl4_18
    | ~ spl4_9
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f119,f116,f77,f122])).

fof(f116,plain,
    ( spl4_17
  <=> ! [X1,X0,X2] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f119,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK3(X1,X2))
        | ~ r3_wellord1(X0,sK2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ r3_wellord1(sK0,X0,sK3(X1,X2))
        | ~ r4_wellord1(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_9
    | ~ spl4_17 ),
    inference(resolution,[],[f117,f78])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f116])).

fof(f118,plain,
    ( spl4_17
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f114,f110,f69,f116])).

fof(f69,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f110,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(k5_relat_1(X2,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2) )
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2) )
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(resolution,[],[f111,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k5_relat_1(X2,X1))
        | ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl4_16
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f108,f104,f81,f110])).

fof(f81,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( v1_funct_1(k5_relat_1(X0,X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f104,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_funct_1(k5_relat_1(X2,X1))
        | ~ v1_relat_1(k5_relat_1(X2,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(k5_relat_1(X2,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2) )
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(k5_relat_1(X2,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(resolution,[],[f105,f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k5_relat_1(X0,X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(k5_relat_1(X2,X1))
        | ~ r3_wellord1(X0,sK2,X1)
        | ~ v1_relat_1(k5_relat_1(X2,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r3_wellord1(sK0,X0,X2) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_15
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f102,f98,f94,f104,f49,f39])).

fof(f94,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r3_wellord1(sK0,sK2,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f98,plain,
    ( spl4_14
  <=> ! [X1,X3,X0,X2,X4] :
        ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
        | ~ r3_wellord1(X1,X2,X4)
        | ~ r3_wellord1(X0,X1,X3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_wellord1(X0,sK2,X1)
        | ~ r3_wellord1(sK0,X0,X2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(k5_relat_1(X2,X1))
        | ~ v1_funct_1(k5_relat_1(X2,X1)) )
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(resolution,[],[f99,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(sK0,sK2,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f99,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
        | ~ r3_wellord1(X1,X2,X4)
        | ~ r3_wellord1(X0,X1,X3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f34,f98])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
      | ~ r3_wellord1(X1,X2,X4)
      | ~ r3_wellord1(X0,X1,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
                      | ~ r3_wellord1(X1,X2,X4)
                      | ~ r3_wellord1(X0,X1,X3)
                      | ~ v1_funct_1(X4)
                      | ~ v1_relat_1(X4) )
                  | ~ v1_funct_1(X3)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
                      | ~ r3_wellord1(X1,X2,X4)
                      | ~ r3_wellord1(X0,X1,X3)
                      | ~ v1_funct_1(X4)
                      | ~ v1_relat_1(X4) )
                  | ~ v1_funct_1(X3)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( ( v1_funct_1(X3)
                    & v1_relat_1(X3) )
                 => ! [X4] :
                      ( ( v1_funct_1(X4)
                        & v1_relat_1(X4) )
                     => ( ( r3_wellord1(X1,X2,X4)
                          & r3_wellord1(X0,X1,X3) )
                       => r3_wellord1(X0,X2,k5_relat_1(X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_wellord1)).

fof(f96,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_13
    | spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f92,f89,f64,f94,f49,f39])).

fof(f64,plain,
    ( spl4_6
  <=> r4_wellord1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f89,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( r4_wellord1(X0,X1)
        | ~ r3_wellord1(X0,X1,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(sK0,sK2,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(sK0) )
    | spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f90,f66])).

fof(f66,plain,
    ( ~ r4_wellord1(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( r4_wellord1(X0,X1)
        | ~ r3_wellord1(X0,X1,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ( r3_wellord1(X0,X1,sK3(X0,X1))
                & v1_funct_1(sK3(X0,X1))
                & v1_relat_1(sK3(X0,X1)) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK3(X0,X1))
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X3] :
                  ( r3_wellord1(X0,X1,X3)
                  & v1_funct_1(X3)
                  & v1_relat_1(X3) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X2] :
                  ( r3_wellord1(X0,X1,X2)
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).

fof(f87,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK3(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f79,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK3(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK3(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f67,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ~ r4_wellord1(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r4_wellord1(sK0,sK2)
    & r4_wellord1(sK1,sK2)
    & r4_wellord1(sK0,sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r4_wellord1(X0,X2)
                & r4_wellord1(X1,X2)
                & r4_wellord1(X0,X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(sK0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(sK0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r4_wellord1(sK0,X2)
            & r4_wellord1(X1,X2)
            & r4_wellord1(sK0,X1)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r4_wellord1(sK0,X2)
          & r4_wellord1(sK1,X2)
          & r4_wellord1(sK0,sK1)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ r4_wellord1(sK0,X2)
        & r4_wellord1(sK1,X2)
        & r4_wellord1(sK0,sK1)
        & v1_relat_1(X2) )
   => ( ~ r4_wellord1(sK0,sK2)
      & r4_wellord1(sK1,sK2)
      & r4_wellord1(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( ( r4_wellord1(X1,X2)
                    & r4_wellord1(X0,X1) )
                 => r4_wellord1(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).

fof(f62,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    r4_wellord1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    r4_wellord1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
