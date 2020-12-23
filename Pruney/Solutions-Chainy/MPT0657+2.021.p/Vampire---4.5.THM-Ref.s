%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 288 expanded)
%              Number of leaves         :   35 ( 124 expanded)
%              Depth                    :    9
%              Number of atoms          :  579 (1099 expanded)
%              Number of equality atoms :   95 ( 227 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f61,f65,f69,f73,f81,f87,f99,f103,f107,f117,f121,f125,f134,f153,f167,f180,f213,f229,f241,f265,f347,f353,f395,f408])).

fof(f408,plain,
    ( ~ spl2_1
    | spl2_6
    | ~ spl2_15
    | ~ spl2_48 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl2_1
    | spl2_6
    | ~ spl2_15
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f406,f44])).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f406,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_6
    | ~ spl2_15
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f401,f64])).

fof(f64,plain,
    ( sK1 != k2_funct_1(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_6
  <=> sK1 = k2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f401,plain,
    ( sK1 = k2_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_15
    | ~ spl2_48 ),
    inference(superposition,[],[f102,f394])).

fof(f394,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl2_48
  <=> k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f102,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_15
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f395,plain,
    ( ~ spl2_30
    | spl2_48
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_19
    | ~ spl2_36
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f362,f345,f263,f119,f67,f47,f43,f393,f198])).

fof(f198,plain,
    ( spl2_30
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f47,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f67,plain,
    ( spl2_7
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f119,plain,
    ( spl2_19
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f263,plain,
    ( spl2_36
  <=> k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f345,plain,
    ( spl2_44
  <=> ! [X0] :
        ( k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f362,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_19
    | ~ spl2_36
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f361,f264])).

fof(f264,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f263])).

fof(f361,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_19
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f360,f68])).

fof(f68,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f360,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_19
    | ~ spl2_44 ),
    inference(subsumption_resolution,[],[f359,f48])).

fof(f48,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f359,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_19
    | ~ spl2_44 ),
    inference(subsumption_resolution,[],[f358,f44])).

fof(f358,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ spl2_19
    | ~ spl2_44 ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_19
    | ~ spl2_44 ),
    inference(superposition,[],[f346,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f119])).

fof(f346,plain,
    ( ! [X0] :
        ( k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f345])).

fof(f353,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_11
    | spl2_43 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_11
    | spl2_43 ),
    inference(subsumption_resolution,[],[f351,f44])).

fof(f351,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_2
    | ~ spl2_11
    | spl2_43 ),
    inference(subsumption_resolution,[],[f349,f48])).

fof(f349,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_11
    | spl2_43 ),
    inference(resolution,[],[f343,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f343,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl2_43 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl2_43
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f347,plain,
    ( ~ spl2_30
    | ~ spl2_43
    | spl2_44
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_18
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f158,f151,f115,f47,f43,f345,f342,f198])).

fof(f115,plain,
    ( spl2_18
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f151,plain,
    ( spl2_24
  <=> ! [X11,X10] :
        ( ~ v1_relat_1(X10)
        | ~ v1_relat_1(X11)
        | k5_relat_1(k5_relat_1(sK1,X10),X11) = k5_relat_1(sK1,k5_relat_1(X10,X11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f158,plain,
    ( ! [X0] :
        ( k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK1))
        | ~ v2_funct_1(sK1) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_18
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f157,f44])).

fof(f157,plain,
    ( ! [X0] :
        ( k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_18
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f154,f48])).

fof(f154,plain,
    ( ! [X0] :
        ( k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v2_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_18
    | ~ spl2_24 ),
    inference(superposition,[],[f152,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f152,plain,
    ( ! [X10,X11] :
        ( k5_relat_1(k5_relat_1(sK1,X10),X11) = k5_relat_1(sK1,k5_relat_1(X10,X11))
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f151])).

fof(f265,plain,
    ( spl2_36
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f256,f227,f115,f59,f55,f51,f263])).

fof(f51,plain,
    ( spl2_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f55,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f227,plain,
    ( spl2_34
  <=> k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f256,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f255,f56])).

fof(f56,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f255,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f254,f52])).

fof(f52,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f254,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f252,f60])).

fof(f60,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f252,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_18
    | ~ spl2_34 ),
    inference(superposition,[],[f228,f116])).

fof(f228,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f227])).

fof(f241,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | ~ spl2_11
    | spl2_33 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_11
    | spl2_33 ),
    inference(subsumption_resolution,[],[f239,f56])).

fof(f239,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_5
    | ~ spl2_11
    | spl2_33 ),
    inference(subsumption_resolution,[],[f237,f60])).

fof(f237,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_11
    | spl2_33 ),
    inference(resolution,[],[f225,f86])).

fof(f225,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_33 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl2_33
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f229,plain,
    ( ~ spl2_33
    | spl2_34
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f187,f178,f151,f55,f227,f224])).

fof(f178,plain,
    ( spl2_27
  <=> k2_funct_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f187,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f185,f56])).

fof(f185,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_24
    | ~ spl2_27 ),
    inference(superposition,[],[f179,f152])).

fof(f179,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f178])).

fof(f213,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_14
    | ~ spl2_21
    | spl2_30 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_14
    | ~ spl2_21
    | spl2_30 ),
    inference(unit_resulting_resolution,[],[f56,f60,f44,f48,f98,f68,f199,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,X0))
        | k1_relat_1(X0) != k2_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,X0))
        | k1_relat_1(X0) != k2_relat_1(X1)
        | v2_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f199,plain,
    ( ~ v2_funct_1(sK1)
    | spl2_30 ),
    inference(avatar_component_clause,[],[f198])).

fof(f98,plain,
    ( v2_funct_1(k5_relat_1(sK1,sK0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_14
  <=> v2_funct_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f180,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f175,f165,f71,f59,f55,f51,f178])).

fof(f71,plain,
    ( spl2_8
  <=> k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f165,plain,
    ( spl2_26
  <=> ! [X0] :
        ( k2_funct_1(X0) = k5_relat_1(k6_relat_1(k2_relat_1(X0)),k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f175,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f174,f72])).

fof(f72,plain,
    ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f174,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f173,f56])).

fof(f173,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f169,f52])).

fof(f169,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_5
    | ~ spl2_26 ),
    inference(resolution,[],[f166,f60])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k2_funct_1(X0) = k5_relat_1(k6_relat_1(k2_relat_1(X0)),k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl2_26
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f113,f105,f101,f85,f165])).

fof(f105,plain,
    ( spl2_16
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f113,plain,
    ( ! [X0] :
        ( k2_funct_1(X0) = k5_relat_1(k6_relat_1(k2_relat_1(X0)),k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f112,f86])).

fof(f112,plain,
    ( ! [X0] :
        ( k2_funct_1(X0) = k5_relat_1(k6_relat_1(k2_relat_1(X0)),k2_funct_1(X0))
        | ~ v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(superposition,[],[f102,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f153,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f130,f123,f43,f151])).

fof(f123,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f130,plain,
    ( ! [X10,X11] :
        ( ~ v1_relat_1(X10)
        | ~ v1_relat_1(X11)
        | k5_relat_1(k5_relat_1(sK1,X10),X11) = k5_relat_1(sK1,k5_relat_1(X10,X11)) )
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(resolution,[],[f124,f44])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f123])).

fof(f134,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f40,f132])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f125,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f33,f123])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f121,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f39,f119])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f117,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f38,f115])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f36,f105])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f103,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f32,f101])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f99,plain,
    ( spl2_14
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f83,f79,f71,f97])).

fof(f79,plain,
    ( spl2_10
  <=> ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f83,plain,
    ( v2_funct_1(k5_relat_1(sK1,sK0))
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(superposition,[],[f80,f72])).

fof(f80,plain,
    ( ! [X0] : v2_funct_1(k6_relat_1(X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f87,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f34,f85])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f81,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f79])).

fof(f31,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f73,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f71])).

fof(f26,plain,(
    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f69,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f67])).

fof(f25,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:15:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (9158)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.41  % (9158)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f409,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f61,f65,f69,f73,f81,f87,f99,f103,f107,f117,f121,f125,f134,f153,f167,f180,f213,f229,f241,f265,f347,f353,f395,f408])).
% 0.20/0.41  fof(f408,plain,(
% 0.20/0.41    ~spl2_1 | spl2_6 | ~spl2_15 | ~spl2_48),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f407])).
% 0.20/0.41  fof(f407,plain,(
% 0.20/0.41    $false | (~spl2_1 | spl2_6 | ~spl2_15 | ~spl2_48)),
% 0.20/0.41    inference(subsumption_resolution,[],[f406,f44])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f43])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.41  fof(f406,plain,(
% 0.20/0.41    ~v1_relat_1(sK1) | (spl2_6 | ~spl2_15 | ~spl2_48)),
% 0.20/0.41    inference(subsumption_resolution,[],[f401,f64])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    sK1 != k2_funct_1(sK0) | spl2_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f63])).
% 0.20/0.41  fof(f63,plain,(
% 0.20/0.41    spl2_6 <=> sK1 = k2_funct_1(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.41  fof(f401,plain,(
% 0.20/0.41    sK1 = k2_funct_1(sK0) | ~v1_relat_1(sK1) | (~spl2_15 | ~spl2_48)),
% 0.20/0.41    inference(superposition,[],[f102,f394])).
% 0.20/0.41  fof(f394,plain,(
% 0.20/0.41    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) | ~spl2_48),
% 0.20/0.41    inference(avatar_component_clause,[],[f393])).
% 0.20/0.41  fof(f393,plain,(
% 0.20/0.41    spl2_48 <=> k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.20/0.41  fof(f102,plain,(
% 0.20/0.41    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) ) | ~spl2_15),
% 0.20/0.41    inference(avatar_component_clause,[],[f101])).
% 0.20/0.41  fof(f101,plain,(
% 0.20/0.41    spl2_15 <=> ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.41  fof(f395,plain,(
% 0.20/0.41    ~spl2_30 | spl2_48 | ~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_19 | ~spl2_36 | ~spl2_44),
% 0.20/0.41    inference(avatar_split_clause,[],[f362,f345,f263,f119,f67,f47,f43,f393,f198])).
% 0.20/0.41  fof(f198,plain,(
% 0.20/0.41    spl2_30 <=> v2_funct_1(sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    spl2_2 <=> v1_funct_1(sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    spl2_7 <=> k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.41  fof(f119,plain,(
% 0.20/0.41    spl2_19 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.41  fof(f263,plain,(
% 0.20/0.41    spl2_36 <=> k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.20/0.41  fof(f345,plain,(
% 0.20/0.41    spl2_44 <=> ! [X0] : (k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) | ~v1_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.20/0.41  fof(f362,plain,(
% 0.20/0.41    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) | ~v2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_19 | ~spl2_36 | ~spl2_44)),
% 0.20/0.41    inference(forward_demodulation,[],[f361,f264])).
% 0.20/0.41  fof(f264,plain,(
% 0.20/0.41    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))) | ~spl2_36),
% 0.20/0.41    inference(avatar_component_clause,[],[f263])).
% 0.20/0.41  fof(f361,plain,(
% 0.20/0.41    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_7 | ~spl2_19 | ~spl2_44)),
% 0.20/0.41    inference(forward_demodulation,[],[f360,f68])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    k1_relat_1(sK0) = k2_relat_1(sK1) | ~spl2_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f67])).
% 0.20/0.41  fof(f360,plain,(
% 0.20/0.41    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~v2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_19 | ~spl2_44)),
% 0.20/0.41    inference(subsumption_resolution,[],[f359,f48])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    v1_funct_1(sK1) | ~spl2_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f47])).
% 0.20/0.42  fof(f359,plain,(
% 0.20/0.42    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | (~spl2_1 | ~spl2_19 | ~spl2_44)),
% 0.20/0.42    inference(subsumption_resolution,[],[f358,f44])).
% 0.20/0.42  fof(f358,plain,(
% 0.20/0.42    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | (~spl2_19 | ~spl2_44)),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f354])).
% 0.20/0.42  fof(f354,plain,(
% 0.20/0.42    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl2_19 | ~spl2_44)),
% 0.20/0.42    inference(superposition,[],[f346,f120])).
% 0.20/0.42  fof(f120,plain,(
% 0.20/0.42    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_19),
% 0.20/0.42    inference(avatar_component_clause,[],[f119])).
% 0.20/0.42  fof(f346,plain,(
% 0.20/0.42    ( ! [X0] : (k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) | ~v1_relat_1(X0)) ) | ~spl2_44),
% 0.20/0.42    inference(avatar_component_clause,[],[f345])).
% 0.20/0.42  fof(f353,plain,(
% 0.20/0.42    ~spl2_1 | ~spl2_2 | ~spl2_11 | spl2_43),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f352])).
% 0.20/0.42  fof(f352,plain,(
% 0.20/0.42    $false | (~spl2_1 | ~spl2_2 | ~spl2_11 | spl2_43)),
% 0.20/0.42    inference(subsumption_resolution,[],[f351,f44])).
% 0.20/0.42  fof(f351,plain,(
% 0.20/0.42    ~v1_relat_1(sK1) | (~spl2_2 | ~spl2_11 | spl2_43)),
% 0.20/0.42    inference(subsumption_resolution,[],[f349,f48])).
% 0.20/0.42  fof(f349,plain,(
% 0.20/0.42    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl2_11 | spl2_43)),
% 0.20/0.42    inference(resolution,[],[f343,f86])).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f85])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    spl2_11 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.42  fof(f343,plain,(
% 0.20/0.42    ~v1_relat_1(k2_funct_1(sK1)) | spl2_43),
% 0.20/0.42    inference(avatar_component_clause,[],[f342])).
% 0.20/0.42  fof(f342,plain,(
% 0.20/0.42    spl2_43 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.42  fof(f347,plain,(
% 0.20/0.42    ~spl2_30 | ~spl2_43 | spl2_44 | ~spl2_1 | ~spl2_2 | ~spl2_18 | ~spl2_24),
% 0.20/0.42    inference(avatar_split_clause,[],[f158,f151,f115,f47,f43,f345,f342,f198])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    spl2_18 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.42  fof(f151,plain,(
% 0.20/0.42    spl2_24 <=> ! [X11,X10] : (~v1_relat_1(X10) | ~v1_relat_1(X11) | k5_relat_1(k5_relat_1(sK1,X10),X11) = k5_relat_1(sK1,k5_relat_1(X10,X11)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.42  fof(f158,plain,(
% 0.20/0.42    ( ! [X0] : (k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_18 | ~spl2_24)),
% 0.20/0.42    inference(subsumption_resolution,[],[f157,f44])).
% 0.20/0.42  fof(f157,plain,(
% 0.20/0.42    ( ! [X0] : (k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_18 | ~spl2_24)),
% 0.20/0.42    inference(subsumption_resolution,[],[f154,f48])).
% 0.20/0.42  fof(f154,plain,(
% 0.20/0.42    ( ! [X0] : (k5_relat_1(sK1,k5_relat_1(k2_funct_1(sK1),X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl2_18 | ~spl2_24)),
% 0.20/0.42    inference(superposition,[],[f152,f116])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_18),
% 0.20/0.42    inference(avatar_component_clause,[],[f115])).
% 0.20/0.42  fof(f152,plain,(
% 0.20/0.42    ( ! [X10,X11] : (k5_relat_1(k5_relat_1(sK1,X10),X11) = k5_relat_1(sK1,k5_relat_1(X10,X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X10)) ) | ~spl2_24),
% 0.20/0.42    inference(avatar_component_clause,[],[f151])).
% 0.20/0.42  fof(f265,plain,(
% 0.20/0.42    spl2_36 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_18 | ~spl2_34),
% 0.20/0.42    inference(avatar_split_clause,[],[f256,f227,f115,f59,f55,f51,f263])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl2_3 <=> v2_funct_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl2_4 <=> v1_relat_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl2_5 <=> v1_funct_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f227,plain,(
% 0.20/0.42    spl2_34 <=> k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.42  fof(f256,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_18 | ~spl2_34)),
% 0.20/0.42    inference(subsumption_resolution,[],[f255,f56])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    v1_relat_1(sK0) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f55])).
% 0.20/0.42  fof(f255,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_5 | ~spl2_18 | ~spl2_34)),
% 0.20/0.42    inference(subsumption_resolution,[],[f254,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    v2_funct_1(sK0) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f51])).
% 0.20/0.42  fof(f254,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl2_5 | ~spl2_18 | ~spl2_34)),
% 0.20/0.42    inference(subsumption_resolution,[],[f252,f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    v1_funct_1(sK0) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f59])).
% 0.20/0.42  fof(f252,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl2_18 | ~spl2_34)),
% 0.20/0.42    inference(superposition,[],[f228,f116])).
% 0.20/0.42  fof(f228,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) | ~spl2_34),
% 0.20/0.42    inference(avatar_component_clause,[],[f227])).
% 0.20/0.42  fof(f241,plain,(
% 0.20/0.42    ~spl2_4 | ~spl2_5 | ~spl2_11 | spl2_33),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f240])).
% 0.20/0.42  fof(f240,plain,(
% 0.20/0.42    $false | (~spl2_4 | ~spl2_5 | ~spl2_11 | spl2_33)),
% 0.20/0.42    inference(subsumption_resolution,[],[f239,f56])).
% 0.20/0.42  fof(f239,plain,(
% 0.20/0.42    ~v1_relat_1(sK0) | (~spl2_5 | ~spl2_11 | spl2_33)),
% 0.20/0.42    inference(subsumption_resolution,[],[f237,f60])).
% 0.20/0.42  fof(f237,plain,(
% 0.20/0.42    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl2_11 | spl2_33)),
% 0.20/0.42    inference(resolution,[],[f225,f86])).
% 0.20/0.42  fof(f225,plain,(
% 0.20/0.42    ~v1_relat_1(k2_funct_1(sK0)) | spl2_33),
% 0.20/0.42    inference(avatar_component_clause,[],[f224])).
% 0.20/0.42  fof(f224,plain,(
% 0.20/0.42    spl2_33 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.20/0.42  fof(f229,plain,(
% 0.20/0.42    ~spl2_33 | spl2_34 | ~spl2_4 | ~spl2_24 | ~spl2_27),
% 0.20/0.42    inference(avatar_split_clause,[],[f187,f178,f151,f55,f227,f224])).
% 0.20/0.42  fof(f178,plain,(
% 0.20/0.42    spl2_27 <=> k2_funct_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.42  fof(f187,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | (~spl2_4 | ~spl2_24 | ~spl2_27)),
% 0.20/0.42    inference(subsumption_resolution,[],[f185,f56])).
% 0.20/0.42  fof(f185,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_24 | ~spl2_27)),
% 0.20/0.42    inference(superposition,[],[f179,f152])).
% 0.20/0.42  fof(f179,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) | ~spl2_27),
% 0.20/0.42    inference(avatar_component_clause,[],[f178])).
% 0.20/0.42  fof(f213,plain,(
% 0.20/0.42    ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_14 | ~spl2_21 | spl2_30),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f210])).
% 0.20/0.42  fof(f210,plain,(
% 0.20/0.42    $false | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_14 | ~spl2_21 | spl2_30)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f56,f60,f44,f48,f98,f68,f199,f133])).
% 0.20/0.42  fof(f133,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v2_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_21),
% 0.20/0.42    inference(avatar_component_clause,[],[f132])).
% 0.20/0.42  fof(f132,plain,(
% 0.20/0.42    spl2_21 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.42  fof(f199,plain,(
% 0.20/0.42    ~v2_funct_1(sK1) | spl2_30),
% 0.20/0.42    inference(avatar_component_clause,[],[f198])).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    v2_funct_1(k5_relat_1(sK1,sK0)) | ~spl2_14),
% 0.20/0.42    inference(avatar_component_clause,[],[f97])).
% 0.20/0.42  fof(f97,plain,(
% 0.20/0.42    spl2_14 <=> v2_funct_1(k5_relat_1(sK1,sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.42  fof(f180,plain,(
% 0.20/0.42    spl2_27 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_8 | ~spl2_26),
% 0.20/0.42    inference(avatar_split_clause,[],[f175,f165,f71,f59,f55,f51,f178])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl2_8 <=> k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f165,plain,(
% 0.20/0.42    spl2_26 <=> ! [X0] : (k2_funct_1(X0) = k5_relat_1(k6_relat_1(k2_relat_1(X0)),k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.20/0.42  fof(f175,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_8 | ~spl2_26)),
% 0.20/0.42    inference(forward_demodulation,[],[f174,f72])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f71])).
% 0.20/0.42  fof(f174,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_26)),
% 0.20/0.42    inference(subsumption_resolution,[],[f173,f56])).
% 0.20/0.42  fof(f173,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_5 | ~spl2_26)),
% 0.20/0.42    inference(subsumption_resolution,[],[f169,f52])).
% 0.20/0.42  fof(f169,plain,(
% 0.20/0.42    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl2_5 | ~spl2_26)),
% 0.20/0.42    inference(resolution,[],[f166,f60])).
% 0.20/0.42  fof(f166,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_funct_1(X0) | k2_funct_1(X0) = k5_relat_1(k6_relat_1(k2_relat_1(X0)),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_26),
% 0.20/0.42    inference(avatar_component_clause,[],[f165])).
% 0.20/0.42  fof(f167,plain,(
% 0.20/0.42    spl2_26 | ~spl2_11 | ~spl2_15 | ~spl2_16),
% 0.20/0.42    inference(avatar_split_clause,[],[f113,f105,f101,f85,f165])).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    spl2_16 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k6_relat_1(k2_relat_1(X0)),k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_11 | ~spl2_15 | ~spl2_16)),
% 0.20/0.42    inference(subsumption_resolution,[],[f112,f86])).
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k6_relat_1(k2_relat_1(X0)),k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_15 | ~spl2_16)),
% 0.20/0.42    inference(superposition,[],[f102,f106])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_16),
% 0.20/0.42    inference(avatar_component_clause,[],[f105])).
% 0.20/0.42  fof(f153,plain,(
% 0.20/0.42    spl2_24 | ~spl2_1 | ~spl2_20),
% 0.20/0.42    inference(avatar_split_clause,[],[f130,f123,f43,f151])).
% 0.20/0.42  fof(f123,plain,(
% 0.20/0.42    spl2_20 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.42  fof(f130,plain,(
% 0.20/0.42    ( ! [X10,X11] : (~v1_relat_1(X10) | ~v1_relat_1(X11) | k5_relat_1(k5_relat_1(sK1,X10),X11) = k5_relat_1(sK1,k5_relat_1(X10,X11))) ) | (~spl2_1 | ~spl2_20)),
% 0.20/0.42    inference(resolution,[],[f124,f44])).
% 0.20/0.42  fof(f124,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) ) | ~spl2_20),
% 0.20/0.42    inference(avatar_component_clause,[],[f123])).
% 0.20/0.42  fof(f134,plain,(
% 0.20/0.42    spl2_21),
% 0.20/0.42    inference(avatar_split_clause,[],[f40,f132])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    spl2_20),
% 0.20/0.42    inference(avatar_split_clause,[],[f33,f123])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.20/0.42  fof(f121,plain,(
% 0.20/0.42    spl2_19),
% 0.20/0.42    inference(avatar_split_clause,[],[f39,f119])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.42  fof(f117,plain,(
% 0.20/0.42    spl2_18),
% 0.20/0.42    inference(avatar_split_clause,[],[f38,f115])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    spl2_16),
% 0.20/0.42    inference(avatar_split_clause,[],[f36,f105])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    spl2_15),
% 0.20/0.42    inference(avatar_split_clause,[],[f32,f101])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    spl2_14 | ~spl2_8 | ~spl2_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f83,f79,f71,f97])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    spl2_10 <=> ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    v2_funct_1(k5_relat_1(sK1,sK0)) | (~spl2_8 | ~spl2_10)),
% 0.20/0.42    inference(superposition,[],[f80,f72])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) ) | ~spl2_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f79])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl2_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f34,f85])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    spl2_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f31,f79])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f71])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f67])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ~spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f63])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    sK1 != k2_funct_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f29,f59])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    v1_funct_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f55])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    v1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f51])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    v2_funct_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f47])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    v1_funct_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f43])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (9158)------------------------------
% 0.20/0.42  % (9158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (9158)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (9158)Memory used [KB]: 10874
% 0.20/0.42  % (9158)Time elapsed: 0.016 s
% 0.20/0.42  % (9158)------------------------------
% 0.20/0.42  % (9158)------------------------------
% 0.20/0.42  % (9148)Success in time 0.069 s
%------------------------------------------------------------------------------
