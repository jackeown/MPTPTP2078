%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:45 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 402 expanded)
%              Number of leaves         :   44 ( 183 expanded)
%              Depth                    :    8
%              Number of atoms          :  757 (1359 expanded)
%              Number of equality atoms :  132 ( 243 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f417,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f96,f103,f107,f111,f115,f119,f123,f132,f141,f145,f155,f159,f163,f171,f175,f183,f217,f224,f244,f295,f304,f318,f324,f348,f352,f374,f389,f408,f416])).

fof(f416,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | ~ spl6_12
    | spl6_53 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_12
    | spl6_53 ),
    inference(subsumption_resolution,[],[f414,f71])).

fof(f71,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f414,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_4
    | ~ spl6_12
    | spl6_53 ),
    inference(subsumption_resolution,[],[f413,f83])).

fof(f83,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f413,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_12
    | spl6_53 ),
    inference(superposition,[],[f407,f114])).

fof(f114,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_12
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f407,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | spl6_53 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl6_53
  <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f408,plain,
    ( ~ spl6_53
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_21
    | ~ spl6_23
    | spl6_48
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f397,f387,f372,f169,f161,f94,f86,f406])).

fof(f86,plain,
    ( spl6_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f94,plain,
    ( spl6_7
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f161,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f169,plain,
    ( spl6_23
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f372,plain,
    ( spl6_48
  <=> r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f387,plain,
    ( spl6_51
  <=> k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f397,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_21
    | ~ spl6_23
    | spl6_48
    | ~ spl6_51 ),
    inference(backward_demodulation,[],[f373,f396])).

fof(f396,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f395,f95])).

fof(f95,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f395,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1))))
    | ~ spl6_5
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f394,f170])).

fof(f170,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f169])).

fof(f394,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1))))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl6_5
    | ~ spl6_21
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f393,f87])).

fof(f87,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f393,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1))))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl6_21
    | ~ spl6_51 ),
    inference(superposition,[],[f162,f388])).

fof(f388,plain,
    ( k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f387])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f373,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)))
    | spl6_48 ),
    inference(avatar_component_clause,[],[f372])).

fof(f389,plain,
    ( spl6_51
    | ~ spl6_1
    | ~ spl6_23
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f354,f346,f169,f70,f387])).

fof(f346,plain,
    ( spl6_45
  <=> ! [X0] :
        ( k4_relat_1(X0) = k5_relat_1(k4_relat_1(X0),k6_relat_1(k1_relat_1(X0)))
        | ~ v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f354,plain,
    ( k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))
    | ~ spl6_1
    | ~ spl6_23
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f353,f71])).

fof(f353,plain,
    ( k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl6_23
    | ~ spl6_45 ),
    inference(resolution,[],[f347,f170])).

fof(f347,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k4_relat_1(X0))
        | k4_relat_1(X0) = k5_relat_1(k4_relat_1(X0),k6_relat_1(k1_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f346])).

fof(f374,plain,
    ( ~ spl6_48
    | ~ spl6_1
    | ~ spl6_21
    | ~ spl6_23
    | spl6_46 ),
    inference(avatar_split_clause,[],[f357,f350,f169,f161,f70,f372])).

fof(f350,plain,
    ( spl6_46
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f357,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)))
    | ~ spl6_1
    | ~ spl6_21
    | ~ spl6_23
    | spl6_46 ),
    inference(subsumption_resolution,[],[f356,f170])).

fof(f356,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl6_1
    | ~ spl6_21
    | spl6_46 ),
    inference(subsumption_resolution,[],[f355,f71])).

fof(f355,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl6_21
    | spl6_46 ),
    inference(superposition,[],[f351,f162])).

fof(f351,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
    | spl6_46 ),
    inference(avatar_component_clause,[],[f350])).

fof(f352,plain,
    ( ~ spl6_46
    | ~ spl6_4
    | spl6_18
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_29
    | ~ spl6_41
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f331,f322,f302,f215,f169,f157,f143,f82,f350])).

fof(f143,plain,
    ( spl6_18
  <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f157,plain,
    ( spl6_20
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f215,plain,
    ( spl6_29
  <=> sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f302,plain,
    ( spl6_41
  <=> ! [X0] :
        ( sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0)))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f322,plain,
    ( spl6_42
  <=> ! [X9,X8] :
        ( ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(k5_relat_1(X8,sK1)))
        | k1_funct_1(k5_relat_1(X8,sK1),X9) = k1_funct_1(sK1,k1_funct_1(X8,X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f331,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
    | ~ spl6_4
    | spl6_18
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_29
    | ~ spl6_41
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f330,f216])).

fof(f216,plain,
    ( sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f215])).

fof(f330,plain,
    ( sK0 != k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
    | ~ spl6_4
    | spl6_18
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_29
    | ~ spl6_41
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f329,f315])).

fof(f315,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) = sK3(sK1,sK0)
    | ~ spl6_4
    | ~ spl6_29
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f313,f83])).

fof(f313,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) = sK3(sK1,sK0)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl6_29
    | ~ spl6_41 ),
    inference(superposition,[],[f303,f216])).

fof(f303,plain,
    ( ! [X0] :
        ( sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0)))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f302])).

fof(f329,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
    | spl6_18
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f328,f170])).

fof(f328,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | spl6_18
    | ~ spl6_20
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f325,f158])).

fof(f158,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f325,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ v1_funct_1(k4_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | spl6_18
    | ~ spl6_42 ),
    inference(superposition,[],[f144,f323])).

fof(f323,plain,
    ( ! [X8,X9] :
        ( k1_funct_1(k5_relat_1(X8,sK1),X9) = k1_funct_1(sK1,k1_funct_1(X8,X9))
        | ~ v1_funct_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(k5_relat_1(X8,sK1)))
        | ~ v1_relat_1(X8) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f322])).

fof(f144,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f348,plain,
    ( spl6_45
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f128,f121,f117,f346])).

fof(f117,plain,
    ( spl6_13
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f121,plain,
    ( spl6_14
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f128,plain,
    ( ! [X0] :
        ( k4_relat_1(X0) = k5_relat_1(k4_relat_1(X0),k6_relat_1(k1_relat_1(X0)))
        | ~ v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(superposition,[],[f122,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f122,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f324,plain,
    ( spl6_42
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f312,f293,f74,f70,f322])).

fof(f74,plain,
    ( spl6_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f293,plain,
    ( spl6_40
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
        | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f312,plain,
    ( ! [X8,X9] :
        ( ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(k5_relat_1(X8,sK1)))
        | k1_funct_1(k5_relat_1(X8,sK1),X9) = k1_funct_1(sK1,k1_funct_1(X8,X9)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f308,f71])).

fof(f308,plain,
    ( ! [X8,X9] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(k5_relat_1(X8,sK1)))
        | k1_funct_1(k5_relat_1(X8,sK1),X9) = k1_funct_1(sK1,k1_funct_1(X8,X9)) )
    | ~ spl6_2
    | ~ spl6_40 ),
    inference(resolution,[],[f294,f75])).

fof(f75,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f294,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
        | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f293])).

fof(f318,plain,
    ( ~ spl6_4
    | spl6_19
    | ~ spl6_29
    | ~ spl6_41 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl6_4
    | spl6_19
    | ~ spl6_29
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f316,f216])).

fof(f316,plain,
    ( sK0 != k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ spl6_4
    | spl6_19
    | ~ spl6_29
    | ~ spl6_41 ),
    inference(backward_demodulation,[],[f154,f315])).

fof(f154,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_19
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f304,plain,
    ( spl6_41
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_24
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f252,f242,f173,f74,f70,f302])).

fof(f173,plain,
    ( spl6_24
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f242,plain,
    ( spl6_33
  <=> ! [X0] :
        ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f252,plain,
    ( ! [X0] :
        ( sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0)))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_24
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f251,f71])).

fof(f251,plain,
    ( ! [X0] :
        ( sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0)))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl6_2
    | ~ spl6_24
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f249,f75])).

fof(f249,plain,
    ( ! [X0] :
        ( sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0)))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl6_24
    | ~ spl6_33 ),
    inference(resolution,[],[f243,f174])).

fof(f174,plain,
    ( ! [X2,X0] :
        ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f173])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f242])).

fof(f295,plain,(
    spl6_40 ),
    inference(avatar_split_clause,[],[f56,f293])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f244,plain,
    ( spl6_33
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f240,f222,f139,f78,f74,f70,f242])).

fof(f78,plain,
    ( spl6_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f139,plain,
    ( spl6_17
  <=> k2_funct_1(sK1) = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f222,plain,
    ( spl6_30
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f240,plain,
    ( ! [X0] :
        ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f239,f140])).

fof(f140,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f238,f71])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f237,f75])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(resolution,[],[f223,f79])).

fof(f79,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,(
    spl6_30 ),
    inference(avatar_split_clause,[],[f50,f222])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f217,plain,
    ( spl6_29
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f213,f181,f82,f74,f70,f215])).

fof(f181,plain,
    ( spl6_25
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK3(X0,X2)) = X2
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f213,plain,
    ( sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f212,f71])).

fof(f212,plain,
    ( sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f208,f75])).

fof(f208,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(resolution,[],[f182,f83])).

fof(f182,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK3(X0,X2)) = X2
        | ~ v1_relat_1(X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f183,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f59,f181])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f175,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f60,f173])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f171,plain,
    ( spl6_23
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f151,f139,f105,f74,f70,f169])).

fof(f105,plain,
    ( spl6_10
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f151,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f150,f71])).

fof(f150,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f147,f75])).

fof(f147,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(superposition,[],[f106,f140])).

fof(f106,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f163,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f40,f161])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f159,plain,
    ( spl6_20
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f149,f139,f109,f74,f70,f157])).

fof(f109,plain,
    ( spl6_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f149,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f148,f71])).

fof(f148,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f146,f75])).

fof(f146,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_11
    | ~ spl6_17 ),
    inference(superposition,[],[f110,f140])).

fof(f110,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f155,plain,
    ( ~ spl6_19
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f137,f130,f101,f78,f74,f70,f153])).

fof(f101,plain,
    ( spl6_9
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f130,plain,
    ( spl6_16
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f137,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f102,f135])).

fof(f135,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f134,f71])).

fof(f134,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f133,f75])).

fof(f133,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(resolution,[],[f131,f79])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k4_relat_1(X0) = k2_funct_1(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f102,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f145,plain,
    ( ~ spl6_18
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_8
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f136,f130,f98,f78,f74,f70,f143])).

fof(f98,plain,
    ( spl6_8
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f136,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_8
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f99,f135])).

fof(f99,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f141,plain,
    ( spl6_17
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f135,f130,f78,f74,f70,f139])).

fof(f132,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f43,f130])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f123,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f37,f121])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f119,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f39,f117])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f115,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f38,f113])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f42,f109])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f107,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f41,f105])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,
    ( ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f30,f101,f98])).

fof(f30,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f96,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f66,f94])).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f88,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f35,f86])).

fof(f84,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f34,f82])).

fof(f34,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f32,f74])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21148)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (21160)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (21141)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (21156)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (21153)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (21145)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (21152)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (21141)Refutation not found, incomplete strategy% (21141)------------------------------
% 0.22/0.48  % (21141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (21141)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (21141)Memory used [KB]: 10618
% 0.22/0.48  % (21141)Time elapsed: 0.061 s
% 0.22/0.48  % (21141)------------------------------
% 0.22/0.48  % (21141)------------------------------
% 0.22/0.49  % (21160)Refutation not found, incomplete strategy% (21160)------------------------------
% 0.22/0.49  % (21160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21160)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21160)Memory used [KB]: 10618
% 0.22/0.49  % (21160)Time elapsed: 0.098 s
% 0.22/0.49  % (21160)------------------------------
% 0.22/0.49  % (21160)------------------------------
% 0.22/0.49  % (21157)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (21155)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (21143)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (21146)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (21147)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (21149)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (21144)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (21142)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (21140)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (21158)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (21159)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (21150)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (21154)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.31/0.52  % (21151)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.31/0.52  % (21149)Refutation found. Thanks to Tanya!
% 1.31/0.52  % SZS status Theorem for theBenchmark
% 1.31/0.52  % SZS output start Proof for theBenchmark
% 1.31/0.52  fof(f417,plain,(
% 1.31/0.52    $false),
% 1.31/0.52    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f96,f103,f107,f111,f115,f119,f123,f132,f141,f145,f155,f159,f163,f171,f175,f183,f217,f224,f244,f295,f304,f318,f324,f348,f352,f374,f389,f408,f416])).
% 1.31/0.53  fof(f416,plain,(
% 1.31/0.53    ~spl6_1 | ~spl6_4 | ~spl6_12 | spl6_53),
% 1.31/0.53    inference(avatar_contradiction_clause,[],[f415])).
% 1.31/0.53  fof(f415,plain,(
% 1.31/0.53    $false | (~spl6_1 | ~spl6_4 | ~spl6_12 | spl6_53)),
% 1.31/0.53    inference(subsumption_resolution,[],[f414,f71])).
% 1.31/0.53  fof(f71,plain,(
% 1.31/0.53    v1_relat_1(sK1) | ~spl6_1),
% 1.31/0.53    inference(avatar_component_clause,[],[f70])).
% 1.31/0.53  fof(f70,plain,(
% 1.31/0.53    spl6_1 <=> v1_relat_1(sK1)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.31/0.53  fof(f414,plain,(
% 1.31/0.53    ~v1_relat_1(sK1) | (~spl6_4 | ~spl6_12 | spl6_53)),
% 1.31/0.53    inference(subsumption_resolution,[],[f413,f83])).
% 1.31/0.53  fof(f83,plain,(
% 1.31/0.53    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl6_4),
% 1.31/0.53    inference(avatar_component_clause,[],[f82])).
% 1.31/0.53  fof(f82,plain,(
% 1.31/0.53    spl6_4 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.31/0.53  fof(f413,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl6_12 | spl6_53)),
% 1.31/0.53    inference(superposition,[],[f407,f114])).
% 1.31/0.53  fof(f114,plain,(
% 1.31/0.53    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl6_12),
% 1.31/0.53    inference(avatar_component_clause,[],[f113])).
% 1.31/0.53  fof(f113,plain,(
% 1.31/0.53    spl6_12 <=> ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.31/0.53  fof(f407,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | spl6_53),
% 1.31/0.53    inference(avatar_component_clause,[],[f406])).
% 1.31/0.53  fof(f406,plain,(
% 1.31/0.53    spl6_53 <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.31/0.53  fof(f408,plain,(
% 1.31/0.53    ~spl6_53 | ~spl6_5 | ~spl6_7 | ~spl6_21 | ~spl6_23 | spl6_48 | ~spl6_51),
% 1.31/0.53    inference(avatar_split_clause,[],[f397,f387,f372,f169,f161,f94,f86,f406])).
% 1.31/0.53  fof(f86,plain,(
% 1.31/0.53    spl6_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.31/0.53  fof(f94,plain,(
% 1.31/0.53    spl6_7 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.31/0.53  fof(f161,plain,(
% 1.31/0.53    spl6_21 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.31/0.53  fof(f169,plain,(
% 1.31/0.53    spl6_23 <=> v1_relat_1(k4_relat_1(sK1))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.31/0.53  fof(f372,plain,(
% 1.31/0.53    spl6_48 <=> r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 1.31/0.53  fof(f387,plain,(
% 1.31/0.53    spl6_51 <=> k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 1.31/0.53  fof(f397,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl6_5 | ~spl6_7 | ~spl6_21 | ~spl6_23 | spl6_48 | ~spl6_51)),
% 1.31/0.53    inference(backward_demodulation,[],[f373,f396])).
% 1.31/0.53  fof(f396,plain,(
% 1.31/0.53    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) | (~spl6_5 | ~spl6_7 | ~spl6_21 | ~spl6_23 | ~spl6_51)),
% 1.31/0.53    inference(forward_demodulation,[],[f395,f95])).
% 1.31/0.53  fof(f95,plain,(
% 1.31/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl6_7),
% 1.31/0.53    inference(avatar_component_clause,[],[f94])).
% 1.31/0.53  fof(f395,plain,(
% 1.31/0.53    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1)))) | (~spl6_5 | ~spl6_21 | ~spl6_23 | ~spl6_51)),
% 1.31/0.53    inference(subsumption_resolution,[],[f394,f170])).
% 1.31/0.53  fof(f170,plain,(
% 1.31/0.53    v1_relat_1(k4_relat_1(sK1)) | ~spl6_23),
% 1.31/0.53    inference(avatar_component_clause,[],[f169])).
% 1.31/0.53  fof(f394,plain,(
% 1.31/0.53    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1)))) | ~v1_relat_1(k4_relat_1(sK1)) | (~spl6_5 | ~spl6_21 | ~spl6_51)),
% 1.31/0.53    inference(subsumption_resolution,[],[f393,f87])).
% 1.31/0.53  fof(f87,plain,(
% 1.31/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl6_5),
% 1.31/0.53    inference(avatar_component_clause,[],[f86])).
% 1.31/0.53  fof(f393,plain,(
% 1.31/0.53    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1)))) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK1))) | ~v1_relat_1(k4_relat_1(sK1)) | (~spl6_21 | ~spl6_51)),
% 1.31/0.53    inference(superposition,[],[f162,f388])).
% 1.31/0.53  fof(f388,plain,(
% 1.31/0.53    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) | ~spl6_51),
% 1.31/0.53    inference(avatar_component_clause,[],[f387])).
% 1.31/0.53  fof(f162,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl6_21),
% 1.31/0.53    inference(avatar_component_clause,[],[f161])).
% 1.31/0.53  fof(f373,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))) | spl6_48),
% 1.31/0.53    inference(avatar_component_clause,[],[f372])).
% 1.31/0.53  fof(f389,plain,(
% 1.31/0.53    spl6_51 | ~spl6_1 | ~spl6_23 | ~spl6_45),
% 1.31/0.53    inference(avatar_split_clause,[],[f354,f346,f169,f70,f387])).
% 1.31/0.53  fof(f346,plain,(
% 1.31/0.53    spl6_45 <=> ! [X0] : (k4_relat_1(X0) = k5_relat_1(k4_relat_1(X0),k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.31/0.53  fof(f354,plain,(
% 1.31/0.53    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) | (~spl6_1 | ~spl6_23 | ~spl6_45)),
% 1.31/0.53    inference(subsumption_resolution,[],[f353,f71])).
% 1.31/0.53  fof(f353,plain,(
% 1.31/0.53    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) | ~v1_relat_1(sK1) | (~spl6_23 | ~spl6_45)),
% 1.31/0.53    inference(resolution,[],[f347,f170])).
% 1.31/0.53  fof(f347,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(k4_relat_1(X0)) | k4_relat_1(X0) = k5_relat_1(k4_relat_1(X0),k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(X0)) ) | ~spl6_45),
% 1.31/0.53    inference(avatar_component_clause,[],[f346])).
% 1.31/0.53  fof(f374,plain,(
% 1.31/0.53    ~spl6_48 | ~spl6_1 | ~spl6_21 | ~spl6_23 | spl6_46),
% 1.31/0.53    inference(avatar_split_clause,[],[f357,f350,f169,f161,f70,f372])).
% 1.31/0.53  fof(f350,plain,(
% 1.31/0.53    spl6_46 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 1.31/0.53  fof(f357,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))) | (~spl6_1 | ~spl6_21 | ~spl6_23 | spl6_46)),
% 1.31/0.53    inference(subsumption_resolution,[],[f356,f170])).
% 1.31/0.53  fof(f356,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))) | ~v1_relat_1(k4_relat_1(sK1)) | (~spl6_1 | ~spl6_21 | spl6_46)),
% 1.31/0.53    inference(subsumption_resolution,[],[f355,f71])).
% 1.31/0.53  fof(f355,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | (~spl6_21 | spl6_46)),
% 1.31/0.53    inference(superposition,[],[f351,f162])).
% 1.31/0.53  fof(f351,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | spl6_46),
% 1.31/0.53    inference(avatar_component_clause,[],[f350])).
% 1.31/0.53  fof(f352,plain,(
% 1.31/0.53    ~spl6_46 | ~spl6_4 | spl6_18 | ~spl6_20 | ~spl6_23 | ~spl6_29 | ~spl6_41 | ~spl6_42),
% 1.31/0.53    inference(avatar_split_clause,[],[f331,f322,f302,f215,f169,f157,f143,f82,f350])).
% 1.31/0.53  fof(f143,plain,(
% 1.31/0.53    spl6_18 <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.31/0.53  fof(f157,plain,(
% 1.31/0.53    spl6_20 <=> v1_funct_1(k4_relat_1(sK1))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.31/0.53  fof(f215,plain,(
% 1.31/0.53    spl6_29 <=> sK0 = k1_funct_1(sK1,sK3(sK1,sK0))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.31/0.53  fof(f302,plain,(
% 1.31/0.53    spl6_41 <=> ! [X0] : (sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0))) | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.31/0.53  fof(f322,plain,(
% 1.31/0.53    spl6_42 <=> ! [X9,X8] : (~v1_relat_1(X8) | ~v1_funct_1(X8) | ~r2_hidden(X9,k1_relat_1(k5_relat_1(X8,sK1))) | k1_funct_1(k5_relat_1(X8,sK1),X9) = k1_funct_1(sK1,k1_funct_1(X8,X9)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.31/0.53  fof(f331,plain,(
% 1.31/0.53    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | (~spl6_4 | spl6_18 | ~spl6_20 | ~spl6_23 | ~spl6_29 | ~spl6_41 | ~spl6_42)),
% 1.31/0.53    inference(subsumption_resolution,[],[f330,f216])).
% 1.31/0.53  fof(f216,plain,(
% 1.31/0.53    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~spl6_29),
% 1.31/0.53    inference(avatar_component_clause,[],[f215])).
% 1.31/0.53  fof(f330,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,sK3(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | (~spl6_4 | spl6_18 | ~spl6_20 | ~spl6_23 | ~spl6_29 | ~spl6_41 | ~spl6_42)),
% 1.31/0.53    inference(forward_demodulation,[],[f329,f315])).
% 1.31/0.53  fof(f315,plain,(
% 1.31/0.53    k1_funct_1(k4_relat_1(sK1),sK0) = sK3(sK1,sK0) | (~spl6_4 | ~spl6_29 | ~spl6_41)),
% 1.31/0.53    inference(subsumption_resolution,[],[f313,f83])).
% 1.31/0.53  fof(f313,plain,(
% 1.31/0.53    k1_funct_1(k4_relat_1(sK1),sK0) = sK3(sK1,sK0) | ~r2_hidden(sK0,k2_relat_1(sK1)) | (~spl6_29 | ~spl6_41)),
% 1.31/0.53    inference(superposition,[],[f303,f216])).
% 1.31/0.53  fof(f303,plain,(
% 1.31/0.53    ( ! [X0] : (sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0))) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl6_41),
% 1.31/0.53    inference(avatar_component_clause,[],[f302])).
% 1.31/0.53  fof(f329,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | (spl6_18 | ~spl6_20 | ~spl6_23 | ~spl6_42)),
% 1.31/0.53    inference(subsumption_resolution,[],[f328,f170])).
% 1.31/0.53  fof(f328,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | ~v1_relat_1(k4_relat_1(sK1)) | (spl6_18 | ~spl6_20 | ~spl6_42)),
% 1.31/0.53    inference(subsumption_resolution,[],[f325,f158])).
% 1.31/0.53  fof(f158,plain,(
% 1.31/0.53    v1_funct_1(k4_relat_1(sK1)) | ~spl6_20),
% 1.31/0.53    inference(avatar_component_clause,[],[f157])).
% 1.31/0.53  fof(f325,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | ~v1_relat_1(k4_relat_1(sK1)) | (spl6_18 | ~spl6_42)),
% 1.31/0.53    inference(superposition,[],[f144,f323])).
% 1.31/0.53  fof(f323,plain,(
% 1.31/0.53    ( ! [X8,X9] : (k1_funct_1(k5_relat_1(X8,sK1),X9) = k1_funct_1(sK1,k1_funct_1(X8,X9)) | ~v1_funct_1(X8) | ~r2_hidden(X9,k1_relat_1(k5_relat_1(X8,sK1))) | ~v1_relat_1(X8)) ) | ~spl6_42),
% 1.31/0.53    inference(avatar_component_clause,[],[f322])).
% 1.31/0.53  fof(f144,plain,(
% 1.31/0.53    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | spl6_18),
% 1.31/0.53    inference(avatar_component_clause,[],[f143])).
% 1.31/0.53  fof(f348,plain,(
% 1.31/0.53    spl6_45 | ~spl6_13 | ~spl6_14),
% 1.31/0.53    inference(avatar_split_clause,[],[f128,f121,f117,f346])).
% 1.31/0.53  fof(f117,plain,(
% 1.31/0.53    spl6_13 <=> ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.31/0.53  fof(f121,plain,(
% 1.31/0.53    spl6_14 <=> ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.31/0.53  fof(f128,plain,(
% 1.31/0.53    ( ! [X0] : (k4_relat_1(X0) = k5_relat_1(k4_relat_1(X0),k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl6_13 | ~spl6_14)),
% 1.31/0.53    inference(superposition,[],[f122,f118])).
% 1.31/0.53  fof(f118,plain,(
% 1.31/0.53    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl6_13),
% 1.31/0.53    inference(avatar_component_clause,[],[f117])).
% 1.31/0.53  fof(f122,plain,(
% 1.31/0.53    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) ) | ~spl6_14),
% 1.31/0.53    inference(avatar_component_clause,[],[f121])).
% 1.31/0.53  fof(f324,plain,(
% 1.31/0.53    spl6_42 | ~spl6_1 | ~spl6_2 | ~spl6_40),
% 1.31/0.53    inference(avatar_split_clause,[],[f312,f293,f74,f70,f322])).
% 1.31/0.53  fof(f74,plain,(
% 1.31/0.53    spl6_2 <=> v1_funct_1(sK1)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.31/0.53  fof(f293,plain,(
% 1.31/0.53    spl6_40 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.31/0.53  fof(f312,plain,(
% 1.31/0.53    ( ! [X8,X9] : (~v1_relat_1(X8) | ~v1_funct_1(X8) | ~r2_hidden(X9,k1_relat_1(k5_relat_1(X8,sK1))) | k1_funct_1(k5_relat_1(X8,sK1),X9) = k1_funct_1(sK1,k1_funct_1(X8,X9))) ) | (~spl6_1 | ~spl6_2 | ~spl6_40)),
% 1.31/0.53    inference(subsumption_resolution,[],[f308,f71])).
% 1.31/0.53  fof(f308,plain,(
% 1.31/0.53    ( ! [X8,X9] : (~v1_relat_1(sK1) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | ~r2_hidden(X9,k1_relat_1(k5_relat_1(X8,sK1))) | k1_funct_1(k5_relat_1(X8,sK1),X9) = k1_funct_1(sK1,k1_funct_1(X8,X9))) ) | (~spl6_2 | ~spl6_40)),
% 1.31/0.53    inference(resolution,[],[f294,f75])).
% 1.31/0.53  fof(f75,plain,(
% 1.31/0.53    v1_funct_1(sK1) | ~spl6_2),
% 1.31/0.53    inference(avatar_component_clause,[],[f74])).
% 1.31/0.53  fof(f294,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) ) | ~spl6_40),
% 1.31/0.53    inference(avatar_component_clause,[],[f293])).
% 1.31/0.53  fof(f318,plain,(
% 1.31/0.53    ~spl6_4 | spl6_19 | ~spl6_29 | ~spl6_41),
% 1.31/0.53    inference(avatar_contradiction_clause,[],[f317])).
% 1.31/0.53  fof(f317,plain,(
% 1.31/0.53    $false | (~spl6_4 | spl6_19 | ~spl6_29 | ~spl6_41)),
% 1.31/0.53    inference(subsumption_resolution,[],[f316,f216])).
% 1.31/0.53  fof(f316,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,sK3(sK1,sK0)) | (~spl6_4 | spl6_19 | ~spl6_29 | ~spl6_41)),
% 1.31/0.53    inference(backward_demodulation,[],[f154,f315])).
% 1.31/0.53  fof(f154,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | spl6_19),
% 1.31/0.53    inference(avatar_component_clause,[],[f153])).
% 1.31/0.53  fof(f153,plain,(
% 1.31/0.53    spl6_19 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.31/0.53  fof(f304,plain,(
% 1.31/0.53    spl6_41 | ~spl6_1 | ~spl6_2 | ~spl6_24 | ~spl6_33),
% 1.31/0.53    inference(avatar_split_clause,[],[f252,f242,f173,f74,f70,f302])).
% 1.31/0.53  fof(f173,plain,(
% 1.31/0.53    spl6_24 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.31/0.53  fof(f242,plain,(
% 1.31/0.53    spl6_33 <=> ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.31/0.53  fof(f252,plain,(
% 1.31/0.53    ( ! [X0] : (sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0))) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl6_1 | ~spl6_2 | ~spl6_24 | ~spl6_33)),
% 1.31/0.53    inference(subsumption_resolution,[],[f251,f71])).
% 1.31/0.53  fof(f251,plain,(
% 1.31/0.53    ( ! [X0] : (sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0))) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl6_2 | ~spl6_24 | ~spl6_33)),
% 1.31/0.53    inference(subsumption_resolution,[],[f249,f75])).
% 1.31/0.53  fof(f249,plain,(
% 1.31/0.53    ( ! [X0] : (sK3(sK1,X0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X0))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl6_24 | ~spl6_33)),
% 1.31/0.53    inference(resolution,[],[f243,f174])).
% 1.31/0.53  fof(f174,plain,(
% 1.31/0.53    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) ) | ~spl6_24),
% 1.31/0.53    inference(avatar_component_clause,[],[f173])).
% 1.31/0.53  fof(f243,plain,(
% 1.31/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl6_33),
% 1.31/0.53    inference(avatar_component_clause,[],[f242])).
% 1.31/0.53  fof(f295,plain,(
% 1.31/0.53    spl6_40),
% 1.31/0.53    inference(avatar_split_clause,[],[f56,f293])).
% 1.31/0.53  fof(f56,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f29])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(flattening,[],[f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 1.31/0.53  fof(f244,plain,(
% 1.31/0.53    spl6_33 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_30),
% 1.31/0.53    inference(avatar_split_clause,[],[f240,f222,f139,f78,f74,f70,f242])).
% 1.31/0.53  fof(f78,plain,(
% 1.31/0.53    spl6_3 <=> v2_funct_1(sK1)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.31/0.53  fof(f139,plain,(
% 1.31/0.53    spl6_17 <=> k2_funct_1(sK1) = k4_relat_1(sK1)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.31/0.53  fof(f222,plain,(
% 1.31/0.53    spl6_30 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.31/0.53  fof(f240,plain,(
% 1.31/0.53    ( ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_30)),
% 1.31/0.53    inference(forward_demodulation,[],[f239,f140])).
% 1.31/0.53  fof(f140,plain,(
% 1.31/0.53    k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl6_17),
% 1.31/0.53    inference(avatar_component_clause,[],[f139])).
% 1.31/0.53  fof(f239,plain,(
% 1.31/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30)),
% 1.31/0.53    inference(subsumption_resolution,[],[f238,f71])).
% 1.31/0.53  fof(f238,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl6_2 | ~spl6_3 | ~spl6_30)),
% 1.31/0.53    inference(subsumption_resolution,[],[f237,f75])).
% 1.31/0.53  fof(f237,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl6_3 | ~spl6_30)),
% 1.31/0.53    inference(resolution,[],[f223,f79])).
% 1.31/0.53  fof(f79,plain,(
% 1.31/0.53    v2_funct_1(sK1) | ~spl6_3),
% 1.31/0.53    inference(avatar_component_clause,[],[f78])).
% 1.31/0.53  fof(f223,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) ) | ~spl6_30),
% 1.31/0.53    inference(avatar_component_clause,[],[f222])).
% 1.31/0.53  fof(f224,plain,(
% 1.31/0.53    spl6_30),
% 1.31/0.53    inference(avatar_split_clause,[],[f50,f222])).
% 1.31/0.53  fof(f50,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f25])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(flattening,[],[f24])).
% 1.31/0.53  fof(f24,plain,(
% 1.31/0.53    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,axiom,(
% 1.31/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 1.31/0.53  fof(f217,plain,(
% 1.31/0.53    spl6_29 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_25),
% 1.31/0.53    inference(avatar_split_clause,[],[f213,f181,f82,f74,f70,f215])).
% 1.31/0.53  fof(f181,plain,(
% 1.31/0.53    spl6_25 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.31/0.53  fof(f213,plain,(
% 1.31/0.53    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_25)),
% 1.31/0.53    inference(subsumption_resolution,[],[f212,f71])).
% 1.31/0.53  fof(f212,plain,(
% 1.31/0.53    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~v1_relat_1(sK1) | (~spl6_2 | ~spl6_4 | ~spl6_25)),
% 1.31/0.53    inference(subsumption_resolution,[],[f208,f75])).
% 1.31/0.53  fof(f208,plain,(
% 1.31/0.53    ~v1_funct_1(sK1) | sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~v1_relat_1(sK1) | (~spl6_4 | ~spl6_25)),
% 1.31/0.53    inference(resolution,[],[f182,f83])).
% 1.31/0.53  fof(f182,plain,(
% 1.31/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~v1_relat_1(X0)) ) | ~spl6_25),
% 1.31/0.53    inference(avatar_component_clause,[],[f181])).
% 1.31/0.53  fof(f183,plain,(
% 1.31/0.53    spl6_25),
% 1.31/0.53    inference(avatar_split_clause,[],[f59,f181])).
% 1.31/0.53  fof(f59,plain,(
% 1.31/0.53    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.31/0.53    inference(equality_resolution,[],[f48])).
% 1.31/0.53  fof(f48,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f23])).
% 1.31/0.53  fof(f23,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(flattening,[],[f22])).
% 1.31/0.53  fof(f22,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f4])).
% 1.31/0.53  fof(f4,axiom,(
% 1.31/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.31/0.53  fof(f175,plain,(
% 1.31/0.53    spl6_24),
% 1.31/0.53    inference(avatar_split_clause,[],[f60,f173])).
% 1.31/0.53  fof(f60,plain,(
% 1.31/0.53    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.31/0.53    inference(equality_resolution,[],[f47])).
% 1.31/0.53  fof(f47,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f23])).
% 1.31/0.53  fof(f171,plain,(
% 1.31/0.53    spl6_23 | ~spl6_1 | ~spl6_2 | ~spl6_10 | ~spl6_17),
% 1.31/0.53    inference(avatar_split_clause,[],[f151,f139,f105,f74,f70,f169])).
% 1.31/0.53  fof(f105,plain,(
% 1.31/0.53    spl6_10 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.31/0.53  fof(f151,plain,(
% 1.31/0.53    v1_relat_1(k4_relat_1(sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_10 | ~spl6_17)),
% 1.31/0.53    inference(subsumption_resolution,[],[f150,f71])).
% 1.31/0.53  fof(f150,plain,(
% 1.31/0.53    v1_relat_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl6_2 | ~spl6_10 | ~spl6_17)),
% 1.31/0.53    inference(subsumption_resolution,[],[f147,f75])).
% 1.31/0.53  fof(f147,plain,(
% 1.31/0.53    v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl6_10 | ~spl6_17)),
% 1.31/0.53    inference(superposition,[],[f106,f140])).
% 1.31/0.53  fof(f106,plain,(
% 1.31/0.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl6_10),
% 1.31/0.53    inference(avatar_component_clause,[],[f105])).
% 1.31/0.53  fof(f163,plain,(
% 1.31/0.53    spl6_21),
% 1.31/0.53    inference(avatar_split_clause,[],[f40,f161])).
% 1.31/0.53  fof(f40,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f17])).
% 1.31/0.53  fof(f17,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f1])).
% 1.31/0.53  fof(f1,axiom,(
% 1.31/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.31/0.53  fof(f159,plain,(
% 1.31/0.53    spl6_20 | ~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_17),
% 1.31/0.53    inference(avatar_split_clause,[],[f149,f139,f109,f74,f70,f157])).
% 1.31/0.53  fof(f109,plain,(
% 1.31/0.53    spl6_11 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.31/0.53  fof(f149,plain,(
% 1.31/0.53    v1_funct_1(k4_relat_1(sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_17)),
% 1.31/0.53    inference(subsumption_resolution,[],[f148,f71])).
% 1.31/0.53  fof(f148,plain,(
% 1.31/0.53    v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl6_2 | ~spl6_11 | ~spl6_17)),
% 1.31/0.53    inference(subsumption_resolution,[],[f146,f75])).
% 1.31/0.53  fof(f146,plain,(
% 1.31/0.53    v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl6_11 | ~spl6_17)),
% 1.31/0.53    inference(superposition,[],[f110,f140])).
% 1.31/0.53  fof(f110,plain,(
% 1.31/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl6_11),
% 1.31/0.53    inference(avatar_component_clause,[],[f109])).
% 1.31/0.53  fof(f155,plain,(
% 1.31/0.53    ~spl6_19 | ~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_16),
% 1.31/0.53    inference(avatar_split_clause,[],[f137,f130,f101,f78,f74,f70,f153])).
% 1.31/0.53  fof(f101,plain,(
% 1.31/0.53    spl6_9 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.31/0.53  fof(f130,plain,(
% 1.31/0.53    spl6_16 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.31/0.53  fof(f137,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_16)),
% 1.31/0.53    inference(backward_demodulation,[],[f102,f135])).
% 1.31/0.53  fof(f135,plain,(
% 1.31/0.53    k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_16)),
% 1.31/0.53    inference(subsumption_resolution,[],[f134,f71])).
% 1.31/0.53  fof(f134,plain,(
% 1.31/0.53    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl6_2 | ~spl6_3 | ~spl6_16)),
% 1.31/0.53    inference(subsumption_resolution,[],[f133,f75])).
% 1.31/0.53  fof(f133,plain,(
% 1.31/0.53    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl6_3 | ~spl6_16)),
% 1.31/0.53    inference(resolution,[],[f131,f79])).
% 1.31/0.53  fof(f131,plain,(
% 1.31/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) ) | ~spl6_16),
% 1.31/0.53    inference(avatar_component_clause,[],[f130])).
% 1.31/0.53  fof(f102,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | spl6_9),
% 1.31/0.53    inference(avatar_component_clause,[],[f101])).
% 1.31/0.53  fof(f145,plain,(
% 1.31/0.53    ~spl6_18 | ~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_8 | ~spl6_16),
% 1.31/0.53    inference(avatar_split_clause,[],[f136,f130,f98,f78,f74,f70,f143])).
% 1.31/0.53  fof(f98,plain,(
% 1.31/0.53    spl6_8 <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.31/0.53  fof(f136,plain,(
% 1.31/0.53    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_8 | ~spl6_16)),
% 1.31/0.53    inference(backward_demodulation,[],[f99,f135])).
% 1.31/0.53  fof(f99,plain,(
% 1.31/0.53    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | spl6_8),
% 1.31/0.53    inference(avatar_component_clause,[],[f98])).
% 1.31/0.53  fof(f141,plain,(
% 1.31/0.53    spl6_17 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_16),
% 1.31/0.53    inference(avatar_split_clause,[],[f135,f130,f78,f74,f70,f139])).
% 1.31/0.53  fof(f132,plain,(
% 1.31/0.53    spl6_16),
% 1.31/0.53    inference(avatar_split_clause,[],[f43,f130])).
% 1.31/0.53  fof(f43,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f21])).
% 1.31/0.53  fof(f21,plain,(
% 1.31/0.53    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(flattening,[],[f20])).
% 1.31/0.53  fof(f20,plain,(
% 1.31/0.53    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f5])).
% 1.31/0.53  fof(f5,axiom,(
% 1.31/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.31/0.53  fof(f123,plain,(
% 1.31/0.53    spl6_14),
% 1.31/0.53    inference(avatar_split_clause,[],[f37,f121])).
% 1.31/0.53  fof(f37,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f15])).
% 1.31/0.53  fof(f15,plain,(
% 1.31/0.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f3])).
% 1.31/0.53  fof(f3,axiom,(
% 1.31/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.31/0.53  fof(f119,plain,(
% 1.31/0.53    spl6_13),
% 1.31/0.53    inference(avatar_split_clause,[],[f39,f117])).
% 1.31/0.53  fof(f39,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f16])).
% 1.31/0.53  fof(f16,plain,(
% 1.31/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f2])).
% 1.31/0.53  fof(f2,axiom,(
% 1.31/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.31/0.53  fof(f115,plain,(
% 1.31/0.53    spl6_12),
% 1.31/0.53    inference(avatar_split_clause,[],[f38,f113])).
% 1.31/0.53  fof(f38,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f16])).
% 1.31/0.53  fof(f111,plain,(
% 1.31/0.53    spl6_11),
% 1.31/0.53    inference(avatar_split_clause,[],[f42,f109])).
% 1.31/0.53  fof(f42,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f19])).
% 1.31/0.53  fof(f19,plain,(
% 1.31/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(flattening,[],[f18])).
% 1.31/0.53  fof(f18,plain,(
% 1.31/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f6])).
% 1.31/0.53  fof(f6,axiom,(
% 1.31/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.31/0.53  fof(f107,plain,(
% 1.31/0.53    spl6_10),
% 1.31/0.53    inference(avatar_split_clause,[],[f41,f105])).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f19])).
% 1.31/0.53  fof(f103,plain,(
% 1.31/0.53    ~spl6_8 | ~spl6_9),
% 1.31/0.53    inference(avatar_split_clause,[],[f30,f101,f98])).
% 1.31/0.53  fof(f30,plain,(
% 1.31/0.53    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 1.31/0.53    inference(cnf_transformation,[],[f14])).
% 1.31/0.53  fof(f14,plain,(
% 1.31/0.53    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.31/0.53    inference(flattening,[],[f13])).
% 1.31/0.53  fof(f13,plain,(
% 1.31/0.53    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f12])).
% 1.31/0.53  fof(f12,negated_conjecture,(
% 1.31/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.31/0.53    inference(negated_conjecture,[],[f11])).
% 1.31/0.53  fof(f11,conjecture,(
% 1.31/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 1.31/0.53  fof(f96,plain,(
% 1.31/0.53    spl6_7),
% 1.31/0.53    inference(avatar_split_clause,[],[f66,f94])).
% 1.31/0.53  fof(f66,plain,(
% 1.31/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f65,f36])).
% 1.31/0.53  fof(f36,plain,(
% 1.31/0.53    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f7])).
% 1.31/0.53  fof(f7,axiom,(
% 1.31/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.31/0.53  fof(f65,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f61,f35])).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f7])).
% 1.31/0.53  fof(f61,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.31/0.53    inference(equality_resolution,[],[f55])).
% 1.31/0.53  fof(f55,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f27,plain,(
% 1.31/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(flattening,[],[f26])).
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f9])).
% 1.31/0.53  fof(f9,axiom,(
% 1.31/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 1.31/0.53  fof(f88,plain,(
% 1.31/0.53    spl6_5),
% 1.31/0.53    inference(avatar_split_clause,[],[f35,f86])).
% 1.31/0.53  fof(f84,plain,(
% 1.31/0.53    spl6_4),
% 1.31/0.53    inference(avatar_split_clause,[],[f34,f82])).
% 1.31/0.53  fof(f34,plain,(
% 1.31/0.53    r2_hidden(sK0,k2_relat_1(sK1))),
% 1.31/0.53    inference(cnf_transformation,[],[f14])).
% 1.31/0.53  fof(f80,plain,(
% 1.31/0.53    spl6_3),
% 1.31/0.53    inference(avatar_split_clause,[],[f33,f78])).
% 1.31/0.53  fof(f33,plain,(
% 1.31/0.53    v2_funct_1(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f14])).
% 1.31/0.53  fof(f76,plain,(
% 1.31/0.53    spl6_2),
% 1.31/0.53    inference(avatar_split_clause,[],[f32,f74])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    v1_funct_1(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f14])).
% 1.31/0.53  fof(f72,plain,(
% 1.31/0.53    spl6_1),
% 1.31/0.53    inference(avatar_split_clause,[],[f31,f70])).
% 1.31/0.53  fof(f31,plain,(
% 1.31/0.53    v1_relat_1(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f14])).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (21149)------------------------------
% 1.31/0.53  % (21149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (21149)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (21149)Memory used [KB]: 10874
% 1.31/0.53  % (21149)Time elapsed: 0.118 s
% 1.31/0.53  % (21149)------------------------------
% 1.31/0.53  % (21149)------------------------------
% 1.31/0.53  % (21139)Success in time 0.17 s
%------------------------------------------------------------------------------
