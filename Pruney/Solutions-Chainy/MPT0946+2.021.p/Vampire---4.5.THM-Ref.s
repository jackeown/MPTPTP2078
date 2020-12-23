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
% DateTime   : Thu Dec  3 13:00:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  254 ( 480 expanded)
%              Number of leaves         :   59 ( 230 expanded)
%              Depth                    :    7
%              Number of atoms          :  938 (1643 expanded)
%              Number of equality atoms :   97 ( 184 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f620,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f111,f115,f123,f127,f131,f135,f139,f147,f151,f155,f159,f174,f181,f185,f197,f203,f207,f219,f247,f280,f296,f309,f325,f329,f346,f357,f371,f380,f409,f413,f428,f449,f464,f468,f477,f479,f495,f532,f554,f603,f619])).

fof(f619,plain,
    ( spl6_47
    | ~ spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_70
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f610,f601,f493,f89,f85,f77,f327])).

fof(f327,plain,
    ( spl6_47
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f77,plain,
    ( spl6_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f85,plain,
    ( spl6_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f89,plain,
    ( spl6_4
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f493,plain,
    ( spl6_70
  <=> ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),X0))
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f601,plain,
    ( spl6_86
  <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f610,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_1
    | spl6_3
    | ~ spl6_4
    | ~ spl6_70
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f609,f78])).

fof(f78,plain,
    ( v3_ordinal1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f609,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_70
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f608,f86])).

fof(f86,plain,
    ( sK0 != sK1
    | spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f608,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | ~ spl6_4
    | ~ spl6_70
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f607,f90])).

fof(f90,plain,
    ( r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f607,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | ~ spl6_70
    | ~ spl6_86 ),
    inference(superposition,[],[f494,f602])).

fof(f602,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f601])).

fof(f494,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),X0))
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0) )
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f493])).

fof(f603,plain,
    ( spl6_86
    | ~ spl6_13
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f560,f552,f125,f601])).

fof(f125,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f552,plain,
    ( spl6_78
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f560,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl6_13
    | ~ spl6_78 ),
    inference(resolution,[],[f553,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f553,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f552])).

fof(f554,plain,
    ( spl6_78
    | ~ spl6_29
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f538,f530,f205,f552])).

fof(f205,plain,
    ( spl6_29
  <=> ! [X3,X0,X2] :
        ( r1_tarski(X2,X3)
        | ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f530,plain,
    ( spl6_76
  <=> r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f538,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_29
    | ~ spl6_76 ),
    inference(resolution,[],[f531,f206])).

fof(f206,plain,
    ( ! [X2,X0,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))
        | r1_tarski(X2,X3) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f205])).

fof(f531,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK3(sK0)))
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f530])).

fof(f532,plain,
    ( spl6_76
    | ~ spl6_41
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f486,f466,f291,f530])).

fof(f291,plain,
    ( spl6_41
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f466,plain,
    ( spl6_68
  <=> ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK3(sK0)))
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f486,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK3(sK0)))
    | ~ spl6_41
    | ~ spl6_68 ),
    inference(resolution,[],[f292,f467])).

fof(f467,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK3(sK0))) )
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f466])).

fof(f292,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f291])).

fof(f495,plain,
    ( spl6_70
    | ~ spl6_28
    | ~ spl6_34
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f376,f369,f245,f201,f493])).

fof(f201,plain,
    ( spl6_28
  <=> ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_hidden(sK0,X1)
        | sK0 = X1
        | r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f245,plain,
    ( spl6_34
  <=> ! [X0] :
        ( r2_hidden(sK0,X0)
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f369,plain,
    ( spl6_53
  <=> ! [X1] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1)))
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f376,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),X0))
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0) )
    | ~ spl6_28
    | ~ spl6_34
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f374,f202])).

fof(f202,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK0)
        | r2_hidden(sK0,X1)
        | sK0 = X1
        | ~ v3_ordinal1(X1) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f201])).

fof(f374,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),X0))
        | ~ r2_hidden(X0,sK0)
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0) )
    | ~ spl6_34
    | ~ spl6_53 ),
    inference(superposition,[],[f370,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( k1_wellord1(k1_wellord2(sK0),X0) = X0
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f245])).

fof(f370,plain,
    ( ! [X1] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1)))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f369])).

fof(f479,plain,
    ( ~ spl6_4
    | ~ spl6_13
    | spl6_59
    | ~ spl6_67 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_13
    | spl6_59
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f474,f90])).

fof(f474,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ spl6_13
    | spl6_59
    | ~ spl6_67 ),
    inference(backward_demodulation,[],[f408,f472])).

fof(f472,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl6_13
    | ~ spl6_67 ),
    inference(resolution,[],[f463,f126])).

fof(f463,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl6_67
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f408,plain,
    ( ~ r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1))
    | spl6_59 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl6_59
  <=> r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f477,plain,
    ( ~ spl6_5
    | ~ spl6_13
    | spl6_58
    | ~ spl6_67 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_13
    | spl6_58
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f473,f94])).

fof(f94,plain,
    ( ! [X0] : v1_relat_1(k1_wellord2(X0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_5
  <=> ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f473,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl6_13
    | spl6_58
    | ~ spl6_67 ),
    inference(backward_demodulation,[],[f405,f472])).

fof(f405,plain,
    ( ~ v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0))
    | spl6_58 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl6_58
  <=> v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f468,plain,
    ( spl6_68
    | ~ spl6_2
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f415,f411,f81,f466])).

fof(f81,plain,
    ( spl6_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f411,plain,
    ( spl6_60
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK3(X0)))
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f415,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK3(sK0)))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_2
    | ~ spl6_60 ),
    inference(resolution,[],[f412,f82])).

fof(f82,plain,
    ( v3_ordinal1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f412,plain,
    ( ! [X0,X1] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK3(X0)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f411])).

fof(f464,plain,
    ( spl6_67
    | ~ spl6_29
    | ~ spl6_65 ),
    inference(avatar_split_clause,[],[f456,f447,f205,f462])).

fof(f447,plain,
    ( spl6_65
  <=> r2_hidden(k4_tarski(sK0,sK1),k1_wellord2(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f456,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_29
    | ~ spl6_65 ),
    inference(resolution,[],[f448,f206])).

fof(f448,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k1_wellord2(sK3(sK1)))
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f447])).

fof(f449,plain,
    ( spl6_65
    | ~ spl6_47
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f439,f426,f327,f447])).

fof(f426,plain,
    ( spl6_62
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK1),k1_wellord2(sK3(sK1)))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f439,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k1_wellord2(sK3(sK1)))
    | ~ spl6_47
    | ~ spl6_62 ),
    inference(resolution,[],[f427,f328])).

fof(f328,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f327])).

fof(f427,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k4_tarski(X0,sK1),k1_wellord2(sK3(sK1))) )
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f426])).

fof(f428,plain,
    ( spl6_62
    | ~ spl6_1
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f414,f411,f77,f426])).

fof(f414,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK1),k1_wellord2(sK3(sK1)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_1
    | ~ spl6_60 ),
    inference(resolution,[],[f412,f78])).

fof(f413,plain,
    ( spl6_60
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f299,f172,f137,f93,f411])).

fof(f137,plain,
    ( spl6_16
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,X1),X0)
        | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f172,plain,
    ( spl6_23
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK3(X0)))
        | ~ v3_ordinal1(X0) )
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f297,f94])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK3(X0)))
        | ~ v1_relat_1(k1_wellord2(sK3(X0)))
        | ~ v3_ordinal1(X0) )
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(superposition,[],[f138,f173])).

fof(f173,plain,
    ( ! [X0] :
        ( k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f172])).

fof(f138,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k1_wellord1(X0,X1))
        | r2_hidden(k4_tarski(X3,X1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f137])).

fof(f409,plain,
    ( ~ spl6_58
    | ~ spl6_59
    | ~ spl6_5
    | ~ spl6_12
    | spl6_54 ),
    inference(avatar_split_clause,[],[f387,f378,f121,f93,f407,f404])).

fof(f121,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r4_wellord1(X0,X1)
        | r4_wellord1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f378,plain,
    ( spl6_54
  <=> r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f387,plain,
    ( ~ r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1))
    | ~ v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ spl6_5
    | ~ spl6_12
    | spl6_54 ),
    inference(subsumption_resolution,[],[f386,f94])).

fof(f386,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1))
    | ~ v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ spl6_12
    | spl6_54 ),
    inference(resolution,[],[f379,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(X1,X0)
        | ~ v1_relat_1(X1)
        | ~ r4_wellord1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f379,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | spl6_54 ),
    inference(avatar_component_clause,[],[f378])).

fof(f380,plain,
    ( ~ spl6_54
    | ~ spl6_47
    | ~ spl6_49
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f367,f355,f344,f327,f378])).

fof(f344,plain,
    ( spl6_49
  <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f355,plain,
    ( spl6_51
  <=> ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f367,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ spl6_47
    | ~ spl6_49
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f364,f328])).

fof(f364,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ spl6_49
    | ~ spl6_51 ),
    inference(superposition,[],[f356,f345])).

fof(f345,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f344])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f355])).

fof(f371,plain,
    ( spl6_53
    | ~ spl6_2
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f331,f323,f81,f369])).

fof(f323,plain,
    ( spl6_46
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f331,plain,
    ( ! [X1] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1)))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_2
    | ~ spl6_46 ),
    inference(resolution,[],[f324,f82])).

fof(f324,plain,
    ( ! [X0,X1] :
        ( ~ v3_ordinal1(X0)
        | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f323])).

fof(f357,plain,
    ( spl6_51
    | ~ spl6_1
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f330,f323,f77,f355])).

fof(f330,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_1
    | ~ spl6_46 ),
    inference(resolution,[],[f324,f78])).

fof(f346,plain,
    ( spl6_49
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f339,f327,f149,f81,f77,f344])).

fof(f149,plain,
    ( spl6_18
  <=> ! [X1,X0] :
        ( ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(X1)
        | ~ r2_hidden(X0,X1)
        | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f339,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f338,f82])).

fof(f338,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl6_1
    | ~ spl6_18
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f337,f78])).

fof(f337,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl6_18
    | ~ spl6_47 ),
    inference(resolution,[],[f328,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v3_ordinal1(X1)
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(X1),X0) = X0 )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f329,plain,
    ( spl6_47
    | ~ spl6_1
    | spl6_3
    | ~ spl6_20
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f321,f307,f157,f85,f77,f327])).

fof(f157,plain,
    ( spl6_20
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f307,plain,
    ( spl6_44
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),k1_wellord2(sK1))
        | r2_hidden(sK0,X0)
        | sK0 = X0
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f321,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_1
    | spl6_3
    | ~ spl6_20
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f320,f158])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
        | r2_hidden(X1,X2) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f320,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK1))
    | ~ spl6_1
    | spl6_3
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f317,f86])).

fof(f317,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK1))
    | ~ spl6_1
    | ~ spl6_44 ),
    inference(resolution,[],[f308,f78])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0)
        | sK0 = X0
        | r2_hidden(k4_tarski(X0,sK0),k1_wellord2(sK1)) )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f307])).

fof(f325,plain,
    ( spl6_46
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f238,f183,f109,f97,f93,f323])).

fof(f97,plain,
    ( spl6_6
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | v2_wellord1(k1_wellord2(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f109,plain,
    ( spl6_9
  <=> ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f183,plain,
    ( spl6_25
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v2_wellord1(X0)
        | ~ r2_hidden(X1,k3_relat_1(X0))
        | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
        | ~ v3_ordinal1(X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f237,f110])).

fof(f110,plain,
    ( ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
        | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
        | ~ v3_ordinal1(X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f236,f94])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k1_wellord2(X0))
        | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
        | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
        | ~ v3_ordinal1(X0) )
    | ~ spl6_6
    | ~ spl6_25 ),
    inference(resolution,[],[f184,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( v2_wellord1(k1_wellord2(X0))
        | ~ v3_ordinal1(X0) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k3_relat_1(X0))
        | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f183])).

fof(f309,plain,
    ( spl6_44
    | ~ spl6_28
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f305,f294,f201,f307])).

fof(f294,plain,
    ( spl6_42
  <=> ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK1))
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f305,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),k1_wellord2(sK1))
        | r2_hidden(sK0,X0)
        | sK0 = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl6_28
    | ~ spl6_42 ),
    inference(resolution,[],[f295,f202])).

fof(f295,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK1)) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( spl6_41
    | spl6_42
    | ~ spl6_2
    | spl6_3
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f286,f278,f85,f81,f294,f291])).

fof(f278,plain,
    ( spl6_40
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK1))
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f286,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK1))
        | ~ r2_hidden(X1,sK0)
        | r2_hidden(sK1,sK0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f284,f86])).

fof(f284,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK1))
        | sK0 = sK1
        | ~ r2_hidden(X1,sK0)
        | r2_hidden(sK1,sK0) )
    | ~ spl6_2
    | ~ spl6_40 ),
    inference(resolution,[],[f279,f82])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK1))
        | sK1 = X0
        | ~ r2_hidden(X1,X0)
        | r2_hidden(sK1,X0) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,
    ( spl6_40
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f226,f217,f137,f93,f278])).

fof(f217,plain,
    ( spl6_31
  <=> ! [X0] :
        ( r2_hidden(sK1,X0)
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK1))
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0) )
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f224,f94])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK1))
        | ~ v1_relat_1(k1_wellord2(sK1))
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0) )
    | ~ spl6_16
    | ~ spl6_31 ),
    inference(superposition,[],[f138,f218])).

fof(f218,plain,
    ( ! [X0] :
        ( k1_wellord1(k1_wellord2(sK1),X0) = X0
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f217])).

fof(f247,plain,
    ( spl6_34
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f211,f201,f149,f81,f245])).

fof(f211,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0 )
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f210,f82])).

fof(f210,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0 )
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK0)
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0 )
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(resolution,[],[f202,f150])).

fof(f219,plain,
    ( spl6_31
    | ~ spl6_1
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f193,f179,f149,f77,f217])).

fof(f179,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0)
        | sK1 = X0
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f193,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0 )
    | ~ spl6_1
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f192,f78])).

fof(f192,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK1)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0 )
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK1)
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0 )
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(resolution,[],[f180,f150])).

fof(f180,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(sK1,X0)
        | sK1 = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f179])).

fof(f207,plain,
    ( spl6_29
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f199,f195,f157,f145,f205])).

fof(f145,plain,
    ( spl6_17
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f195,plain,
    ( spl6_27
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X3,X0)
        | r1_tarski(X2,X3)
        | ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f199,plain,
    ( ! [X2,X0,X3] :
        ( r1_tarski(X2,X3)
        | ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) )
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f198,f158])).

fof(f198,plain,
    ( ! [X2,X0,X3] :
        ( ~ r2_hidden(X3,X0)
        | r1_tarski(X2,X3)
        | ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) )
    | ~ spl6_17
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f196,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
        | r2_hidden(X0,X2) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f196,plain,
    ( ! [X2,X0,X3] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X3,X0)
        | r1_tarski(X2,X3)
        | ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f195])).

fof(f203,plain,
    ( spl6_28
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f176,f153,f81,f201])).

fof(f153,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(X1)
        | r2_hidden(X0,X1)
        | X0 = X1
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f176,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_hidden(sK0,X1)
        | sK0 = X1
        | r2_hidden(X1,sK0) )
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(resolution,[],[f154,f82])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(X1)
        | r2_hidden(X0,X1)
        | X0 = X1
        | r2_hidden(X1,X0) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f197,plain,(
    spl6_27 ),
    inference(avatar_split_clause,[],[f74,f195])).

fof(f74,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f70,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f185,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f37,f183])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f181,plain,
    ( spl6_24
    | ~ spl6_1
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f175,f153,f77,f179])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0)
        | sK1 = X0
        | r2_hidden(X0,sK1) )
    | ~ spl6_1
    | ~ spl6_19 ),
    inference(resolution,[],[f154,f78])).

fof(f174,plain,
    ( spl6_23
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f170,f149,f113,f101,f172])).

fof(f101,plain,
    ( spl6_7
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | v3_ordinal1(sK3(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f113,plain,
    ( spl6_10
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK3(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0 )
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f169,f102])).

fof(f102,plain,
    ( ! [X0] :
        ( v3_ordinal1(sK3(X0))
        | ~ v3_ordinal1(X0) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(sK3(X0))
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0 )
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(sK3(X0))
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(resolution,[],[f150,f114])).

fof(f114,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3(X0))
        | ~ v3_ordinal1(X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f159,plain,
    ( spl6_20
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f143,f133,f109,f93,f157])).

fof(f133,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | r2_hidden(X1,k3_relat_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) )
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f142,f110])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
        | r2_hidden(X1,k3_relat_1(k1_wellord2(X2))) )
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(resolution,[],[f134,f94])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | r2_hidden(X1,k3_relat_1(X2)) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f155,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f47,f153])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f151,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f46,f149])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f147,plain,
    ( spl6_17
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f141,f129,f109,f93,f145])).

fof(f129,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | r2_hidden(X0,k3_relat_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) )
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f140,f110])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
        | r2_hidden(X0,k3_relat_1(k1_wellord2(X2))) )
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(resolution,[],[f130,f94])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | r2_hidden(X0,k3_relat_1(X2)) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f139,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f62,f137])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f135,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f60,f133])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f131,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f59,f129])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f127,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f58,f125])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f123,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f38,f121])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f115,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f49,f113])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X0,sK3(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_ordinal1(X1)
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ? [X1] :
          ( v4_ordinal1(X1)
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_ordinal1)).

fof(f111,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f73,f109])).

fof(f73,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v2_wellord1(k1_wellord2(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f95,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f91,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f87,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f34,f85])).

fof(f34,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (26948)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (26941)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (26941)Refutation not found, incomplete strategy% (26941)------------------------------
% 0.21/0.46  % (26941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (26941)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (26941)Memory used [KB]: 6140
% 0.21/0.46  % (26941)Time elapsed: 0.056 s
% 0.21/0.46  % (26941)------------------------------
% 0.21/0.46  % (26941)------------------------------
% 0.21/0.47  % (26947)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (26933)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (26940)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (26945)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (26936)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (26939)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (26937)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (26931)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (26946)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (26931)Refutation not found, incomplete strategy% (26931)------------------------------
% 0.21/0.50  % (26931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26931)Memory used [KB]: 6140
% 0.21/0.50  % (26931)Time elapsed: 0.083 s
% 0.21/0.50  % (26931)------------------------------
% 0.21/0.50  % (26931)------------------------------
% 0.21/0.50  % (26935)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (26934)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (26938)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (26932)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (26950)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (26949)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (26951)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (26932)Refutation not found, incomplete strategy% (26932)------------------------------
% 0.21/0.51  % (26932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26932)Memory used [KB]: 10618
% 0.21/0.51  % (26932)Time elapsed: 0.088 s
% 0.21/0.51  % (26932)------------------------------
% 0.21/0.51  % (26932)------------------------------
% 0.21/0.51  % (26951)Refutation not found, incomplete strategy% (26951)------------------------------
% 0.21/0.51  % (26951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26951)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26951)Memory used [KB]: 10618
% 0.21/0.51  % (26951)Time elapsed: 0.099 s
% 0.21/0.51  % (26951)------------------------------
% 0.21/0.51  % (26951)------------------------------
% 0.21/0.51  % (26942)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (26944)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (26940)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f620,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f111,f115,f123,f127,f131,f135,f139,f147,f151,f155,f159,f174,f181,f185,f197,f203,f207,f219,f247,f280,f296,f309,f325,f329,f346,f357,f371,f380,f409,f413,f428,f449,f464,f468,f477,f479,f495,f532,f554,f603,f619])).
% 0.21/0.51  fof(f619,plain,(
% 0.21/0.51    spl6_47 | ~spl6_1 | spl6_3 | ~spl6_4 | ~spl6_70 | ~spl6_86),
% 0.21/0.51    inference(avatar_split_clause,[],[f610,f601,f493,f89,f85,f77,f327])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    spl6_47 <=> r2_hidden(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl6_1 <=> v3_ordinal1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl6_3 <=> sK0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl6_4 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f493,plain,(
% 0.21/0.51    spl6_70 <=> ! [X0] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),X0)) | sK0 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK0,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 0.21/0.51  fof(f601,plain,(
% 0.21/0.51    spl6_86 <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).
% 0.21/0.51  fof(f610,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | (~spl6_1 | spl6_3 | ~spl6_4 | ~spl6_70 | ~spl6_86)),
% 0.21/0.51    inference(subsumption_resolution,[],[f609,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    v3_ordinal1(sK1) | ~spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f609,plain,(
% 0.21/0.51    ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | (spl6_3 | ~spl6_4 | ~spl6_70 | ~spl6_86)),
% 0.21/0.51    inference(subsumption_resolution,[],[f608,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    sK0 != sK1 | spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f608,plain,(
% 0.21/0.51    sK0 = sK1 | ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | (~spl6_4 | ~spl6_70 | ~spl6_86)),
% 0.21/0.51    inference(subsumption_resolution,[],[f607,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f607,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | sK0 = sK1 | ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | (~spl6_70 | ~spl6_86)),
% 0.21/0.51    inference(superposition,[],[f494,f602])).
% 0.21/0.51  fof(f602,plain,(
% 0.21/0.51    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl6_86),
% 0.21/0.51    inference(avatar_component_clause,[],[f601])).
% 0.21/0.51  fof(f494,plain,(
% 0.21/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),X0)) | sK0 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK0,X0)) ) | ~spl6_70),
% 0.21/0.51    inference(avatar_component_clause,[],[f493])).
% 0.21/0.51  fof(f603,plain,(
% 0.21/0.51    spl6_86 | ~spl6_13 | ~spl6_78),
% 0.21/0.51    inference(avatar_split_clause,[],[f560,f552,f125,f601])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl6_13 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.51  fof(f552,plain,(
% 0.21/0.51    spl6_78 <=> r1_tarski(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 0.21/0.51  fof(f560,plain,(
% 0.21/0.51    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | (~spl6_13 | ~spl6_78)),
% 0.21/0.51    inference(resolution,[],[f553,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) ) | ~spl6_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f553,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0) | ~spl6_78),
% 0.21/0.51    inference(avatar_component_clause,[],[f552])).
% 0.21/0.51  fof(f554,plain,(
% 0.21/0.51    spl6_78 | ~spl6_29 | ~spl6_76),
% 0.21/0.51    inference(avatar_split_clause,[],[f538,f530,f205,f552])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    spl6_29 <=> ! [X3,X0,X2] : (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.51  fof(f530,plain,(
% 0.21/0.51    spl6_76 <=> r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK3(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 0.21/0.51  fof(f538,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0) | (~spl6_29 | ~spl6_76)),
% 0.21/0.51    inference(resolution,[],[f531,f206])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) | r1_tarski(X2,X3)) ) | ~spl6_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f205])).
% 0.21/0.51  fof(f531,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK3(sK0))) | ~spl6_76),
% 0.21/0.51    inference(avatar_component_clause,[],[f530])).
% 0.21/0.51  fof(f532,plain,(
% 0.21/0.51    spl6_76 | ~spl6_41 | ~spl6_68),
% 0.21/0.51    inference(avatar_split_clause,[],[f486,f466,f291,f530])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    spl6_41 <=> r2_hidden(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.51  fof(f466,plain,(
% 0.21/0.51    spl6_68 <=> ! [X1] : (r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK3(sK0))) | ~r2_hidden(X1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.21/0.51  fof(f486,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK3(sK0))) | (~spl6_41 | ~spl6_68)),
% 0.21/0.51    inference(resolution,[],[f292,f467])).
% 0.21/0.51  fof(f467,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK3(sK0)))) ) | ~spl6_68),
% 0.21/0.51    inference(avatar_component_clause,[],[f466])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    r2_hidden(sK1,sK0) | ~spl6_41),
% 0.21/0.51    inference(avatar_component_clause,[],[f291])).
% 0.21/0.51  fof(f495,plain,(
% 0.21/0.51    spl6_70 | ~spl6_28 | ~spl6_34 | ~spl6_53),
% 0.21/0.51    inference(avatar_split_clause,[],[f376,f369,f245,f201,f493])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl6_28 <=> ! [X1] : (~v3_ordinal1(X1) | r2_hidden(sK0,X1) | sK0 = X1 | r2_hidden(X1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl6_34 <=> ! [X0] : (r2_hidden(sK0,X0) | sK0 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK0),X0) = X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    spl6_53 <=> ! [X1] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1))) | ~r2_hidden(X1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.21/0.51  fof(f376,plain,(
% 0.21/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),X0)) | sK0 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK0,X0)) ) | (~spl6_28 | ~spl6_34 | ~spl6_53)),
% 0.21/0.51    inference(subsumption_resolution,[],[f374,f202])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(X1,sK0) | r2_hidden(sK0,X1) | sK0 = X1 | ~v3_ordinal1(X1)) ) | ~spl6_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f201])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),X0)) | ~r2_hidden(X0,sK0) | sK0 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK0,X0)) ) | (~spl6_34 | ~spl6_53)),
% 0.21/0.51    inference(superposition,[],[f370,f246])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X0] : (k1_wellord1(k1_wellord2(sK0),X0) = X0 | sK0 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK0,X0)) ) | ~spl6_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f245])).
% 0.21/0.51  fof(f370,plain,(
% 0.21/0.51    ( ! [X1] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1))) | ~r2_hidden(X1,sK0)) ) | ~spl6_53),
% 0.21/0.51    inference(avatar_component_clause,[],[f369])).
% 0.21/0.51  fof(f479,plain,(
% 0.21/0.51    ~spl6_4 | ~spl6_13 | spl6_59 | ~spl6_67),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f478])).
% 0.21/0.51  fof(f478,plain,(
% 0.21/0.51    $false | (~spl6_4 | ~spl6_13 | spl6_59 | ~spl6_67)),
% 0.21/0.51    inference(subsumption_resolution,[],[f474,f90])).
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | (~spl6_13 | spl6_59 | ~spl6_67)),
% 0.21/0.51    inference(backward_demodulation,[],[f408,f472])).
% 0.21/0.51  fof(f472,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | (~spl6_13 | ~spl6_67)),
% 0.21/0.51    inference(resolution,[],[f463,f126])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1) | ~spl6_67),
% 0.21/0.51    inference(avatar_component_clause,[],[f462])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    spl6_67 <=> r1_tarski(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    ~r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1)) | spl6_59),
% 0.21/0.51    inference(avatar_component_clause,[],[f407])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    spl6_59 <=> r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.21/0.51  fof(f477,plain,(
% 0.21/0.51    ~spl6_5 | ~spl6_13 | spl6_58 | ~spl6_67),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f476])).
% 0.21/0.51  fof(f476,plain,(
% 0.21/0.51    $false | (~spl6_5 | ~spl6_13 | spl6_58 | ~spl6_67)),
% 0.21/0.51    inference(subsumption_resolution,[],[f473,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) ) | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl6_5 <=> ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f473,plain,(
% 0.21/0.51    ~v1_relat_1(k1_wellord2(sK0)) | (~spl6_13 | spl6_58 | ~spl6_67)),
% 0.21/0.51    inference(backward_demodulation,[],[f405,f472])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    ~v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0)) | spl6_58),
% 0.21/0.51    inference(avatar_component_clause,[],[f404])).
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    spl6_58 <=> v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.21/0.51  fof(f468,plain,(
% 0.21/0.51    spl6_68 | ~spl6_2 | ~spl6_60),
% 0.21/0.51    inference(avatar_split_clause,[],[f415,f411,f81,f466])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl6_2 <=> v3_ordinal1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f411,plain,(
% 0.21/0.51    spl6_60 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK3(X0))) | ~v3_ordinal1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 0.21/0.51  fof(f415,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK3(sK0))) | ~r2_hidden(X1,sK0)) ) | (~spl6_2 | ~spl6_60)),
% 0.21/0.51    inference(resolution,[],[f412,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    v3_ordinal1(sK0) | ~spl6_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f412,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK3(X0))) | ~r2_hidden(X1,X0)) ) | ~spl6_60),
% 0.21/0.51    inference(avatar_component_clause,[],[f411])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    spl6_67 | ~spl6_29 | ~spl6_65),
% 0.21/0.51    inference(avatar_split_clause,[],[f456,f447,f205,f462])).
% 0.21/0.51  fof(f447,plain,(
% 0.21/0.51    spl6_65 <=> r2_hidden(k4_tarski(sK0,sK1),k1_wellord2(sK3(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.21/0.51  fof(f456,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1) | (~spl6_29 | ~spl6_65)),
% 0.21/0.51    inference(resolution,[],[f448,f206])).
% 0.21/0.51  fof(f448,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK0,sK1),k1_wellord2(sK3(sK1))) | ~spl6_65),
% 0.21/0.51    inference(avatar_component_clause,[],[f447])).
% 0.21/0.51  fof(f449,plain,(
% 0.21/0.51    spl6_65 | ~spl6_47 | ~spl6_62),
% 0.21/0.51    inference(avatar_split_clause,[],[f439,f426,f327,f447])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    spl6_62 <=> ! [X0] : (r2_hidden(k4_tarski(X0,sK1),k1_wellord2(sK3(sK1))) | ~r2_hidden(X0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.21/0.51  fof(f439,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK0,sK1),k1_wellord2(sK3(sK1))) | (~spl6_47 | ~spl6_62)),
% 0.21/0.51    inference(resolution,[],[f427,f328])).
% 0.21/0.51  fof(f328,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | ~spl6_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f327])).
% 0.21/0.51  fof(f427,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k4_tarski(X0,sK1),k1_wellord2(sK3(sK1)))) ) | ~spl6_62),
% 0.21/0.51    inference(avatar_component_clause,[],[f426])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    spl6_62 | ~spl6_1 | ~spl6_60),
% 0.21/0.51    inference(avatar_split_clause,[],[f414,f411,f77,f426])).
% 0.21/0.51  fof(f414,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK1),k1_wellord2(sK3(sK1))) | ~r2_hidden(X0,sK1)) ) | (~spl6_1 | ~spl6_60)),
% 0.21/0.51    inference(resolution,[],[f412,f78])).
% 0.21/0.51  fof(f413,plain,(
% 0.21/0.51    spl6_60 | ~spl6_5 | ~spl6_16 | ~spl6_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f299,f172,f137,f93,f411])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl6_16 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k1_wellord1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl6_23 <=> ! [X0] : (~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK3(X0))) | ~v3_ordinal1(X0)) ) | (~spl6_5 | ~spl6_16 | ~spl6_23)),
% 0.21/0.51    inference(subsumption_resolution,[],[f297,f94])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK3(X0))) | ~v1_relat_1(k1_wellord2(sK3(X0))) | ~v3_ordinal1(X0)) ) | (~spl6_16 | ~spl6_23)),
% 0.21/0.51    inference(superposition,[],[f138,f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X0] : (k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0 | ~v3_ordinal1(X0)) ) | ~spl6_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f172])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~v1_relat_1(X0)) ) | ~spl6_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f137])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    ~spl6_58 | ~spl6_59 | ~spl6_5 | ~spl6_12 | spl6_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f387,f378,f121,f93,f407,f404])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl6_12 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.51  fof(f378,plain,(
% 0.21/0.51    spl6_54 <=> r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.21/0.51  fof(f387,plain,(
% 0.21/0.51    ~r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1)) | ~v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0)) | (~spl6_5 | ~spl6_12 | spl6_54)),
% 0.21/0.51    inference(subsumption_resolution,[],[f386,f94])).
% 0.21/0.51  fof(f386,plain,(
% 0.21/0.51    ~v1_relat_1(k1_wellord2(sK1)) | ~r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1)) | ~v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0)) | (~spl6_12 | spl6_54)),
% 0.21/0.51    inference(resolution,[],[f379,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X0)) ) | ~spl6_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | spl6_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f378])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    ~spl6_54 | ~spl6_47 | ~spl6_49 | ~spl6_51),
% 0.21/0.51    inference(avatar_split_clause,[],[f367,f355,f344,f327,f378])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    spl6_49 <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    spl6_51 <=> ! [X0] : (~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) | ~r2_hidden(X0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | (~spl6_47 | ~spl6_49 | ~spl6_51)),
% 0.21/0.51    inference(subsumption_resolution,[],[f364,f328])).
% 0.21/0.51  fof(f364,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | (~spl6_49 | ~spl6_51)),
% 0.21/0.51    inference(superposition,[],[f356,f345])).
% 0.21/0.51  fof(f345,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl6_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f344])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) | ~r2_hidden(X0,sK1)) ) | ~spl6_51),
% 0.21/0.51    inference(avatar_component_clause,[],[f355])).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    spl6_53 | ~spl6_2 | ~spl6_46),
% 0.21/0.51    inference(avatar_split_clause,[],[f331,f323,f81,f369])).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    spl6_46 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    ( ! [X1] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1))) | ~r2_hidden(X1,sK0)) ) | (~spl6_2 | ~spl6_46)),
% 0.21/0.51    inference(resolution,[],[f324,f82])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~r2_hidden(X1,X0)) ) | ~spl6_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f323])).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    spl6_51 | ~spl6_1 | ~spl6_46),
% 0.21/0.51    inference(avatar_split_clause,[],[f330,f323,f77,f355])).
% 0.21/0.51  fof(f330,plain,(
% 0.21/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) | ~r2_hidden(X0,sK1)) ) | (~spl6_1 | ~spl6_46)),
% 0.21/0.51    inference(resolution,[],[f324,f78])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    spl6_49 | ~spl6_1 | ~spl6_2 | ~spl6_18 | ~spl6_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f339,f327,f149,f81,f77,f344])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl6_18 <=> ! [X1,X0] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | (~spl6_1 | ~spl6_2 | ~spl6_18 | ~spl6_47)),
% 0.21/0.51    inference(subsumption_resolution,[],[f338,f82])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | (~spl6_1 | ~spl6_18 | ~spl6_47)),
% 0.21/0.51    inference(subsumption_resolution,[],[f337,f78])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | (~spl6_18 | ~spl6_47)),
% 0.21/0.51    inference(resolution,[],[f328,f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X1),X0) = X0) ) | ~spl6_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f149])).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    spl6_47 | ~spl6_1 | spl6_3 | ~spl6_20 | ~spl6_44),
% 0.21/0.51    inference(avatar_split_clause,[],[f321,f307,f157,f85,f77,f327])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl6_20 <=> ! [X1,X0,X2] : (r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    spl6_44 <=> ! [X0] : (r2_hidden(k4_tarski(X0,sK0),k1_wellord2(sK1)) | r2_hidden(sK0,X0) | sK0 = X0 | ~v3_ordinal1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | (~spl6_1 | spl6_3 | ~spl6_20 | ~spl6_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f320,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | r2_hidden(X1,X2)) ) | ~spl6_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f320,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK1)) | (~spl6_1 | spl6_3 | ~spl6_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f317,f86])).
% 0.21/0.51  fof(f317,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | sK0 = sK1 | r2_hidden(k4_tarski(sK1,sK0),k1_wellord2(sK1)) | (~spl6_1 | ~spl6_44)),
% 0.21/0.51    inference(resolution,[],[f308,f78])).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK0,X0) | sK0 = X0 | r2_hidden(k4_tarski(X0,sK0),k1_wellord2(sK1))) ) | ~spl6_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f307])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    spl6_46 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f238,f183,f109,f97,f93,f323])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl6_6 <=> ! [X0] : (~v3_ordinal1(X0) | v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl6_9 <=> ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl6_25 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_25)),
% 0.21/0.51    inference(forward_demodulation,[],[f237,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) ) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f236,f94])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) ) | (~spl6_6 | ~spl6_25)),
% 0.21/0.51    inference(resolution,[],[f184,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) ) | ~spl6_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) ) | ~spl6_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f183])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    spl6_44 | ~spl6_28 | ~spl6_42),
% 0.21/0.51    inference(avatar_split_clause,[],[f305,f294,f201,f307])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    spl6_42 <=> ! [X1] : (r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK1)) | ~r2_hidden(X1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),k1_wellord2(sK1)) | r2_hidden(sK0,X0) | sK0 = X0 | ~v3_ordinal1(X0)) ) | (~spl6_28 | ~spl6_42)),
% 0.21/0.51    inference(resolution,[],[f295,f202])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK1))) ) | ~spl6_42),
% 0.21/0.51    inference(avatar_component_clause,[],[f294])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    spl6_41 | spl6_42 | ~spl6_2 | spl6_3 | ~spl6_40),
% 0.21/0.51    inference(avatar_split_clause,[],[f286,f278,f85,f81,f294,f291])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    spl6_40 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK1)) | sK1 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK1)) | ~r2_hidden(X1,sK0) | r2_hidden(sK1,sK0)) ) | (~spl6_2 | spl6_3 | ~spl6_40)),
% 0.21/0.51    inference(subsumption_resolution,[],[f284,f86])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(k4_tarski(X1,sK0),k1_wellord2(sK1)) | sK0 = sK1 | ~r2_hidden(X1,sK0) | r2_hidden(sK1,sK0)) ) | (~spl6_2 | ~spl6_40)),
% 0.21/0.51    inference(resolution,[],[f279,f82])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK1)) | sK1 = X0 | ~r2_hidden(X1,X0) | r2_hidden(sK1,X0)) ) | ~spl6_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f278])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    spl6_40 | ~spl6_5 | ~spl6_16 | ~spl6_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f226,f217,f137,f93,f278])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    spl6_31 <=> ! [X0] : (r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK1)) | sK1 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK1,X0)) ) | (~spl6_5 | ~spl6_16 | ~spl6_31)),
% 0.21/0.51    inference(subsumption_resolution,[],[f224,f94])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r2_hidden(k4_tarski(X1,X0),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK1)) | sK1 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK1,X0)) ) | (~spl6_16 | ~spl6_31)),
% 0.21/0.51    inference(superposition,[],[f138,f218])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ( ! [X0] : (k1_wellord1(k1_wellord2(sK1),X0) = X0 | sK1 = X0 | ~v3_ordinal1(X0) | r2_hidden(sK1,X0)) ) | ~spl6_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f217])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    spl6_34 | ~spl6_2 | ~spl6_18 | ~spl6_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f211,f201,f149,f81,f245])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK0,X0) | sK0 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK0),X0) = X0) ) | (~spl6_2 | ~spl6_18 | ~spl6_28)),
% 0.21/0.51    inference(subsumption_resolution,[],[f210,f82])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK0,X0) | sK0 = X0 | ~v3_ordinal1(X0) | ~v3_ordinal1(sK0) | k1_wellord1(k1_wellord2(sK0),X0) = X0) ) | (~spl6_18 | ~spl6_28)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f208])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK0,X0) | sK0 = X0 | ~v3_ordinal1(X0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK0),X0) = X0) ) | (~spl6_18 | ~spl6_28)),
% 0.21/0.51    inference(resolution,[],[f202,f150])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    spl6_31 | ~spl6_1 | ~spl6_18 | ~spl6_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f193,f179,f149,f77,f217])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl6_24 <=> ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK1,X0) | sK1 = X0 | r2_hidden(X0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0) ) | (~spl6_1 | ~spl6_18 | ~spl6_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f192,f78])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0) | ~v3_ordinal1(sK1) | k1_wellord1(k1_wellord2(sK1),X0) = X0) ) | (~spl6_18 | ~spl6_24)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0) ) | (~spl6_18 | ~spl6_24)),
% 0.21/0.51    inference(resolution,[],[f180,f150])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,sK1) | r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0)) ) | ~spl6_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f179])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    spl6_29 | ~spl6_17 | ~spl6_20 | ~spl6_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f199,f195,f157,f145,f205])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl6_17 <=> ! [X1,X0,X2] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    spl6_27 <=> ! [X3,X0,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) ) | (~spl6_17 | ~spl6_20 | ~spl6_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f158])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) ) | (~spl6_17 | ~spl6_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f196,f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | r2_hidden(X0,X2)) ) | ~spl6_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) ) | ~spl6_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f195])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl6_28 | ~spl6_2 | ~spl6_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f176,f153,f81,f201])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl6_19 <=> ! [X1,X0] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(sK0,X1) | sK0 = X1 | r2_hidden(X1,sK0)) ) | (~spl6_2 | ~spl6_19)),
% 0.21/0.51    inference(resolution,[],[f154,f82])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) ) | ~spl6_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    spl6_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f74,f195])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl6_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f183])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    spl6_24 | ~spl6_1 | ~spl6_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f175,f153,f77,f179])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK1,X0) | sK1 = X0 | r2_hidden(X0,sK1)) ) | (~spl6_1 | ~spl6_19)),
% 0.21/0.51    inference(resolution,[],[f154,f78])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl6_23 | ~spl6_7 | ~spl6_10 | ~spl6_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f170,f149,f113,f101,f172])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl6_7 <=> ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(sK3(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl6_10 <=> ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK3(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0) ) | (~spl6_7 | ~spl6_10 | ~spl6_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f169,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0] : (v3_ordinal1(sK3(X0)) | ~v3_ordinal1(X0)) ) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(sK3(X0)) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0) ) | (~spl6_10 | ~spl6_18)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f168])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(sK3(X0)) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK3(X0)),X0) = X0 | ~v3_ordinal1(X0)) ) | (~spl6_10 | ~spl6_18)),
% 0.21/0.51    inference(resolution,[],[f150,f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,sK3(X0)) | ~v3_ordinal1(X0)) ) | ~spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl6_20 | ~spl6_5 | ~spl6_9 | ~spl6_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f143,f133,f109,f93,f157])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl6_15 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))) ) | (~spl6_5 | ~spl6_9 | ~spl6_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f142,f110])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | r2_hidden(X1,k3_relat_1(k1_wellord2(X2)))) ) | (~spl6_5 | ~spl6_15)),
% 0.21/0.51    inference(resolution,[],[f134,f94])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2))) ) | ~spl6_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f133])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl6_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f153])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl6_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f149])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl6_17 | ~spl6_5 | ~spl6_9 | ~spl6_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f141,f129,f109,f93,f145])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl6_14 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))) ) | (~spl6_5 | ~spl6_9 | ~spl6_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f140,f110])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | r2_hidden(X0,k3_relat_1(k1_wellord2(X2)))) ) | (~spl6_5 | ~spl6_14)),
% 0.21/0.51    inference(resolution,[],[f130,f94])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2))) ) | ~spl6_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl6_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f62,f137])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl6_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f133])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl6_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f59,f129])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    spl6_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f58,f125])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl6_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f121])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f113])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK3(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (v4_ordinal1(X1) & r2_hidden(X0,X1) & v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ? [X1] : (v4_ordinal1(X1) & r2_hidden(X0,X1) & v3_ordinal1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_ordinal1)).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f73,f109])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f65,f36])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.51    inference(equality_resolution,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f101])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(sK3(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f97])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(X0) | v2_wellord1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f93])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f89])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f85])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    sK0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v3_ordinal1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f77])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v3_ordinal1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26940)------------------------------
% 0.21/0.51  % (26940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26940)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26940)Memory used [KB]: 11001
% 0.21/0.51  % (26940)Time elapsed: 0.093 s
% 0.21/0.51  % (26940)------------------------------
% 0.21/0.51  % (26940)------------------------------
% 0.21/0.51  % (26930)Success in time 0.155 s
%------------------------------------------------------------------------------
