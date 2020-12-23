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
% DateTime   : Thu Dec  3 13:23:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 341 expanded)
%              Number of leaves         :   55 ( 163 expanded)
%              Depth                    :    7
%              Number of atoms          :  621 (1354 expanded)
%              Number of equality atoms :   78 ( 182 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f113,f118,f122,f130,f151,f155,f159,f163,f169,f180,f184,f196,f220,f232,f236,f241,f271,f297,f338,f343,f358,f369,f458,f582,f591,f597,f760,f765,f785])).

fof(f785,plain,
    ( spl5_43
    | ~ spl5_63
    | ~ spl5_65
    | ~ spl5_77 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | spl5_43
    | ~ spl5_63
    | ~ spl5_65
    | ~ spl5_77 ),
    inference(subsumption_resolution,[],[f654,f769])).

fof(f769,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl5_43
    | ~ spl5_77 ),
    inference(unit_resulting_resolution,[],[f342,f764])).

fof(f764,plain,
    ( ! [X8,X7] :
        ( k4_xboole_0(X7,X8) = X7
        | ~ r1_xboole_0(X7,X8) )
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f763])).

fof(f763,plain,
    ( spl5_77
  <=> ! [X7,X8] :
        ( k4_xboole_0(X7,X8) = X7
        | ~ r1_xboole_0(X7,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f342,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl5_43
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f654,plain,
    ( r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl5_63
    | ~ spl5_65 ),
    inference(unit_resulting_resolution,[],[f596,f581])).

fof(f581,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl5_63
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f596,plain,
    ( r1_xboole_0(k1_tarski(k1_xboole_0),sK1)
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl5_65
  <=> r1_xboole_0(k1_tarski(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f765,plain,
    ( spl5_77
    | ~ spl5_64
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f761,f758,f589,f763])).

fof(f589,plain,
    ( spl5_64
  <=> ! [X6] : k5_xboole_0(X6,k1_xboole_0) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f758,plain,
    ( spl5_76
  <=> ! [X7,X8] :
        ( k4_xboole_0(X7,X8) = k5_xboole_0(X7,k1_xboole_0)
        | ~ r1_xboole_0(X7,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f761,plain,
    ( ! [X8,X7] :
        ( k4_xboole_0(X7,X8) = X7
        | ~ r1_xboole_0(X7,X8) )
    | ~ spl5_64
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f759,f590])).

fof(f590,plain,
    ( ! [X6] : k5_xboole_0(X6,k1_xboole_0) = X6
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f589])).

fof(f759,plain,
    ( ! [X8,X7] :
        ( k4_xboole_0(X7,X8) = k5_xboole_0(X7,k1_xboole_0)
        | ~ r1_xboole_0(X7,X8) )
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f758])).

fof(f760,plain,
    ( spl5_76
    | ~ spl5_24
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f349,f336,f182,f758])).

fof(f182,plain,
    ( spl5_24
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f336,plain,
    ( spl5_42
  <=> ! [X3,X2] :
        ( ~ r1_xboole_0(X2,X3)
        | k1_xboole_0 = k3_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f349,plain,
    ( ! [X8,X7] :
        ( k4_xboole_0(X7,X8) = k5_xboole_0(X7,k1_xboole_0)
        | ~ r1_xboole_0(X7,X8) )
    | ~ spl5_24
    | ~ spl5_42 ),
    inference(superposition,[],[f183,f337])).

fof(f337,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f336])).

fof(f183,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f182])).

fof(f597,plain,
    ( spl5_65
    | ~ spl5_20
    | spl5_54 ),
    inference(avatar_split_clause,[],[f459,f455,f161,f594])).

fof(f161,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f455,plain,
    ( spl5_54
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f459,plain,
    ( r1_xboole_0(k1_tarski(k1_xboole_0),sK1)
    | ~ spl5_20
    | spl5_54 ),
    inference(unit_resulting_resolution,[],[f457,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f457,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl5_54 ),
    inference(avatar_component_clause,[],[f455])).

fof(f591,plain,
    ( spl5_64
    | ~ spl5_12
    | ~ spl5_37
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f374,f367,f295,f128,f589])).

fof(f128,plain,
    ( spl5_12
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f295,plain,
    ( spl5_37
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f367,plain,
    ( spl5_45
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f374,plain,
    ( ! [X6] : k5_xboole_0(X6,k1_xboole_0) = X6
    | ~ spl5_12
    | ~ spl5_37
    | ~ spl5_45 ),
    inference(forward_demodulation,[],[f373,f129])).

fof(f129,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f373,plain,
    ( ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)
    | ~ spl5_37
    | ~ spl5_45 ),
    inference(superposition,[],[f368,f296])).

fof(f296,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f295])).

fof(f368,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f367])).

fof(f582,plain,
    ( spl5_63
    | ~ spl5_26
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f359,f356,f194,f580])).

fof(f194,plain,
    ( spl5_26
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f356,plain,
    ( spl5_44
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f359,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl5_26
    | ~ spl5_44 ),
    inference(resolution,[],[f357,f195])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f194])).

fof(f357,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f356])).

fof(f458,plain,
    ( ~ spl5_54
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_29
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f248,f234,f229,f110,f105,f100,f95,f90,f455])).

fof(f90,plain,
    ( spl5_4
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f95,plain,
    ( spl5_5
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f100,plain,
    ( spl5_6
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f105,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f110,plain,
    ( spl5_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f229,plain,
    ( spl5_29
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f234,plain,
    ( spl5_30
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f248,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_29
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f112,f92,f97,f102,f107,f231,f235])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        | ~ r2_hidden(X2,X1)
        | ~ v1_xboole_0(X2)
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
        | v1_xboole_0(X0) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f234])).

fof(f231,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f229])).

fof(f107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f102,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f97,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f92,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f112,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f369,plain,
    ( spl5_45
    | ~ spl5_19
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f205,f182,f157,f367])).

fof(f157,plain,
    ( spl5_19
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f205,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))
    | ~ spl5_19
    | ~ spl5_24 ),
    inference(superposition,[],[f183,f158])).

fof(f158,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f157])).

fof(f358,plain,
    ( spl5_44
    | ~ spl5_19
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f191,f167,f157,f356])).

fof(f167,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_19
    | ~ spl5_21 ),
    inference(superposition,[],[f168,f158])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f167])).

fof(f343,plain,
    ( ~ spl5_43
    | spl5_9
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f272,f268,f115,f340])).

fof(f115,plain,
    ( spl5_9
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f268,plain,
    ( spl5_34
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f272,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl5_9
    | ~ spl5_34 ),
    inference(superposition,[],[f117,f270])).

fof(f270,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f268])).

fof(f117,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f338,plain,
    ( spl5_42
    | ~ spl5_18
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f190,f167,f153,f336])).

fof(f153,plain,
    ( spl5_18
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f190,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | k1_xboole_0 = k3_xboole_0(X2,X3) )
    | ~ spl5_18
    | ~ spl5_21 ),
    inference(resolution,[],[f168,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f297,plain,
    ( spl5_37
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f204,f178,f128,f120,f295])).

fof(f120,plain,
    ( spl5_10
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f178,plain,
    ( spl5_23
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f204,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f199,f129])).

fof(f199,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_10
    | ~ spl5_23 ),
    inference(superposition,[],[f179,f121])).

fof(f121,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f179,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f178])).

fof(f271,plain,
    ( spl5_34
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_27
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f247,f239,f218,f105,f95,f90,f85,f80,f75,f268])).

fof(f75,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,
    ( spl5_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f85,plain,
    ( spl5_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f218,plain,
    ( spl5_27
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f239,plain,
    ( spl5_31
  <=> ! [X1,X0] :
        ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f247,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_27
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f242,f221])).

fof(f221,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl5_7
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f107,f219])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f218])).

fof(f242,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f92,f97,f107,f240])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f239])).

fof(f87,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f82,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f77,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f241,plain,(
    spl5_31 ),
    inference(avatar_split_clause,[],[f60,f239])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f236,plain,(
    spl5_30 ),
    inference(avatar_split_clause,[],[f73,f234])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f58,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f232,plain,
    ( ~ spl5_29
    | spl5_1
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f170,f149,f80,f75,f229])).

fof(f149,plain,
    ( spl5_17
  <=> ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f170,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f77,f82,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f220,plain,(
    spl5_27 ),
    inference(avatar_split_clause,[],[f72,f218])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f196,plain,(
    spl5_26 ),
    inference(avatar_split_clause,[],[f69,f194])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f184,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f67,f182])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f180,plain,(
    spl5_23 ),
    inference(avatar_split_clause,[],[f66,f178])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f169,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f70,f167])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f163,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f71,f161])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f159,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f65,f157])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f155,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f63,f153])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK3(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK3(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f151,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f59,f149])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f130,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f56,f128])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f122,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f54,f120])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f118,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f52,f115])).

fof(f52,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f113,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f53,f110])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f108,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f51,f105])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f36])).

fof(f103,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f48,f100])).

fof(f48,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f50,f95])).

fof(f50,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f49,f90])).

fof(f49,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:34:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (10655)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (10657)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (10651)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (10657)Refutation not found, incomplete strategy% (10657)------------------------------
% 0.21/0.47  % (10657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (10657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (10657)Memory used [KB]: 10618
% 0.21/0.47  % (10657)Time elapsed: 0.027 s
% 0.21/0.47  % (10657)------------------------------
% 0.21/0.47  % (10657)------------------------------
% 0.21/0.47  % (10646)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (10650)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (10645)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (10659)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (10647)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (10656)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (10658)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (10648)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (10662)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (10654)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (10653)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (10652)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (10661)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (10651)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f787,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f113,f118,f122,f130,f151,f155,f159,f163,f169,f180,f184,f196,f220,f232,f236,f241,f271,f297,f338,f343,f358,f369,f458,f582,f591,f597,f760,f765,f785])).
% 0.21/0.50  fof(f785,plain,(
% 0.21/0.50    spl5_43 | ~spl5_63 | ~spl5_65 | ~spl5_77),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f784])).
% 0.21/0.50  fof(f784,plain,(
% 0.21/0.50    $false | (spl5_43 | ~spl5_63 | ~spl5_65 | ~spl5_77)),
% 0.21/0.50    inference(subsumption_resolution,[],[f654,f769])).
% 0.21/0.50  fof(f769,plain,(
% 0.21/0.50    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl5_43 | ~spl5_77)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f342,f764])).
% 0.21/0.50  fof(f764,plain,(
% 0.21/0.50    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = X7 | ~r1_xboole_0(X7,X8)) ) | ~spl5_77),
% 0.21/0.50    inference(avatar_component_clause,[],[f763])).
% 0.21/0.50  fof(f763,plain,(
% 0.21/0.50    spl5_77 <=> ! [X7,X8] : (k4_xboole_0(X7,X8) = X7 | ~r1_xboole_0(X7,X8))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl5_43),
% 0.21/0.50    inference(avatar_component_clause,[],[f340])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    spl5_43 <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.21/0.50  fof(f654,plain,(
% 0.21/0.50    r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (~spl5_63 | ~spl5_65)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f596,f581])).
% 0.21/0.50  fof(f581,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl5_63),
% 0.21/0.50    inference(avatar_component_clause,[],[f580])).
% 0.21/0.50  fof(f580,plain,(
% 0.21/0.50    spl5_63 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 0.21/0.50  fof(f596,plain,(
% 0.21/0.50    r1_xboole_0(k1_tarski(k1_xboole_0),sK1) | ~spl5_65),
% 0.21/0.50    inference(avatar_component_clause,[],[f594])).
% 0.21/0.50  fof(f594,plain,(
% 0.21/0.50    spl5_65 <=> r1_xboole_0(k1_tarski(k1_xboole_0),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 0.21/0.50  fof(f765,plain,(
% 0.21/0.50    spl5_77 | ~spl5_64 | ~spl5_76),
% 0.21/0.50    inference(avatar_split_clause,[],[f761,f758,f589,f763])).
% 0.21/0.50  fof(f589,plain,(
% 0.21/0.50    spl5_64 <=> ! [X6] : k5_xboole_0(X6,k1_xboole_0) = X6),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 0.21/0.50  fof(f758,plain,(
% 0.21/0.50    spl5_76 <=> ! [X7,X8] : (k4_xboole_0(X7,X8) = k5_xboole_0(X7,k1_xboole_0) | ~r1_xboole_0(X7,X8))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 0.21/0.50  fof(f761,plain,(
% 0.21/0.50    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = X7 | ~r1_xboole_0(X7,X8)) ) | (~spl5_64 | ~spl5_76)),
% 0.21/0.50    inference(forward_demodulation,[],[f759,f590])).
% 0.21/0.50  fof(f590,plain,(
% 0.21/0.50    ( ! [X6] : (k5_xboole_0(X6,k1_xboole_0) = X6) ) | ~spl5_64),
% 0.21/0.50    inference(avatar_component_clause,[],[f589])).
% 0.21/0.50  fof(f759,plain,(
% 0.21/0.50    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(X7,k1_xboole_0) | ~r1_xboole_0(X7,X8)) ) | ~spl5_76),
% 0.21/0.50    inference(avatar_component_clause,[],[f758])).
% 0.21/0.50  fof(f760,plain,(
% 0.21/0.50    spl5_76 | ~spl5_24 | ~spl5_42),
% 0.21/0.50    inference(avatar_split_clause,[],[f349,f336,f182,f758])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl5_24 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    spl5_42 <=> ! [X3,X2] : (~r1_xboole_0(X2,X3) | k1_xboole_0 = k3_xboole_0(X2,X3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(X7,k1_xboole_0) | ~r1_xboole_0(X7,X8)) ) | (~spl5_24 | ~spl5_42)),
% 0.21/0.50    inference(superposition,[],[f183,f337])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,X3) | ~r1_xboole_0(X2,X3)) ) | ~spl5_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f336])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl5_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f597,plain,(
% 0.21/0.50    spl5_65 | ~spl5_20 | spl5_54),
% 0.21/0.50    inference(avatar_split_clause,[],[f459,f455,f161,f594])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl5_20 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.50  fof(f455,plain,(
% 0.21/0.50    spl5_54 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.21/0.50  fof(f459,plain,(
% 0.21/0.50    r1_xboole_0(k1_tarski(k1_xboole_0),sK1) | (~spl5_20 | spl5_54)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f457,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl5_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f161])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    ~r2_hidden(k1_xboole_0,sK1) | spl5_54),
% 0.21/0.50    inference(avatar_component_clause,[],[f455])).
% 0.21/0.50  fof(f591,plain,(
% 0.21/0.50    spl5_64 | ~spl5_12 | ~spl5_37 | ~spl5_45),
% 0.21/0.50    inference(avatar_split_clause,[],[f374,f367,f295,f128,f589])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl5_12 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    spl5_37 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    spl5_45 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ( ! [X6] : (k5_xboole_0(X6,k1_xboole_0) = X6) ) | (~spl5_12 | ~spl5_37 | ~spl5_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f373,f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f128])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)) ) | (~spl5_37 | ~spl5_45)),
% 0.21/0.50    inference(superposition,[],[f368,f296])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl5_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f295])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) ) | ~spl5_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f367])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    spl5_63 | ~spl5_26 | ~spl5_44),
% 0.21/0.50    inference(avatar_split_clause,[],[f359,f356,f194,f580])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    spl5_26 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    spl5_44 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | (~spl5_26 | ~spl5_44)),
% 0.21/0.50    inference(resolution,[],[f357,f195])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl5_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f194])).
% 0.21/0.50  fof(f357,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f356])).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    ~spl5_54 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | spl5_29 | ~spl5_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f248,f234,f229,f110,f105,f100,f95,f90,f455])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl5_4 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl5_5 <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl5_6 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl5_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl5_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    spl5_29 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    spl5_30 <=> ! [X1,X0,X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ~r2_hidden(k1_xboole_0,sK1) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | spl5_29 | ~spl5_30)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f112,f92,f97,f102,f107,f231,f235])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X0)) ) | ~spl5_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f234])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_struct_0(sK0)) | spl5_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f229])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f95])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    spl5_45 | ~spl5_19 | ~spl5_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f205,f182,f157,f367])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl5_19 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) ) | (~spl5_19 | ~spl5_24)),
% 0.21/0.50    inference(superposition,[],[f183,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl5_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f157])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    spl5_44 | ~spl5_19 | ~spl5_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f191,f167,f157,f356])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl5_21 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) ) | (~spl5_19 | ~spl5_21)),
% 0.21/0.50    inference(superposition,[],[f168,f158])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f167])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    ~spl5_43 | spl5_9 | ~spl5_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f272,f268,f115,f340])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl5_9 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    spl5_34 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl5_9 | ~spl5_34)),
% 0.21/0.50    inference(superposition,[],[f117,f270])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~spl5_34),
% 0.21/0.50    inference(avatar_component_clause,[],[f268])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    spl5_42 | ~spl5_18 | ~spl5_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f190,f167,f153,f336])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl5_18 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | k1_xboole_0 = k3_xboole_0(X2,X3)) ) | (~spl5_18 | ~spl5_21)),
% 0.21/0.50    inference(resolution,[],[f168,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f153])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    spl5_37 | ~spl5_10 | ~spl5_12 | ~spl5_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f204,f178,f128,f120,f295])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl5_10 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl5_23 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl5_10 | ~spl5_12 | ~spl5_23)),
% 0.21/0.50    inference(forward_demodulation,[],[f199,f129])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl5_10 | ~spl5_23)),
% 0.21/0.50    inference(superposition,[],[f179,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl5_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f178])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    spl5_34 | spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_27 | ~spl5_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f247,f239,f218,f105,f95,f90,f85,f80,f75,f268])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl5_2 <=> l1_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl5_3 <=> v1_xboole_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    spl5_27 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    spl5_31 <=> ! [X1,X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_27 | ~spl5_31)),
% 0.21/0.50    inference(forward_demodulation,[],[f242,f221])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl5_7 | ~spl5_27)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f107,f219])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl5_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f218])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) | (spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_31)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f77,f82,f87,f92,f97,f107,f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl5_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f239])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1) | spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    spl5_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f239])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    spl5_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f234])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f58,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(rectify,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    ~spl5_29 | spl5_1 | ~spl5_2 | ~spl5_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f170,f149,f80,f75,f229])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    spl5_17 <=> ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_17)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f77,f82,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl5_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f149])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    spl5_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f72,f218])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    spl5_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f194])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl5_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f67,f182])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl5_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f66,f178])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl5_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f70,f167])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl5_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f71,f161])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl5_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f157])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f63,f153])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK3(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK3(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl5_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f149])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f128])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f120])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f115])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f18])).
% 0.21/0.50  fof(f18,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl5_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f110])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f105])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f100])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f95])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f90])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f85])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f80])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f75])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (10651)------------------------------
% 0.21/0.50  % (10651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10651)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (10651)Memory used [KB]: 6652
% 0.21/0.50  % (10651)Time elapsed: 0.068 s
% 0.21/0.50  % (10651)------------------------------
% 0.21/0.50  % (10651)------------------------------
% 0.21/0.51  % (10642)Success in time 0.145 s
%------------------------------------------------------------------------------
