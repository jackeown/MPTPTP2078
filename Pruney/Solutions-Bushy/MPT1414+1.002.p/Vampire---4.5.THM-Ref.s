%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1414+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  292 ( 577 expanded)
%              Number of leaves         :   81 ( 313 expanded)
%              Depth                    :    7
%              Number of atoms          : 1407 (3049 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f521,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f107,f112,f117,f121,f125,f130,f134,f138,f142,f146,f150,f154,f159,f163,f167,f175,f179,f183,f187,f191,f195,f200,f205,f209,f213,f227,f238,f243,f248,f253,f258,f271,f278,f283,f289,f302,f304,f334,f357,f362,f368,f373,f376,f380,f382,f387,f392,f413,f435,f442,f463,f468,f470,f474,f508,f511,f520])).

fof(f520,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_43
    | ~ spl6_59
    | ~ spl6_41
    | ~ spl6_33
    | spl6_51 ),
    inference(avatar_split_clause,[],[f513,f319,f225,f261,f365,f268,f127,f94,f89,f99,f84])).

fof(f84,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f99,plain,
    ( spl6_4
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f89,plain,
    ( spl6_2
  <=> v3_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f94,plain,
    ( spl6_3
  <=> v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f127,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f268,plain,
    ( spl6_43
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f365,plain,
    ( spl6_59
  <=> v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f261,plain,
    ( spl6_41
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f225,plain,
    ( spl6_33
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f319,plain,
    ( spl6_51
  <=> m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f513,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_33
    | spl6_51 ),
    inference(resolution,[],[f321,f226])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f225])).

fof(f321,plain,
    ( ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | spl6_51 ),
    inference(avatar_component_clause,[],[f319])).

fof(f511,plain,
    ( ~ spl6_8
    | ~ spl6_82 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_82 ),
    inference(resolution,[],[f507,f120])).

fof(f120,plain,
    ( ! [X0] : m1_subset_1(sK4(X0),X0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_8
  <=> ! [X0] : m1_subset_1(sK4(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f507,plain,
    ( ! [X5] : ~ m1_subset_1(X5,k8_eqrel_1(sK0,sK1))
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl6_82
  <=> ! [X5] : ~ m1_subset_1(X5,k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f508,plain,
    ( spl6_82
    | spl6_55
    | ~ spl6_68
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f477,f472,f428,f343,f506])).

fof(f343,plain,
    ( spl6_55
  <=> v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f428,plain,
    ( spl6_68
  <=> m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f472,plain,
    ( spl6_76
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f477,plain,
    ( ! [X5] :
        ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X5,k8_eqrel_1(sK0,sK1)) )
    | ~ spl6_68
    | ~ spl6_76 ),
    inference(resolution,[],[f473,f429])).

fof(f429,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f428])).

fof(f473,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f472])).

fof(f474,plain,
    ( spl6_76
    | ~ spl6_13
    | ~ spl6_75 ),
    inference(avatar_split_clause,[],[f469,f466,f140,f472])).

fof(f140,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f466,plain,
    ( spl6_75
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f469,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl6_13
    | ~ spl6_75 ),
    inference(resolution,[],[f467,f141])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f140])).

% (27380)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f466])).

fof(f470,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_22
    | spl6_70 ),
    inference(avatar_split_clause,[],[f443,f439,f177,f127,f99,f94,f89])).

% (27397)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
fof(f177,plain,
    ( spl6_22
  <=> ! [X1,X0] :
        ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(X1,X0)
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f439,plain,
    ( spl6_70
  <=> m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f443,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ spl6_22
    | spl6_70 ),
    inference(resolution,[],[f441,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(X1,X0)
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f177])).

fof(f441,plain,
    ( ~ m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | spl6_70 ),
    inference(avatar_component_clause,[],[f439])).

fof(f468,plain,
    ( spl6_75
    | ~ spl6_9
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f464,f461,f123,f466])).

fof(f123,plain,
    ( spl6_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ sP5(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f461,plain,
    ( spl6_74
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | sP5(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f464,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl6_9
    | ~ spl6_74 ),
    inference(resolution,[],[f462,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ sP5(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f462,plain,
    ( ! [X0] :
        ( sP5(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f461])).

fof(f463,plain,
    ( spl6_74
    | ~ spl6_15
    | ~ spl6_69 ),
    inference(avatar_split_clause,[],[f454,f432,f148,f461])).

fof(f148,plain,
    ( spl6_15
  <=> ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | sP5(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f432,plain,
    ( spl6_69
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | sP5(X0) )
    | ~ spl6_15
    | ~ spl6_69 ),
    inference(resolution,[],[f434,f149])).

fof(f149,plain,
    ( ! [X2,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | sP5(X1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f434,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f432])).

fof(f442,plain,
    ( ~ spl6_70
    | ~ spl6_12
    | spl6_68 ),
    inference(avatar_split_clause,[],[f436,f428,f136,f439])).

fof(f136,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_eqrel_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f436,plain,
    ( ~ m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ spl6_12
    | spl6_68 ),
    inference(resolution,[],[f430,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_eqrel_1(X1,X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f430,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl6_68 ),
    inference(avatar_component_clause,[],[f428])).

fof(f435,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_5
    | ~ spl6_68
    | spl6_69
    | ~ spl6_25
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f414,f355,f189,f432,f428,f104,f127,f99,f94,f89,f84])).

fof(f104,plain,
    ( spl6_5
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f189,plain,
    ( spl6_25
  <=> ! [X1,X0,X2] :
        ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(X1,X0)
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f355,plain,
    ( spl6_57
  <=> ! [X0] :
        ( ~ m2_subset_1(k9_eqrel_1(sK0,sK1,sK2),X0,k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f414,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_25
    | ~ spl6_57 ),
    inference(resolution,[],[f356,f190])).

fof(f190,plain,
    ( ! [X2,X0,X1] :
        ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(X1,X0)
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | v1_xboole_0(X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f189])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ m2_subset_1(k9_eqrel_1(sK0,sK1,sK2),X0,k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(X0)) )
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f355])).

fof(f413,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | spl6_1
    | ~ spl6_22
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f393,f390,f177,f84,f127,f99,f94,f89])).

fof(f390,plain,
    ( spl6_61
  <=> ! [X1] :
        ( ~ m1_eqrel_1(k8_eqrel_1(sK0,sK1),X1)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f393,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ spl6_22
    | ~ spl6_61 ),
    inference(resolution,[],[f391,f178])).

fof(f391,plain,
    ( ! [X1] :
        ( ~ m1_eqrel_1(k8_eqrel_1(sK0,sK1),X1)
        | v1_xboole_0(X1) )
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f390])).

fof(f392,plain,
    ( spl6_61
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f384,f343,f132,f390])).

fof(f132,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_eqrel_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f384,plain,
    ( ! [X1] :
        ( ~ m1_eqrel_1(k8_eqrel_1(sK0,sK1),X1)
        | v1_xboole_0(X1) )
    | ~ spl6_11
    | ~ spl6_55 ),
    inference(resolution,[],[f345,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_eqrel_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f345,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f343])).

fof(f387,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_43
    | ~ spl6_59
    | ~ spl6_41
    | ~ spl6_30
    | spl6_50 ),
    inference(avatar_split_clause,[],[f385,f315,f211,f261,f365,f268,f127,f94,f89,f99,f84])).

fof(f211,plain,
    ( spl6_30
  <=> ! [X1,X0,X2] :
        ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f315,plain,
    ( spl6_50
  <=> v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f385,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_30
    | spl6_50 ),
    inference(resolution,[],[f317,f212])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f211])).

fof(f317,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | spl6_50 ),
    inference(avatar_component_clause,[],[f315])).

fof(f382,plain,
    ( ~ spl6_5
    | ~ spl6_43
    | ~ spl6_59
    | ~ spl6_41
    | ~ spl6_7
    | ~ spl6_24
    | spl6_60 ),
    inference(avatar_split_clause,[],[f374,f370,f185,f114,f261,f365,f268,f104])).

fof(f114,plain,
    ( spl6_7
  <=> r3_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f185,plain,
    ( spl6_24
  <=> ! [X1,X0,X2] :
        ( r2_binop_1(X0,X1,X2)
        | ~ r3_binop_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f370,plain,
    ( spl6_60
  <=> r2_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f374,plain,
    ( ~ r3_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl6_24
    | spl6_60 ),
    inference(resolution,[],[f372,f186])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( r2_binop_1(X0,X1,X2)
        | ~ r3_binop_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f185])).

fof(f372,plain,
    ( ~ r2_binop_1(sK0,sK2,sK3)
    | spl6_60 ),
    inference(avatar_component_clause,[],[f370])).

fof(f380,plain,
    ( spl6_1
    | ~ spl6_46
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f379,f276,f109,f286,f84])).

fof(f286,plain,
    ( spl6_46
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f109,plain,
    ( spl6_6
  <=> m2_filter_1(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f276,plain,
    ( spl6_44
  <=> ! [X1,X0] :
        ( ~ m2_filter_1(sK3,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f379,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(resolution,[],[f277,f111])).

fof(f111,plain,
    ( m2_filter_1(sK3,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( ~ m2_filter_1(sK3,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f276])).

fof(f376,plain,
    ( spl6_1
    | spl6_45
    | ~ spl6_18
    | spl6_59 ),
    inference(avatar_split_clause,[],[f375,f365,f161,f281,f84])).

fof(f281,plain,
    ( spl6_45
  <=> ! [X0] :
        ( ~ m2_filter_1(sK3,sK0,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f161,plain,
    ( spl6_18
  <=> ! [X1,X0,X2] :
        ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ m2_filter_1(X2,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ m2_filter_1(sK3,sK0,X0)
        | ~ v1_relat_1(X0)
        | v1_xboole_0(sK0) )
    | ~ spl6_18
    | spl6_59 ),
    inference(resolution,[],[f367,f162])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ m2_filter_1(X2,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f367,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | spl6_59 ),
    inference(avatar_component_clause,[],[f365])).

fof(f373,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_60
    | ~ spl6_28
    | spl6_54 ),
    inference(avatar_split_clause,[],[f338,f331,f203,f370,f109,f104,f127,f94,f89,f99,f84])).

fof(f203,plain,
    ( spl6_28
  <=> ! [X1,X3,X0,X2] :
        ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
        | ~ r2_binop_1(X0,X2,X3)
        | ~ m2_filter_1(X3,X0,X1)
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f331,plain,
    ( spl6_54
  <=> r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f338,plain,
    ( ~ r2_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_28
    | spl6_54 ),
    inference(resolution,[],[f333,f204])).

fof(f204,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
        | ~ r2_binop_1(X0,X2,X3)
        | ~ m2_filter_1(X3,X0,X1)
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f203])).

fof(f333,plain,
    ( ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | spl6_54 ),
    inference(avatar_component_clause,[],[f331])).

fof(f368,plain,
    ( ~ spl6_5
    | ~ spl6_43
    | ~ spl6_59
    | ~ spl6_41
    | ~ spl6_7
    | ~ spl6_23
    | spl6_58 ),
    inference(avatar_split_clause,[],[f363,f359,f181,f114,f261,f365,f268,f104])).

fof(f181,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( r1_binop_1(X0,X1,X2)
        | ~ r3_binop_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f359,plain,
    ( spl6_58
  <=> r1_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f363,plain,
    ( ~ r3_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl6_23
    | spl6_58 ),
    inference(resolution,[],[f361,f182])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( r1_binop_1(X0,X1,X2)
        | ~ r3_binop_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f361,plain,
    ( ~ r1_binop_1(sK0,sK2,sK3)
    | spl6_58 ),
    inference(avatar_component_clause,[],[f359])).

fof(f362,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_58
    | ~ spl6_29
    | spl6_52 ),
    inference(avatar_split_clause,[],[f336,f323,f207,f359,f109,f104,f127,f94,f89,f99,f84])).

fof(f207,plain,
    ( spl6_29
  <=> ! [X1,X3,X0,X2] :
        ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
        | ~ r1_binop_1(X0,X2,X3)
        | ~ m2_filter_1(X3,X0,X1)
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f323,plain,
    ( spl6_52
  <=> r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f336,plain,
    ( ~ r1_binop_1(sK0,sK2,sK3)
    | ~ m2_filter_1(sK3,sK0,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_29
    | spl6_52 ),
    inference(resolution,[],[f325,f208])).

fof(f208,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
        | ~ r1_binop_1(X0,X2,X3)
        | ~ m2_filter_1(X3,X0,X1)
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f207])).

fof(f325,plain,
    ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | spl6_52 ),
    inference(avatar_component_clause,[],[f323])).

fof(f357,plain,
    ( spl6_55
    | spl6_57
    | ~ spl6_19
    | spl6_53 ),
    inference(avatar_split_clause,[],[f335,f327,f165,f355,f343])).

fof(f165,plain,
    ( spl6_19
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,X1)
        | ~ m2_subset_1(X2,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f327,plain,
    ( spl6_53
  <=> m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ m2_subset_1(k9_eqrel_1(sK0,sK1,sK2),X0,k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(X0))
        | v1_xboole_0(k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(X0) )
    | ~ spl6_19
    | spl6_53 ),
    inference(resolution,[],[f329,f166])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,X1)
        | ~ m2_subset_1(X2,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f329,plain,
    ( ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | spl6_53 ),
    inference(avatar_component_clause,[],[f327])).

fof(f334,plain,
    ( ~ spl6_50
    | ~ spl6_51
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_54
    | spl6_17
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f312,f265,f156,f331,f327,f323,f319,f315])).

fof(f156,plain,
    ( spl6_17
  <=> r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f265,plain,
    ( spl6_42
  <=> ! [X1,X0] :
        ( r3_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ r2_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ m1_subset_1(X1,X0)
        | ~ r1_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(X0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f312,plain,
    ( ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | spl6_17
    | ~ spl6_42 ),
    inference(resolution,[],[f266,f158])).

fof(f158,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( r3_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ r2_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ m1_subset_1(X1,X0)
        | ~ r1_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(X0,X0),X0) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f265])).

fof(f304,plain,
    ( spl6_34
    | ~ spl6_14
    | spl6_46 ),
    inference(avatar_split_clause,[],[f298,f286,f144,f229])).

fof(f229,plain,
    ( spl6_34
  <=> ! [X3,X2] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f144,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f298,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl6_14
    | spl6_46 ),
    inference(resolution,[],[f288,f145])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f288,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_46 ),
    inference(avatar_component_clause,[],[f286])).

fof(f302,plain,
    ( ~ spl6_10
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_34 ),
    inference(resolution,[],[f230,f129])).

fof(f129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f230,plain,
    ( ! [X2,X3] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f229])).

fof(f289,plain,
    ( ~ spl6_46
    | ~ spl6_6
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f284,f281,f109,f286])).

fof(f284,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_6
    | ~ spl6_45 ),
    inference(resolution,[],[f282,f111])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ m2_filter_1(sK3,sK0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( spl6_1
    | spl6_45
    | ~ spl6_21
    | spl6_41 ),
    inference(avatar_split_clause,[],[f273,f261,f173,f281,f84])).

fof(f173,plain,
    ( spl6_21
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ m2_filter_1(X2,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ m2_filter_1(sK3,sK0,X0)
        | ~ v1_relat_1(X0)
        | v1_xboole_0(sK0) )
    | ~ spl6_21
    | spl6_41 ),
    inference(resolution,[],[f263,f174])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ m2_filter_1(X2,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f173])).

fof(f263,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f261])).

fof(f278,plain,
    ( spl6_44
    | ~ spl6_16
    | spl6_43 ),
    inference(avatar_split_clause,[],[f272,f268,f152,f276])).

% (27383)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
fof(f152,plain,
    ( spl6_16
  <=> ! [X1,X0,X2] :
        ( v1_funct_1(X2)
        | ~ m2_filter_1(X2,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ m2_filter_1(sK3,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) )
    | ~ spl6_16
    | spl6_43 ),
    inference(resolution,[],[f270,f153])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(X2)
        | ~ m2_filter_1(X2,X0,X1)
        | ~ v1_relat_1(X1)
        | v1_xboole_0(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f270,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_43 ),
    inference(avatar_component_clause,[],[f268])).

fof(f271,plain,
    ( spl6_34
    | ~ spl6_41
    | spl6_42
    | ~ spl6_43
    | ~ spl6_6
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f259,f256,f109,f268,f265,f261,f229])).

fof(f256,plain,
    ( spl6_40
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ v1_funct_1(X0)
        | ~ m2_filter_1(X0,sK0,X1)
        | r3_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ r1_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X3,X2)
        | ~ r2_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f259,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(sK3)
        | r3_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(X0,X0),X0)
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ r1_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ m1_subset_1(X1,X0)
        | ~ r2_binop_1(X0,X1,k3_filter_1(sK0,sK1,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl6_6
    | ~ spl6_40 ),
    inference(resolution,[],[f257,f111])).

fof(f257,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m2_filter_1(X0,sK0,X1)
        | ~ v1_funct_1(X0)
        | r3_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ r1_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X3,X2)
        | ~ r2_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl6_40
    | ~ spl6_14
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f254,f251,f144,f256])).

fof(f251,plain,
    ( spl6_39
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X3)
        | ~ m2_filter_1(X0,sK0,X3)
        | r3_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ r1_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X1,X2)
        | ~ r2_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f254,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m2_filter_1(X0,sK0,X1)
        | r3_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ r1_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X3,X2)
        | ~ r2_binop_1(X2,X3,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl6_14
    | ~ spl6_39 ),
    inference(resolution,[],[f252,f145])).

fof(f252,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X3)
        | ~ v1_funct_1(X0)
        | ~ m2_filter_1(X0,sK0,X3)
        | r3_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ r1_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X1,X2)
        | ~ r2_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f251])).

fof(f253,plain,
    ( spl6_1
    | spl6_39
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f249,f246,f161,f251,f84])).

fof(f246,plain,
    ( spl6_38
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ r2_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2))
        | ~ r1_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2))
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X2),k2_zfmisc_1(X1,X1),X1)
        | r3_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f249,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X1,X2)
        | ~ r2_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ r1_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | r3_binop_1(X2,X1,k3_filter_1(sK0,sK1,X0))
        | ~ m2_filter_1(X0,sK0,X3)
        | ~ v1_relat_1(X3)
        | v1_xboole_0(sK0) )
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(resolution,[],[f247,f162])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X0,X1)
        | ~ r2_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2))
        | ~ r1_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2))
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X2),k2_zfmisc_1(X1,X1),X1)
        | r3_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2)) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( ~ spl6_10
    | spl6_1
    | spl6_38
    | ~ spl6_4
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f244,f241,f99,f246,f84,f127])).

fof(f241,plain,
    ( spl6_37
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
        | ~ m1_subset_1(X3,X2)
        | r3_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | ~ v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | ~ m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ r1_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | ~ r2_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | v1_xboole_0(X1)
        | ~ v1_partfun1(sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | r3_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2))
        | ~ v1_funct_2(k3_filter_1(sK0,sK1,X2),k2_zfmisc_1(X1,X1),X1)
        | ~ m1_subset_1(k3_filter_1(sK0,sK1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ r1_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2))
        | ~ r2_binop_1(X1,X0,k3_filter_1(sK0,sK1,X2))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X2) )
    | ~ spl6_4
    | ~ spl6_37 ),
    inference(resolution,[],[f242,f101])).

fof(f101,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f242,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_partfun1(sK1,X1)
        | ~ m1_subset_1(X3,X2)
        | r3_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | ~ v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | ~ m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ r1_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | ~ r2_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f241])).

fof(f243,plain,
    ( ~ spl6_2
    | spl6_37
    | ~ spl6_3
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f239,f236,f94,f241,f89])).

fof(f236,plain,
    ( spl6_36
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ v8_relat_2(X2)
        | ~ v3_relat_2(X2)
        | ~ v1_partfun1(X2,X1)
        | v1_xboole_0(X1)
        | ~ r2_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ r1_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(X3,X3),X3)
        | r3_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ m1_subset_1(X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f239,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v3_relat_2(sK1)
        | ~ v1_partfun1(sK1,X1)
        | v1_xboole_0(X1)
        | ~ r2_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | ~ r1_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | ~ m1_subset_1(k3_filter_1(X1,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ v1_funct_2(k3_filter_1(X1,sK1,X0),k2_zfmisc_1(X2,X2),X2)
        | r3_binop_1(X2,X3,k3_filter_1(X1,sK1,X0))
        | ~ m1_subset_1(X3,X2) )
    | ~ spl6_3
    | ~ spl6_36 ),
    inference(resolution,[],[f237,f96])).

% (27390)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f96,plain,
    ( v8_relat_2(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f237,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v8_relat_2(X2)
        | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v3_relat_2(X2)
        | ~ v1_partfun1(X2,X1)
        | v1_xboole_0(X1)
        | ~ r2_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ r1_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(X3,X3),X3)
        | r3_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ m1_subset_1(X4,X3) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f236])).

fof(f238,plain,
    ( spl6_36
    | ~ spl6_26
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f201,f198,f193,f236])).

fof(f193,plain,
    ( spl6_26
  <=> ! [X1,X0,X2] :
        ( r3_binop_1(X0,X1,X2)
        | ~ r2_binop_1(X0,X1,X2)
        | ~ r1_binop_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f198,plain,
    ( spl6_27
  <=> ! [X1,X0,X2] :
        ( v1_funct_1(k3_filter_1(X0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f201,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ v8_relat_2(X2)
        | ~ v3_relat_2(X2)
        | ~ v1_partfun1(X2,X1)
        | v1_xboole_0(X1)
        | ~ r2_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ r1_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(k3_filter_1(X1,X2,X0),k2_zfmisc_1(X3,X3),X3)
        | r3_binop_1(X3,X4,k3_filter_1(X1,X2,X0))
        | ~ m1_subset_1(X4,X3) )
    | ~ spl6_26
    | ~ spl6_27 ),
    inference(resolution,[],[f199,f194])).

fof(f194,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ r2_binop_1(X0,X1,X2)
        | ~ r1_binop_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | r3_binop_1(X0,X1,X2)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f193])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k3_filter_1(X0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v8_relat_2(X1)
        | ~ v3_relat_2(X1)
        | ~ v1_partfun1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f198])).

fof(f227,plain,(
    spl6_33 ),
    inference(avatar_split_clause,[],[f79,f225])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(f213,plain,(
    spl6_30 ),
    inference(avatar_split_clause,[],[f78,f211])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f209,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f62,f207])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r1_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r1_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r1_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r1_binop_1(X0,X2,X3)
                   => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_1)).

fof(f205,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f61,f203])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r2_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r2_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r2_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r2_binop_1(X0,X2,X3)
                   => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_filter_1)).

fof(f200,plain,(
    spl6_27 ),
    inference(avatar_split_clause,[],[f77,f198])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f195,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f68,f193])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r3_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).

fof(f191,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f76,f189])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

fof(f187,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f67,f185])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f183,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f66,f181])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f179,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f74,f177])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

fof(f175,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f73,f173])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(f167,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f69,f165])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(f163,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f72,f161])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f159,plain,(
    ~ spl6_17 ),
    inference(avatar_split_clause,[],[f59,f156])).

fof(f59,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                    & r3_binop_1(X0,X2,X3)
                    & m2_filter_1(X3,X0,X1) )
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                  & r3_binop_1(sK0,X2,X3)
                  & m2_filter_1(X3,sK0,X1) )
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                & r3_binop_1(sK0,X2,X3)
                & m2_filter_1(X3,sK0,X1) )
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3))
              & r3_binop_1(sK0,X2,X3)
              & m2_filter_1(X3,sK0,sK1) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v8_relat_2(sK1)
      & v3_relat_2(sK1)
      & v1_partfun1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,X2),k3_filter_1(sK0,sK1,X3))
            & r3_binop_1(sK0,X2,X3)
            & m2_filter_1(X3,sK0,sK1) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
          & r3_binop_1(sK0,sK2,X3)
          & m2_filter_1(X3,sK0,sK1) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,X3))
        & r3_binop_1(sK0,sK2,X3)
        & m2_filter_1(X3,sK0,sK1) )
   => ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
      & r3_binop_1(sK0,sK2,sK3)
      & m2_filter_1(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r3_binop_1(X0,X2,X3)
                     => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r3_binop_1(X0,X2,X3)
                   => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_1)).

fof(f154,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f71,f152])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f150,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f81,f148])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f81_D])).

fof(f81_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f146,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f75,f144])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f142,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f65,f140])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f138,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f64,f136])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_eqrel_1(X1,X0)
     => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

fof(f134,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f60,f132])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_eqrel_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_eqrel_1)).

% (27386)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
fof(f130,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f55,f127])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f82,f123])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f80,f81_D])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f121,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f63,f119])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f117,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f58,f114])).

fof(f58,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f57,f109])).

fof(f57,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f56,f104])).

fof(f56,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f99])).

fof(f52,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f54,f94])).

fof(f54,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f53,f89])).

fof(f53,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f51,f84])).

fof(f51,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

%------------------------------------------------------------------------------
