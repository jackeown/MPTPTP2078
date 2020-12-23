%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:39 EST 2020

% Result     : Theorem 17.78s
% Output     : Refutation 17.78s
% Verified   : 
% Statistics : Number of formulae       :  544 (1043 expanded)
%              Number of leaves         :  128 ( 487 expanded)
%              Depth                    :   12
%              Number of atoms          : 2334 (3966 expanded)
%              Number of equality atoms :  413 ( 663 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f227,f231,f235,f239,f243,f247,f251,f255,f259,f263,f271,f279,f283,f287,f291,f295,f315,f327,f331,f335,f339,f351,f379,f387,f391,f395,f415,f419,f427,f437,f449,f457,f473,f477,f485,f514,f519,f570,f574,f620,f623,f699,f703,f717,f747,f755,f764,f791,f841,f861,f876,f890,f908,f915,f928,f933,f964,f976,f1103,f1161,f1281,f1318,f1339,f1359,f1701,f1707,f1791,f1874,f1912,f2003,f2101,f2105,f2121,f2155,f2179,f2291,f2324,f2338,f2919,f2945,f2979,f3085,f3151,f3199,f3415,f3441,f3678,f3696,f3742,f3811,f3826,f3855,f8146,f9173,f9178,f9203,f10336,f10361])).

fof(f10361,plain,
    ( ~ spl8_8
    | ~ spl8_56
    | spl8_183
    | ~ spl8_411 ),
    inference(avatar_contradiction_clause,[],[f10360])).

fof(f10360,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_56
    | spl8_183
    | ~ spl8_411 ),
    inference(subsumption_resolution,[],[f10359,f254])).

fof(f254,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f10359,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_56
    | spl8_183
    | ~ spl8_411 ),
    inference(subsumption_resolution,[],[f10341,f1338])).

fof(f1338,plain,
    ( sK0 != k2_relat_1(sK1)
    | spl8_183 ),
    inference(avatar_component_clause,[],[f1337])).

fof(f1337,plain,
    ( spl8_183
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_183])])).

fof(f10341,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_56
    | ~ spl8_411 ),
    inference(superposition,[],[f448,f10335])).

fof(f10335,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl8_411 ),
    inference(avatar_component_clause,[],[f10334])).

fof(f10334,plain,
    ( spl8_411
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_411])])).

fof(f448,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl8_56
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f10336,plain,
    ( spl8_411
    | spl8_182
    | ~ spl8_385
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_204
    | ~ spl8_237 ),
    inference(avatar_split_clause,[],[f9201,f2289,f1872,f253,f249,f241,f233,f229,f8135,f1334,f10334])).

fof(f1334,plain,
    ( spl8_182
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_182])])).

fof(f8135,plain,
    ( spl8_385
  <=> sK0 = k2_relset_1(sK0,sK0,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_385])])).

fof(f229,plain,
    ( spl8_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f233,plain,
    ( spl8_3
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f241,plain,
    ( spl8_5
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f249,plain,
    ( spl8_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1872,plain,
    ( spl8_204
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_204])])).

fof(f2289,plain,
    ( spl8_237
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK2,X2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X0,sK2)) != X3
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X3
        | k2_relset_1(X1,X2,X0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_237])])).

fof(f9201,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_204
    | ~ spl8_237 ),
    inference(subsumption_resolution,[],[f9200,f230])).

fof(f230,plain,
    ( v1_funct_1(sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f229])).

fof(f9200,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_204
    | ~ spl8_237 ),
    inference(subsumption_resolution,[],[f9199,f242])).

fof(f242,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f241])).

fof(f9199,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_204
    | ~ spl8_237 ),
    inference(subsumption_resolution,[],[f9198,f250])).

fof(f250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f249])).

fof(f9198,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl8_3
    | ~ spl8_8
    | ~ spl8_204
    | ~ spl8_237 ),
    inference(subsumption_resolution,[],[f9197,f234])).

fof(f234,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f233])).

fof(f9197,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl8_8
    | ~ spl8_204
    | ~ spl8_237 ),
    inference(subsumption_resolution,[],[f9195,f254])).

fof(f9195,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl8_204
    | ~ spl8_237 ),
    inference(superposition,[],[f2290,f1873])).

fof(f1873,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ spl8_204 ),
    inference(avatar_component_clause,[],[f1872])).

fof(f2290,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X0,sK2)) != X3
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK2,X2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(X0,X1,X2)
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X3
        | k2_relset_1(X1,X2,X0) = X2 )
    | ~ spl8_237 ),
    inference(avatar_component_clause,[],[f2289])).

fof(f9203,plain,
    ( ~ spl8_101
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | spl8_12
    | ~ spl8_97 ),
    inference(avatar_split_clause,[],[f9108,f715,f269,f253,f245,f241,f229,f736])).

fof(f736,plain,
    ( spl8_101
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f245,plain,
    ( spl8_6
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f269,plain,
    ( spl8_12
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f715,plain,
    ( spl8_97
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v3_funct_2(X1,X0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f9108,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | spl8_12
    | ~ spl8_97 ),
    inference(subsumption_resolution,[],[f9107,f230])).

fof(f9107,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | spl8_12
    | ~ spl8_97 ),
    inference(subsumption_resolution,[],[f9106,f254])).

fof(f9106,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_12
    | ~ spl8_97 ),
    inference(subsumption_resolution,[],[f9105,f246])).

fof(f246,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f245])).

fof(f9105,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl8_5
    | spl8_12
    | ~ spl8_97 ),
    inference(subsumption_resolution,[],[f9104,f242])).

fof(f9104,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl8_12
    | ~ spl8_97 ),
    inference(superposition,[],[f270,f716])).

fof(f716,plain,
    ( ! [X0,X1] :
        ( k2_funct_2(X0,X1) = k2_funct_1(X1)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v3_funct_2(X1,X0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_1(X1) )
    | ~ spl8_97 ),
    inference(avatar_component_clause,[],[f715])).

fof(f270,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f269])).

fof(f9178,plain,
    ( ~ spl8_7
    | ~ spl8_49
    | spl8_386 ),
    inference(avatar_contradiction_clause,[],[f9177])).

fof(f9177,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_49
    | spl8_386 ),
    inference(subsumption_resolution,[],[f9175,f250])).

fof(f9175,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_49
    | spl8_386 ),
    inference(resolution,[],[f9172,f418])).

fof(f418,plain,
    ( ! [X0,X3,X1] :
        ( r2_relset_1(X0,X1,X3,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl8_49
  <=> ! [X1,X3,X0] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_relset_1(X0,X1,X3,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f9172,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | spl8_386 ),
    inference(avatar_component_clause,[],[f9171])).

fof(f9171,plain,
    ( spl8_386
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_386])])).

fof(f9173,plain,
    ( ~ spl8_386
    | spl8_101
    | ~ spl8_181 ),
    inference(avatar_split_clause,[],[f8719,f1331,f736,f9171])).

fof(f1331,plain,
    ( spl8_181
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_181])])).

fof(f8719,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | spl8_101
    | ~ spl8_181 ),
    inference(forward_demodulation,[],[f737,f1332])).

fof(f1332,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl8_181 ),
    inference(avatar_component_clause,[],[f1331])).

fof(f737,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | spl8_101 ),
    inference(avatar_component_clause,[],[f736])).

fof(f8146,plain,
    ( ~ spl8_27
    | ~ spl8_56
    | ~ spl8_127
    | spl8_385 ),
    inference(avatar_contradiction_clause,[],[f8145])).

fof(f8145,plain,
    ( $false
    | ~ spl8_27
    | ~ spl8_56
    | ~ spl8_127
    | spl8_385 ),
    inference(subsumption_resolution,[],[f8144,f330])).

fof(f330,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl8_27
  <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f8144,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_56
    | ~ spl8_127
    | spl8_385 ),
    inference(subsumption_resolution,[],[f8143,f963])).

fof(f963,plain,
    ( sK0 = k2_relat_1(k6_relat_1(sK0))
    | ~ spl8_127 ),
    inference(avatar_component_clause,[],[f962])).

fof(f962,plain,
    ( spl8_127
  <=> sK0 = k2_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).

fof(f8143,plain,
    ( sK0 != k2_relat_1(k6_relat_1(sK0))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_56
    | spl8_385 ),
    inference(superposition,[],[f8136,f448])).

fof(f8136,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0))
    | spl8_385 ),
    inference(avatar_component_clause,[],[f8135])).

fof(f3855,plain,
    ( ~ spl8_53
    | ~ spl8_287
    | ~ spl8_304
    | spl8_331
    | ~ spl8_336 ),
    inference(avatar_contradiction_clause,[],[f3854])).

fof(f3854,plain,
    ( $false
    | ~ spl8_53
    | ~ spl8_287
    | ~ spl8_304
    | spl8_331
    | ~ spl8_336 ),
    inference(subsumption_resolution,[],[f3849,f2918])).

fof(f2918,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_287 ),
    inference(avatar_component_clause,[],[f2917])).

fof(f2917,plain,
    ( spl8_287
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_287])])).

fof(f3849,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_53
    | ~ spl8_304
    | spl8_331
    | ~ spl8_336 ),
    inference(backward_demodulation,[],[f3791,f3848])).

fof(f3848,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl8_53
    | ~ spl8_304
    | ~ spl8_336 ),
    inference(forward_demodulation,[],[f3198,f3747])).

fof(f3747,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_53
    | ~ spl8_336 ),
    inference(resolution,[],[f3741,f436])).

fof(f436,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl8_53
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f3741,plain,
    ( ! [X24] :
        ( ~ m1_subset_1(X24,k1_zfmisc_1(sK2))
        | k1_xboole_0 = X24 )
    | ~ spl8_336 ),
    inference(avatar_component_clause,[],[f3740])).

fof(f3740,plain,
    ( spl8_336
  <=> ! [X24] :
        ( ~ m1_subset_1(X24,k1_zfmisc_1(sK2))
        | k1_xboole_0 = X24 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_336])])).

fof(f3198,plain,
    ( sK2 = k2_funct_1(sK2)
    | ~ spl8_304 ),
    inference(avatar_component_clause,[],[f3197])).

fof(f3197,plain,
    ( spl8_304
  <=> sK2 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_304])])).

fof(f3791,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl8_53
    | spl8_331
    | ~ spl8_336 ),
    inference(backward_demodulation,[],[f3677,f3747])).

fof(f3677,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))
    | spl8_331 ),
    inference(avatar_component_clause,[],[f3676])).

fof(f3676,plain,
    ( spl8_331
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_331])])).

fof(f3826,plain,
    ( ~ spl8_53
    | ~ spl8_300
    | spl8_303
    | ~ spl8_336 ),
    inference(avatar_contradiction_clause,[],[f3825])).

fof(f3825,plain,
    ( $false
    | ~ spl8_53
    | ~ spl8_300
    | spl8_303
    | ~ spl8_336 ),
    inference(subsumption_resolution,[],[f3793,f3784])).

fof(f3784,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_53
    | spl8_303
    | ~ spl8_336 ),
    inference(backward_demodulation,[],[f3195,f3747])).

fof(f3195,plain,
    ( k1_xboole_0 != k5_relat_1(sK2,sK2)
    | spl8_303 ),
    inference(avatar_component_clause,[],[f3194])).

fof(f3194,plain,
    ( spl8_303
  <=> k1_xboole_0 = k5_relat_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_303])])).

fof(f3793,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_53
    | ~ spl8_300
    | ~ spl8_336 ),
    inference(backward_demodulation,[],[f3695,f3747])).

fof(f3695,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2)
    | ~ spl8_300 ),
    inference(avatar_component_clause,[],[f3184])).

fof(f3184,plain,
    ( spl8_300
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_300])])).

fof(f3811,plain,
    ( ~ spl8_53
    | ~ spl8_200
    | spl8_302
    | ~ spl8_336 ),
    inference(avatar_contradiction_clause,[],[f3810])).

fof(f3810,plain,
    ( $false
    | ~ spl8_53
    | ~ spl8_200
    | spl8_302
    | ~ spl8_336 ),
    inference(subsumption_resolution,[],[f3783,f1700])).

fof(f1700,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_200 ),
    inference(avatar_component_clause,[],[f1699])).

fof(f1699,plain,
    ( spl8_200
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_200])])).

fof(f3783,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl8_53
    | spl8_302
    | ~ spl8_336 ),
    inference(backward_demodulation,[],[f3191,f3747])).

fof(f3191,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl8_302 ),
    inference(avatar_component_clause,[],[f3190])).

fof(f3190,plain,
    ( spl8_302
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_302])])).

fof(f3742,plain,
    ( spl8_336
    | ~ spl8_205
    | ~ spl8_324 ),
    inference(avatar_split_clause,[],[f3423,f3413,f1910,f3740])).

fof(f1910,plain,
    ( spl8_205
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_205])])).

fof(f3413,plain,
    ( spl8_324
  <=> ! [X38,X37,X39] :
        ( ~ m1_subset_1(X37,k1_zfmisc_1(X38))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X39,k1_xboole_0)))
        | k1_xboole_0 = X37 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_324])])).

fof(f3423,plain,
    ( ! [X24] :
        ( ~ m1_subset_1(X24,k1_zfmisc_1(sK2))
        | k1_xboole_0 = X24 )
    | ~ spl8_205
    | ~ spl8_324 ),
    inference(resolution,[],[f3414,f1911])).

fof(f1911,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_205 ),
    inference(avatar_component_clause,[],[f1910])).

fof(f3414,plain,
    ( ! [X39,X37,X38] :
        ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X39,k1_xboole_0)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
        | k1_xboole_0 = X37 )
    | ~ spl8_324 ),
    inference(avatar_component_clause,[],[f3413])).

fof(f3696,plain,
    ( spl8_300
    | ~ spl8_53
    | ~ spl8_290
    | ~ spl8_325 ),
    inference(avatar_split_clause,[],[f3495,f3439,f2943,f435,f3184])).

fof(f2943,plain,
    ( spl8_290
  <=> k1_xboole_0 = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_290])])).

fof(f3439,plain,
    ( spl8_325
  <=> ! [X23] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(sK1))
        | k1_xboole_0 = X23 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_325])])).

fof(f3495,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2)
    | ~ spl8_53
    | ~ spl8_290
    | ~ spl8_325 ),
    inference(backward_demodulation,[],[f2944,f3446])).

fof(f3446,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_53
    | ~ spl8_325 ),
    inference(resolution,[],[f3440,f436])).

fof(f3440,plain,
    ( ! [X23] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(sK1))
        | k1_xboole_0 = X23 )
    | ~ spl8_325 ),
    inference(avatar_component_clause,[],[f3439])).

fof(f2944,plain,
    ( k1_xboole_0 = k5_relat_1(sK1,sK2)
    | ~ spl8_290 ),
    inference(avatar_component_clause,[],[f2943])).

fof(f3678,plain,
    ( ~ spl8_331
    | ~ spl8_53
    | spl8_215
    | ~ spl8_325 ),
    inference(avatar_split_clause,[],[f3474,f3439,f2119,f435,f3676])).

fof(f2119,plain,
    ( spl8_215
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_215])])).

fof(f3474,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))
    | ~ spl8_53
    | spl8_215
    | ~ spl8_325 ),
    inference(backward_demodulation,[],[f2120,f3446])).

fof(f2120,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))
    | spl8_215 ),
    inference(avatar_component_clause,[],[f2119])).

fof(f3441,plain,
    ( spl8_325
    | ~ spl8_208
    | ~ spl8_324 ),
    inference(avatar_split_clause,[],[f3422,f3413,f2001,f3439])).

fof(f2001,plain,
    ( spl8_208
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_208])])).

fof(f3422,plain,
    ( ! [X23] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(sK1))
        | k1_xboole_0 = X23 )
    | ~ spl8_208
    | ~ spl8_324 ),
    inference(resolution,[],[f3414,f2002])).

fof(f2002,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_208 ),
    inference(avatar_component_clause,[],[f2001])).

fof(f3415,plain,
    ( spl8_324
    | ~ spl8_63
    | ~ spl8_241 ),
    inference(avatar_split_clause,[],[f2334,f2322,f512,f3413])).

fof(f512,plain,
    ( spl8_63
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f2322,plain,
    ( spl8_241
  <=> ! [X16,X15,X17,X14] :
        ( k1_xboole_0 = X14
        | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_xboole_0(X17) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_241])])).

fof(f2334,plain,
    ( ! [X39,X37,X38] :
        ( ~ m1_subset_1(X37,k1_zfmisc_1(X38))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X39,k1_xboole_0)))
        | k1_xboole_0 = X37 )
    | ~ spl8_63
    | ~ spl8_241 ),
    inference(resolution,[],[f2323,f513])).

fof(f513,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f512])).

fof(f2323,plain,
    ( ! [X14,X17,X15,X16] :
        ( ~ v1_xboole_0(X17)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | k1_xboole_0 = X14 )
    | ~ spl8_241 ),
    inference(avatar_component_clause,[],[f2322])).

fof(f3199,plain,
    ( ~ spl8_81
    | ~ spl8_303
    | spl8_304
    | ~ spl8_302
    | ~ spl8_1
    | ~ spl8_211
    | ~ spl8_297 ),
    inference(avatar_split_clause,[],[f3155,f3149,f2099,f225,f3190,f3197,f3194,f618])).

fof(f618,plain,
    ( spl8_81
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f225,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2099,plain,
    ( spl8_211
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_211])])).

fof(f3149,plain,
    ( spl8_297
  <=> ! [X0] :
        ( k1_xboole_0 != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_297])])).

fof(f3155,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = k2_funct_1(sK2)
    | k1_xboole_0 != k5_relat_1(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_211
    | ~ spl8_297 ),
    inference(subsumption_resolution,[],[f3153,f226])).

fof(f226,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f225])).

fof(f3153,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = k2_funct_1(sK2)
    | k1_xboole_0 != k5_relat_1(sK2,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_211
    | ~ spl8_297 ),
    inference(superposition,[],[f3150,f2100])).

fof(f2100,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl8_211 ),
    inference(avatar_component_clause,[],[f2099])).

fof(f3150,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != k1_relat_1(sK2)
        | k2_funct_1(sK2) = X0
        | k1_xboole_0 != k5_relat_1(X0,sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_297 ),
    inference(avatar_component_clause,[],[f3149])).

fof(f3151,plain,
    ( spl8_297
    | ~ spl8_224
    | ~ spl8_262 ),
    inference(avatar_split_clause,[],[f3005,f2539,f2177,f3149])).

fof(f2177,plain,
    ( spl8_224
  <=> ! [X0] :
        ( k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_224])])).

fof(f2539,plain,
    ( spl8_262
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_262])])).

fof(f3005,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_224
    | ~ spl8_262 ),
    inference(backward_demodulation,[],[f2178,f2540])).

fof(f2540,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl8_262 ),
    inference(avatar_component_clause,[],[f2539])).

fof(f2178,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_224 ),
    inference(avatar_component_clause,[],[f2177])).

fof(f3085,plain,
    ( ~ spl8_28
    | ~ spl8_53
    | ~ spl8_63
    | ~ spl8_242
    | spl8_286 ),
    inference(avatar_contradiction_clause,[],[f3081])).

fof(f3081,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_53
    | ~ spl8_63
    | ~ spl8_242
    | spl8_286 ),
    inference(unit_resulting_resolution,[],[f513,f334,f436,f3072,f2337])).

fof(f2337,plain,
    ( ! [X21,X19,X20,X18] :
        ( ~ v1_xboole_0(X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | k1_xboole_0 = X18 )
    | ~ spl8_242 ),
    inference(avatar_component_clause,[],[f2336])).

fof(f2336,plain,
    ( spl8_242
  <=> ! [X18,X20,X19,X21] :
        ( k1_xboole_0 = X18
        | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_xboole_0(X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_242])])).

fof(f3072,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | spl8_286 ),
    inference(avatar_component_clause,[],[f2892])).

fof(f2892,plain,
    ( spl8_286
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_286])])).

fof(f334,plain,
    ( ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl8_28
  <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f2979,plain,
    ( ~ spl8_27
    | ~ spl8_53
    | ~ spl8_63
    | ~ spl8_242
    | spl8_262 ),
    inference(avatar_contradiction_clause,[],[f2975])).

fof(f2975,plain,
    ( $false
    | ~ spl8_27
    | ~ spl8_53
    | ~ spl8_63
    | ~ spl8_242
    | spl8_262 ),
    inference(unit_resulting_resolution,[],[f513,f330,f436,f2940,f2337])).

fof(f2940,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | spl8_262 ),
    inference(avatar_component_clause,[],[f2539])).

fof(f2945,plain,
    ( spl8_290
    | ~ spl8_221
    | ~ spl8_286 ),
    inference(avatar_split_clause,[],[f2900,f2892,f2153,f2943])).

fof(f2153,plain,
    ( spl8_221
  <=> k6_partfun1(k1_xboole_0) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_221])])).

fof(f2900,plain,
    ( k1_xboole_0 = k5_relat_1(sK1,sK2)
    | ~ spl8_221
    | ~ spl8_286 ),
    inference(backward_demodulation,[],[f2154,f2893])).

fof(f2893,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl8_286 ),
    inference(avatar_component_clause,[],[f2892])).

fof(f2154,plain,
    ( k6_partfun1(k1_xboole_0) = k5_relat_1(sK1,sK2)
    | ~ spl8_221 ),
    inference(avatar_component_clause,[],[f2153])).

fof(f2919,plain,
    ( spl8_287
    | ~ spl8_212
    | ~ spl8_286 ),
    inference(avatar_split_clause,[],[f2897,f2892,f2103,f2917])).

fof(f2103,plain,
    ( spl8_212
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_212])])).

fof(f2897,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_212
    | ~ spl8_286 ),
    inference(backward_demodulation,[],[f2104,f2893])).

fof(f2104,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0))
    | ~ spl8_212 ),
    inference(avatar_component_clause,[],[f2103])).

fof(f2338,plain,
    ( spl8_242
    | ~ spl8_43
    | ~ spl8_57 ),
    inference(avatar_split_clause,[],[f468,f455,f393,f2336])).

fof(f393,plain,
    ( spl8_43
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f455,plain,
    ( spl8_57
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f468,plain,
    ( ! [X21,X19,X20,X18] :
        ( k1_xboole_0 = X18
        | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_xboole_0(X20) )
    | ~ spl8_43
    | ~ spl8_57 ),
    inference(resolution,[],[f456,f394])).

fof(f394,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f393])).

fof(f456,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f455])).

fof(f2324,plain,
    ( spl8_241
    | ~ spl8_42
    | ~ spl8_57 ),
    inference(avatar_split_clause,[],[f467,f455,f389,f2322])).

fof(f389,plain,
    ( spl8_42
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f467,plain,
    ( ! [X14,X17,X15,X16] :
        ( k1_xboole_0 = X14
        | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_xboole_0(X17) )
    | ~ spl8_42
    | ~ spl8_57 ),
    inference(resolution,[],[f456,f390])).

fof(f390,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_xboole_0(X0) )
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f389])).

fof(f2291,plain,
    ( spl8_237
    | ~ spl8_1
    | ~ spl8_74
    | ~ spl8_118 ),
    inference(avatar_split_clause,[],[f871,f859,f572,f225,f2289])).

fof(f572,plain,
    ( spl8_74
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f859,plain,
    ( spl8_118
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X1,X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
        | ~ v2_funct_1(X4)
        | k1_xboole_0 = X2
        | k2_relset_1(X0,X1,X3) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f871,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK2,X2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X0,sK2)) != X3
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X3
        | k2_relset_1(X1,X2,X0) = X2 )
    | ~ spl8_1
    | ~ spl8_74
    | ~ spl8_118 ),
    inference(subsumption_resolution,[],[f869,f226])).

fof(f869,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,X2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X0,sK2)) != X3
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X3
        | k2_relset_1(X1,X2,X0) = X2 )
    | ~ spl8_74
    | ~ spl8_118 ),
    inference(resolution,[],[f860,f573])).

fof(f573,plain,
    ( v2_funct_1(sK2)
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f572])).

fof(f860,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_funct_1(X4)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X1,X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
        | ~ v1_funct_1(X3)
        | k1_xboole_0 = X2
        | k2_relset_1(X0,X1,X3) = X1 )
    | ~ spl8_118 ),
    inference(avatar_component_clause,[],[f859])).

fof(f2179,plain,
    ( spl8_224
    | ~ spl8_174
    | ~ spl8_182 ),
    inference(avatar_split_clause,[],[f2079,f1334,f1279,f2177])).

fof(f1279,plain,
    ( spl8_174
  <=> ! [X0] :
        ( k6_relat_1(sK0) != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_174])])).

fof(f2079,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_174
    | ~ spl8_182 ),
    inference(backward_demodulation,[],[f1280,f1335])).

fof(f1335,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_182 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1280,plain,
    ( ! [X0] :
        ( k6_relat_1(sK0) != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_174 ),
    inference(avatar_component_clause,[],[f1279])).

fof(f2155,plain,
    ( spl8_221
    | ~ spl8_111
    | ~ spl8_182 ),
    inference(avatar_split_clause,[],[f2068,f1334,f796,f2153])).

fof(f796,plain,
    ( spl8_111
  <=> k6_partfun1(sK0) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).

fof(f2068,plain,
    ( k6_partfun1(k1_xboole_0) = k5_relat_1(sK1,sK2)
    | ~ spl8_111
    | ~ spl8_182 ),
    inference(backward_demodulation,[],[f797,f1335])).

fof(f797,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,sK2)
    | ~ spl8_111 ),
    inference(avatar_component_clause,[],[f796])).

fof(f2121,plain,
    ( ~ spl8_215
    | spl8_101
    | ~ spl8_182 ),
    inference(avatar_split_clause,[],[f2067,f1334,f736,f2119])).

fof(f2067,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))
    | spl8_101
    | ~ spl8_182 ),
    inference(backward_demodulation,[],[f737,f1335])).

fof(f2105,plain,
    ( spl8_212
    | ~ spl8_126
    | ~ spl8_182 ),
    inference(avatar_split_clause,[],[f2072,f1334,f931,f2103])).

fof(f931,plain,
    ( spl8_126
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f2072,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0))
    | ~ spl8_126
    | ~ spl8_182 ),
    inference(backward_demodulation,[],[f932,f1335])).

fof(f932,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl8_126 ),
    inference(avatar_component_clause,[],[f931])).

fof(f2101,plain,
    ( spl8_211
    | ~ spl8_123
    | ~ spl8_182 ),
    inference(avatar_split_clause,[],[f2070,f1334,f906,f2099])).

fof(f906,plain,
    ( spl8_123
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).

fof(f2070,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl8_123
    | ~ spl8_182 ),
    inference(backward_demodulation,[],[f907,f1335])).

fof(f907,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl8_123 ),
    inference(avatar_component_clause,[],[f906])).

fof(f2003,plain,
    ( spl8_208
    | ~ spl8_8
    | ~ spl8_182 ),
    inference(avatar_split_clause,[],[f1968,f1334,f253,f2001])).

fof(f1968,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_8
    | ~ spl8_182 ),
    inference(backward_demodulation,[],[f254,f1335])).

fof(f1912,plain,
    ( spl8_205
    | ~ spl8_7
    | ~ spl8_182 ),
    inference(avatar_split_clause,[],[f1879,f1334,f249,f1910])).

fof(f1879,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_7
    | ~ spl8_182 ),
    inference(backward_demodulation,[],[f250,f1335])).

fof(f1874,plain,
    ( spl8_204
    | ~ spl8_125
    | ~ spl8_179 ),
    inference(avatar_split_clause,[],[f1846,f1305,f913,f1872])).

fof(f913,plain,
    ( spl8_125
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_125])])).

fof(f1305,plain,
    ( spl8_179
  <=> k6_partfun1(sK0) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_179])])).

fof(f1846,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ spl8_125
    | ~ spl8_179 ),
    inference(backward_demodulation,[],[f914,f1790])).

fof(f1790,plain,
    ( k6_partfun1(sK0) = k6_relat_1(sK0)
    | ~ spl8_179 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f914,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_partfun1(sK0)
    | ~ spl8_125 ),
    inference(avatar_component_clause,[],[f913])).

fof(f1791,plain,
    ( spl8_182
    | spl8_179
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_122
    | ~ spl8_201 ),
    inference(avatar_split_clause,[],[f1714,f1705,f888,f249,f233,f1305,f1334])).

fof(f888,plain,
    ( spl8_122
  <=> sK0 = k2_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f1705,plain,
    ( spl8_201
  <=> ! [X1,X0] :
        ( k6_partfun1(X1) = k6_relat_1(sK0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_201])])).

fof(f1714,plain,
    ( k6_partfun1(sK0) = k6_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_122
    | ~ spl8_201 ),
    inference(subsumption_resolution,[],[f1713,f250])).

fof(f1713,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k6_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl8_3
    | ~ spl8_122
    | ~ spl8_201 ),
    inference(subsumption_resolution,[],[f1710,f234])).

fof(f1710,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k6_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl8_122
    | ~ spl8_201 ),
    inference(trivial_inequality_removal,[],[f1709])).

fof(f1709,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k6_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl8_122
    | ~ spl8_201 ),
    inference(superposition,[],[f1706,f889])).

fof(f889,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl8_122 ),
    inference(avatar_component_clause,[],[f888])).

fof(f1706,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k6_partfun1(X1) = k6_relat_1(sK0)
        | k1_xboole_0 = X1 )
    | ~ spl8_201 ),
    inference(avatar_component_clause,[],[f1705])).

fof(f1707,plain,
    ( spl8_201
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_56
    | ~ spl8_74
    | ~ spl8_80
    | ~ spl8_109
    | ~ spl8_122 ),
    inference(avatar_split_clause,[],[f897,f888,f789,f615,f572,f447,f249,f225,f1705])).

fof(f615,plain,
    ( spl8_80
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f789,plain,
    ( spl8_109
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) != X1
        | ~ v2_funct_1(X2)
        | k1_xboole_0 = X1
        | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f897,plain,
    ( ! [X0,X1] :
        ( k6_partfun1(X1) = k6_relat_1(sK0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | k1_xboole_0 = X1 )
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_56
    | ~ spl8_74
    | ~ spl8_80
    | ~ spl8_109
    | ~ spl8_122 ),
    inference(backward_demodulation,[],[f808,f896])).

fof(f896,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl8_7
    | ~ spl8_56
    | ~ spl8_122 ),
    inference(subsumption_resolution,[],[f891,f250])).

fof(f891,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_56
    | ~ spl8_122 ),
    inference(superposition,[],[f889,f448])).

fof(f808,plain,
    ( ! [X0,X1] :
        ( k6_partfun1(X1) = k6_relat_1(k2_relat_1(sK2))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | k1_xboole_0 = X1 )
    | ~ spl8_1
    | ~ spl8_74
    | ~ spl8_80
    | ~ spl8_109 ),
    inference(forward_demodulation,[],[f807,f616])).

fof(f616,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f615])).

fof(f807,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | k1_xboole_0 = X1
        | k6_partfun1(X1) = k5_relat_1(k2_funct_1(sK2),sK2) )
    | ~ spl8_1
    | ~ spl8_74
    | ~ spl8_109 ),
    inference(subsumption_resolution,[],[f805,f226])).

fof(f805,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_1(sK2)
        | k1_xboole_0 = X1
        | k6_partfun1(X1) = k5_relat_1(k2_funct_1(sK2),sK2) )
    | ~ spl8_74
    | ~ spl8_109 ),
    inference(resolution,[],[f790,f573])).

fof(f790,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) != X1
        | ~ v1_funct_1(X2)
        | k1_xboole_0 = X1
        | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) )
    | ~ spl8_109 ),
    inference(avatar_component_clause,[],[f789])).

fof(f1701,plain,
    ( spl8_200
    | ~ spl8_152
    | ~ spl8_185 ),
    inference(avatar_split_clause,[],[f1369,f1357,f1159,f1699])).

fof(f1159,plain,
    ( spl8_152
  <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_152])])).

fof(f1357,plain,
    ( spl8_185
  <=> ! [X8] :
        ( ~ r1_tarski(X8,k1_xboole_0)
        | k1_xboole_0 = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_185])])).

fof(f1369,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_152
    | ~ spl8_185 ),
    inference(resolution,[],[f1358,f1160])).

fof(f1160,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl8_152 ),
    inference(avatar_component_clause,[],[f1159])).

fof(f1358,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k1_xboole_0)
        | k1_xboole_0 = X8 )
    | ~ spl8_185 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f1359,plain,
    ( spl8_185
    | ~ spl8_32
    | ~ spl8_53
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f506,f475,f435,f349,f1357])).

fof(f349,plain,
    ( spl8_32
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f475,plain,
    ( spl8_60
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK4(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f506,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k1_xboole_0)
        | k1_xboole_0 = X8 )
    | ~ spl8_32
    | ~ spl8_53
    | ~ spl8_60 ),
    inference(forward_demodulation,[],[f493,f486])).

fof(f486,plain,
    ( ! [X0] : k1_xboole_0 = sK4(X0)
    | ~ spl8_53
    | ~ spl8_60 ),
    inference(resolution,[],[f476,f436])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(X1)))
        | k1_xboole_0 = X0 )
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f475])).

fof(f493,plain,
    ( ! [X8,X9] :
        ( k1_xboole_0 = X8
        | ~ r1_tarski(X8,sK4(X9)) )
    | ~ spl8_32
    | ~ spl8_60 ),
    inference(resolution,[],[f476,f350])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f349])).

fof(f1339,plain,
    ( spl8_181
    | spl8_182
    | ~ spl8_183
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_180 ),
    inference(avatar_split_clause,[],[f1329,f1316,f931,f913,f253,f249,f241,f233,f229,f225,f1337,f1334,f1331])).

fof(f1316,plain,
    ( spl8_180
  <=> ! [X1,X3,X0,X2] :
        ( k2_relat_1(X2) != X1
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X2)
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k2_funct_1(X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_180])])).

fof(f1329,plain,
    ( sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_180 ),
    inference(subsumption_resolution,[],[f1328,f230])).

fof(f1328,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_180 ),
    inference(subsumption_resolution,[],[f1327,f250])).

fof(f1327,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_180 ),
    inference(subsumption_resolution,[],[f1326,f234])).

fof(f1326,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_180 ),
    inference(subsumption_resolution,[],[f1325,f226])).

fof(f1325,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_180 ),
    inference(subsumption_resolution,[],[f1324,f254])).

fof(f1324,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_5
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_180 ),
    inference(subsumption_resolution,[],[f1323,f242])).

fof(f1323,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_125
    | ~ spl8_126
    | ~ spl8_180 ),
    inference(subsumption_resolution,[],[f1321,f932])).

fof(f1321,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_125
    | ~ spl8_180 ),
    inference(duplicate_literal_removal,[],[f1320])).

fof(f1320,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl8_125
    | ~ spl8_180 ),
    inference(superposition,[],[f1317,f914])).

fof(f1317,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X2)
        | k2_relat_1(X2) != X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k2_funct_1(X2) = X3 )
    | ~ spl8_180 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f1318,plain,
    ( spl8_180
    | ~ spl8_56
    | ~ spl8_119 ),
    inference(avatar_split_clause,[],[f882,f874,f447,f1316])).

fof(f874,plain,
    ( spl8_119
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X0,X1,X2) != X1
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k2_funct_1(X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f882,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_relat_1(X2) != X1
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X2)
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k2_funct_1(X2) = X3 )
    | ~ spl8_56
    | ~ spl8_119 ),
    inference(duplicate_literal_removal,[],[f881])).

fof(f881,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_relat_1(X2) != X1
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X2)
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k2_funct_1(X2) = X3
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_56
    | ~ spl8_119 ),
    inference(superposition,[],[f875,f448])).

fof(f875,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_relset_1(X0,X1,X2) != X1
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X2)
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k2_funct_1(X2) = X3 )
    | ~ spl8_119 ),
    inference(avatar_component_clause,[],[f874])).

fof(f1281,plain,
    ( ~ spl8_81
    | spl8_174
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_56
    | ~ spl8_74
    | ~ spl8_102
    | ~ spl8_122 ),
    inference(avatar_split_clause,[],[f898,f888,f745,f572,f447,f249,f225,f1279,f618])).

fof(f745,plain,
    ( spl8_102
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(X1)
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
        | k2_funct_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f898,plain,
    ( ! [X0] :
        ( k6_relat_1(sK0) != k5_relat_1(X0,sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | k2_funct_1(sK2) = X0 )
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_56
    | ~ spl8_74
    | ~ spl8_102
    | ~ spl8_122 ),
    inference(backward_demodulation,[],[f759,f896])).

fof(f759,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0 )
    | ~ spl8_1
    | ~ spl8_74
    | ~ spl8_102 ),
    inference(subsumption_resolution,[],[f757,f226])).

fof(f757,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(X0,sK2)
        | k2_funct_1(sK2) = X0 )
    | ~ spl8_74
    | ~ spl8_102 ),
    inference(resolution,[],[f746,f573])).

fof(f746,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k2_relat_1(X1)
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
        | k2_funct_1(X0) = X1 )
    | ~ spl8_102 ),
    inference(avatar_component_clause,[],[f745])).

fof(f1161,plain,
    ( spl8_152
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_23
    | ~ spl8_129 ),
    inference(avatar_split_clause,[],[f984,f974,f313,f281,f277,f1159])).

fof(f277,plain,
    ( spl8_14
  <=> ! [X0] : v1_relat_1(sK3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f281,plain,
    ( spl8_15
  <=> ! [X0] : v1_funct_1(sK3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f313,plain,
    ( spl8_23
  <=> ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f974,plain,
    ( spl8_129
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).

fof(f984,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_23
    | ~ spl8_129 ),
    inference(subsumption_resolution,[],[f983,f282])).

fof(f282,plain,
    ( ! [X0] : v1_funct_1(sK3(X0))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f281])).

fof(f983,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | ~ v1_funct_1(sK3(X0)) )
    | ~ spl8_14
    | ~ spl8_23
    | ~ spl8_129 ),
    inference(subsumption_resolution,[],[f981,f278])).

fof(f278,plain,
    ( ! [X0] : v1_relat_1(sK3(X0))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f277])).

fof(f981,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | ~ v1_relat_1(sK3(X0))
        | ~ v1_funct_1(sK3(X0)) )
    | ~ spl8_23
    | ~ spl8_129 ),
    inference(superposition,[],[f975,f314])).

fof(f314,plain,
    ( ! [X0] : k1_relat_1(sK3(X0)) = X0
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f313])).

fof(f975,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl8_129 ),
    inference(avatar_component_clause,[],[f974])).

fof(f1103,plain,
    ( spl8_111
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_104
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f945,f913,f753,f253,f249,f229,f225,f796])).

fof(f753,plain,
    ( spl8_104
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f945,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_104
    | ~ spl8_125 ),
    inference(subsumption_resolution,[],[f944,f230])).

fof(f944,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_104
    | ~ spl8_125 ),
    inference(subsumption_resolution,[],[f943,f250])).

fof(f943,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_104
    | ~ spl8_125 ),
    inference(subsumption_resolution,[],[f942,f226])).

fof(f942,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl8_8
    | ~ spl8_104
    | ~ spl8_125 ),
    inference(subsumption_resolution,[],[f936,f254])).

fof(f936,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl8_104
    | ~ spl8_125 ),
    inference(superposition,[],[f914,f754])).

fof(f754,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4) )
    | ~ spl8_104 ),
    inference(avatar_component_clause,[],[f753])).

fof(f976,plain,
    ( spl8_129
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_29
    | ~ spl8_73 ),
    inference(avatar_split_clause,[],[f645,f568,f337,f261,f257,f974])).

fof(f257,plain,
    ( spl8_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f261,plain,
    ( spl8_10
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f337,plain,
    ( spl8_29
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v5_funct_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f568,plain,
    ( spl8_73
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v5_funct_1(X1,X0)
        | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f645,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) )
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_29
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f644,f262])).

fof(f262,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f261])).

fof(f644,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) )
    | ~ spl8_9
    | ~ spl8_29
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f643,f258])).

fof(f258,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f257])).

fof(f643,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) )
    | ~ spl8_29
    | ~ spl8_73 ),
    inference(duplicate_literal_removal,[],[f642])).

fof(f642,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_29
    | ~ spl8_73 ),
    inference(resolution,[],[f569,f338])).

fof(f338,plain,
    ( ! [X0] :
        ( v5_funct_1(k1_xboole_0,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f337])).

fof(f569,plain,
    ( ! [X0,X1] :
        ( ~ v5_funct_1(X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X0)
        | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) )
    | ~ spl8_73 ),
    inference(avatar_component_clause,[],[f568])).

fof(f964,plain,
    ( spl8_127
    | ~ spl8_7
    | ~ spl8_56
    | ~ spl8_94
    | ~ spl8_122 ),
    inference(avatar_split_clause,[],[f899,f888,f697,f447,f249,f962])).

fof(f697,plain,
    ( spl8_94
  <=> k2_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f899,plain,
    ( sK0 = k2_relat_1(k6_relat_1(sK0))
    | ~ spl8_7
    | ~ spl8_56
    | ~ spl8_94
    | ~ spl8_122 ),
    inference(backward_demodulation,[],[f698,f896])).

fof(f698,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f697])).

fof(f933,plain,
    ( spl8_126
    | ~ spl8_17
    | ~ spl8_125 ),
    inference(avatar_split_clause,[],[f929,f913,f289,f931])).

fof(f289,plain,
    ( spl8_17
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f929,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl8_17
    | ~ spl8_125 ),
    inference(backward_demodulation,[],[f290,f914])).

fof(f290,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f289])).

fof(f928,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_105
    | spl8_124 ),
    inference(avatar_contradiction_clause,[],[f927])).

fof(f927,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_105
    | spl8_124 ),
    inference(subsumption_resolution,[],[f926,f230])).

fof(f926,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_105
    | spl8_124 ),
    inference(subsumption_resolution,[],[f925,f250])).

fof(f925,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_105
    | spl8_124 ),
    inference(subsumption_resolution,[],[f924,f226])).

fof(f924,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl8_8
    | ~ spl8_105
    | spl8_124 ),
    inference(subsumption_resolution,[],[f917,f254])).

fof(f917,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl8_105
    | spl8_124 ),
    inference(resolution,[],[f911,f763])).

fof(f763,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4) )
    | ~ spl8_105 ),
    inference(avatar_component_clause,[],[f762])).

fof(f762,plain,
    ( spl8_105
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f911,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl8_124 ),
    inference(avatar_component_clause,[],[f910])).

fof(f910,plain,
    ( spl8_124
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f915,plain,
    ( ~ spl8_124
    | spl8_125
    | ~ spl8_17
    | ~ spl8_28
    | ~ spl8_95 ),
    inference(avatar_split_clause,[],[f713,f701,f333,f289,f913,f910])).

fof(f701,plain,
    ( spl8_95
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | X2 = X3
        | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).

fof(f713,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_17
    | ~ spl8_28
    | ~ spl8_95 ),
    inference(subsumption_resolution,[],[f710,f334])).

fof(f710,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_17
    | ~ spl8_95 ),
    inference(resolution,[],[f702,f290])).

fof(f702,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_relset_1(X0,X1,X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | X2 = X3
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_95 ),
    inference(avatar_component_clause,[],[f701])).

fof(f908,plain,
    ( spl8_123
    | ~ spl8_7
    | ~ spl8_56
    | ~ spl8_122 ),
    inference(avatar_split_clause,[],[f896,f888,f447,f249,f906])).

fof(f890,plain,
    ( spl8_122
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(avatar_split_clause,[],[f850,f839,f289,f253,f249,f241,f233,f229,f225,f888])).

fof(f839,plain,
    ( spl8_117
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
        | k2_relset_1(X0,X1,X2) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f850,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(subsumption_resolution,[],[f849,f226])).

fof(f849,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(subsumption_resolution,[],[f848,f254])).

fof(f848,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(subsumption_resolution,[],[f847,f242])).

fof(f847,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(subsumption_resolution,[],[f846,f230])).

fof(f846,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(subsumption_resolution,[],[f845,f250])).

fof(f845,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl8_3
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(subsumption_resolution,[],[f842,f234])).

fof(f842,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(resolution,[],[f840,f290])).

fof(f840,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X2)
        | k2_relset_1(X0,X1,X2) = X1 )
    | ~ spl8_117 ),
    inference(avatar_component_clause,[],[f839])).

fof(f876,plain,(
    spl8_119 ),
    inference(avatar_split_clause,[],[f223,f874])).

fof(f223,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k2_funct_1(X2) = X3 ) ),
    inference(subsumption_resolution,[],[f199,f197])).

fof(f197,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f199,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k2_funct_1(X2) = X3 ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f861,plain,(
    spl8_118 ),
    inference(avatar_split_clause,[],[f203,f859])).

fof(f203,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
      | ~ v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) = X1 ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k2_relset_1(X0,X1,X3) = X1
          | k1_xboole_0 = X2
          | ~ v2_funct_1(X4)
          | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k2_relset_1(X0,X1,X3) = X1
          | k1_xboole_0 = X2
          | ~ v2_funct_1(X4)
          | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(f841,plain,(
    spl8_117 ),
    inference(avatar_split_clause,[],[f196,f839])).

fof(f196,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f791,plain,(
    spl8_109 ),
    inference(avatar_split_clause,[],[f195,f789])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f764,plain,(
    spl8_105 ),
    inference(avatar_split_clause,[],[f209,f762])).

fof(f209,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f755,plain,(
    spl8_104 ),
    inference(avatar_split_clause,[],[f207,f753])).

fof(f207,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f116])).

fof(f116,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f747,plain,(
    spl8_102 ),
    inference(avatar_split_clause,[],[f148,f745])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f717,plain,(
    spl8_97 ),
    inference(avatar_split_clause,[],[f179,f715])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f703,plain,(
    spl8_95 ),
    inference(avatar_split_clause,[],[f205,f701])).

fof(f205,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f112])).

fof(f112,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f699,plain,
    ( ~ spl8_81
    | spl8_94
    | ~ spl8_1
    | ~ spl8_59
    | ~ spl8_74
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f625,f615,f572,f471,f225,f697,f618])).

fof(f471,plain,
    ( spl8_59
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f625,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_59
    | ~ spl8_74
    | ~ spl8_80 ),
    inference(backward_demodulation,[],[f585,f616])).

fof(f585,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ spl8_1
    | ~ spl8_59
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f581,f226])).

fof(f581,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ spl8_59
    | ~ spl8_74 ),
    inference(resolution,[],[f573,f472])).

fof(f472,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f471])).

fof(f623,plain,
    ( ~ spl8_7
    | ~ spl8_39
    | spl8_81 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_39
    | spl8_81 ),
    inference(unit_resulting_resolution,[],[f250,f619,f378])).

fof(f378,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl8_39
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f619,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_81 ),
    inference(avatar_component_clause,[],[f618])).

fof(f620,plain,
    ( spl8_80
    | ~ spl8_81
    | ~ spl8_1
    | ~ spl8_62
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f583,f572,f483,f225,f618,f615])).

fof(f483,plain,
    ( spl8_62
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f583,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl8_1
    | ~ spl8_62
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f579,f226])).

fof(f579,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl8_62
    | ~ spl8_74 ),
    inference(resolution,[],[f573,f484])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) )
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f483])).

fof(f574,plain,
    ( spl8_74
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f564,f517,f249,f237,f225,f572])).

fof(f237,plain,
    ( spl8_4
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f517,plain,
    ( spl8_64
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v3_funct_2(X2,X0,X1)
        | v2_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f564,plain,
    ( v2_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_64 ),
    inference(subsumption_resolution,[],[f563,f250])).

fof(f563,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_64 ),
    inference(subsumption_resolution,[],[f561,f226])).

fof(f561,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ spl8_4
    | ~ spl8_64 ),
    inference(resolution,[],[f518,f238])).

fof(f238,plain,
    ( v3_funct_2(sK2,sK0,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f237])).

fof(f518,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v2_funct_1(X2) )
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f517])).

fof(f570,plain,(
    spl8_73 ),
    inference(avatar_split_clause,[],[f147,f568])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v5_funct_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
          | ~ v5_funct_1(X1,X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
          | ~ v5_funct_1(X1,X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v5_funct_1(X1,X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
         => r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).

fof(f519,plain,(
    spl8_64 ),
    inference(avatar_split_clause,[],[f192,f517])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f514,plain,
    ( spl8_63
    | ~ spl8_16
    | ~ spl8_53
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f499,f475,f435,f285,f512])).

fof(f285,plain,
    ( spl8_16
  <=> ! [X0] : v1_xboole_0(sK4(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f499,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_16
    | ~ spl8_53
    | ~ spl8_60 ),
    inference(backward_demodulation,[],[f286,f486])).

fof(f286,plain,
    ( ! [X0] : v1_xboole_0(sK4(X0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f285])).

fof(f485,plain,(
    spl8_62 ),
    inference(avatar_split_clause,[],[f146,f483])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f477,plain,
    ( spl8_60
    | ~ spl8_16
    | ~ spl8_57 ),
    inference(avatar_split_clause,[],[f462,f455,f285,f475])).

fof(f462,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK4(X1))) )
    | ~ spl8_16
    | ~ spl8_57 ),
    inference(resolution,[],[f456,f286])).

fof(f473,plain,(
    spl8_59 ),
    inference(avatar_split_clause,[],[f144,f471])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f457,plain,
    ( spl8_57
    | ~ spl8_41
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f453,f425,f385,f455])).

fof(f385,plain,
    ( spl8_41
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f425,plain,
    ( spl8_51
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k1_xboole_0 = X1
        | r2_hidden(sK6(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f453,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_xboole_0(X1) )
    | ~ spl8_41
    | ~ spl8_51 ),
    inference(condensation,[],[f451])).

fof(f451,plain,
    ( ! [X4,X5,X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
        | ~ m1_subset_1(X3,k1_zfmisc_1(X5))
        | ~ v1_xboole_0(X5) )
    | ~ spl8_41
    | ~ spl8_51 ),
    inference(resolution,[],[f426,f386])).

fof(f386,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f385])).

fof(f426,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,X1),X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f425])).

fof(f449,plain,(
    spl8_56 ),
    inference(avatar_split_clause,[],[f184,f447])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f437,plain,
    ( spl8_53
    | ~ spl8_18
    | ~ spl8_26
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f433,f413,f325,f293,f435])).

fof(f293,plain,
    ( spl8_18
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f325,plain,
    ( spl8_26
  <=> ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f413,plain,
    ( spl8_48
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f433,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl8_18
    | ~ spl8_26
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f432,f294])).

fof(f294,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f293])).

fof(f432,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl8_26
    | ~ spl8_48 ),
    inference(superposition,[],[f414,f326])).

fof(f326,plain,
    ( ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f325])).

fof(f414,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f413])).

fof(f427,plain,(
    spl8_51 ),
    inference(avatar_split_clause,[],[f171,f425])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f419,plain,(
    spl8_49 ),
    inference(avatar_split_clause,[],[f219,f417])).

fof(f219,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f204])).

fof(f204,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f415,plain,(
    spl8_48 ),
    inference(avatar_split_clause,[],[f176,f413])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f395,plain,(
    spl8_43 ),
    inference(avatar_split_clause,[],[f163,f393])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f391,plain,(
    spl8_42 ),
    inference(avatar_split_clause,[],[f162,f389])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f387,plain,(
    spl8_41 ),
    inference(avatar_split_clause,[],[f201,f385])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f379,plain,(
    spl8_39 ),
    inference(avatar_split_clause,[],[f183,f377])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f351,plain,(
    spl8_32 ),
    inference(avatar_split_clause,[],[f180,f349])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f339,plain,(
    spl8_29 ),
    inference(avatar_split_clause,[],[f142,f337])).

fof(f142,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f335,plain,(
    spl8_28 ),
    inference(avatar_split_clause,[],[f139,f333])).

fof(f139,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f331,plain,(
    spl8_27 ),
    inference(avatar_split_clause,[],[f133,f329])).

fof(f133,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f327,plain,(
    spl8_26 ),
    inference(avatar_split_clause,[],[f221,f325])).

fof(f221,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f212,f130])).

fof(f130,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f212,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f315,plain,(
    spl8_23 ),
    inference(avatar_split_clause,[],[f153,f313])).

fof(f153,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(f295,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f130,f293])).

fof(f291,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f124,f289])).

fof(f124,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f50])).

fof(f50,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f287,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f155,f285])).

fof(f155,plain,(
    ! [X0] : v1_xboole_0(sK4(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f283,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f152,f281])).

fof(f152,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f69])).

fof(f279,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f151,f277])).

fof(f151,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f69])).

fof(f271,plain,(
    ~ spl8_12 ),
    inference(avatar_split_clause,[],[f125,f269])).

fof(f125,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f263,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f136,f261])).

fof(f136,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f259,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f134,f257])).

fof(f134,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

fof(f255,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f129,f253])).

fof(f129,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f251,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f123,f249])).

fof(f123,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f247,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f128,f245])).

fof(f128,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f243,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f127,f241])).

fof(f127,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f239,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f122,f237])).

fof(f122,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f235,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f121,f233])).

fof(f121,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f231,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f126,f229])).

fof(f126,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f227,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f120,f225])).

fof(f120,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (6608)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_16 on theBenchmark
% 0.21/0.47  % (6624)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (6614)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_14 on theBenchmark
% 1.43/0.54  % (6622)dis+11_28_av=off:fsr=off:irw=on:lcm=predicate:nm=2:newcnf=on:nwc=5:sp=occurrence:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (6602)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_2 on theBenchmark
% 1.43/0.55  % (6605)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.55  % (6623)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_72 on theBenchmark
% 1.55/0.56  % (6601)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_3 on theBenchmark
% 1.55/0.56  % (6615)ott+1_8_av=off:bd=off:bs=on:cond=on:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:lwlo=on:nwc=1:sos=on_10 on theBenchmark
% 1.55/0.56  % (6606)dis+1011_10_aac=none:add=large:afp=10000:afq=1.1:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=6:newcnf=on:nwc=2.5:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.56  % (6619)dis+1010_4_afp=10000:afq=1.2:anc=none:irw=on:lma=on:nm=64:nwc=10:sas=z3:sac=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.56  % (6607)ott+1002_2_av=off:bd=preordered:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_22 on theBenchmark
% 1.55/0.57  % (6629)lrs+10_6_aac=none:acc=model:add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bd=off:ccuc=small_ones:irw=on:lcm=reverse:nm=0:nwc=1:nicw=on:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.57  % (6603)ott+1010_5:4_av=off:bd=off:fde=none:irw=on:lma=on:nm=32:nwc=2.5:sd=2:ss=axioms:st=3.0:urr=on_5 on theBenchmark
% 1.55/0.57  % (6627)ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.55/0.57  % (6625)lrs+1011_4:1_av=off:fsr=off:irw=on:nwc=1:stl=30:sd=4:ss=axioms:st=1.5:sp=reverse_arity_12 on theBenchmark
% 1.55/0.57  % (6604)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_3 on theBenchmark
% 1.55/0.57  % (6621)ott+1004_12_awrs=converge:awrsf=64:aac=none:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bs=on:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=on:lma=on:nwc=5:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=ec_only_2 on theBenchmark
% 1.55/0.57  % (6617)dis+11_3:1_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:irw=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 1.55/0.58  % (6609)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.55/0.58  % (6610)dis+11_4_afr=on:afp=1000:afq=1.4:amm=off:anc=none:lcm=reverse:lma=on:lwlo=on:nm=6:newcnf=on:nwc=1:sd=2:ss=axioms:st=2.0:sp=reverse_arity_2 on theBenchmark
% 1.55/0.58  % (6613)lrs+1003_2_acc=on:afp=4000:afq=2.0:amm=sco:bd=off:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:nm=64:newcnf=on:nwc=2.5:nicw=on:stl=30:urr=ec_only_8 on theBenchmark
% 1.55/0.58  % (6611)dis-3_5_av=off:cond=on:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:sos=on:sp=reverse_arity_3 on theBenchmark
% 1.55/0.58  % (6628)dis+1003_64_add=off:afr=on:afp=100000:afq=1.1:anc=none:cond=fast:fde=none:irw=on:nm=6:newcnf=on:nwc=1.3:uhcvi=on_5 on theBenchmark
% 1.55/0.59  % (6630)ott+11_8_amm=off:anc=none:bsr=on:cond=on:irw=on:nm=2:nwc=1.1:ss=axioms:st=2.0:sac=on_1 on theBenchmark
% 1.55/0.59  % (6602)Refutation not found, incomplete strategy% (6602)------------------------------
% 1.55/0.59  % (6602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (6602)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (6602)Memory used [KB]: 11129
% 1.55/0.59  % (6602)Time elapsed: 0.168 s
% 1.55/0.59  % (6602)------------------------------
% 1.55/0.59  % (6602)------------------------------
% 1.55/0.59  % (6618)lrs+1002_3_aac=none:acc=on:add=off:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1.1:nicw=on:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=occurrence:updr=off_24 on theBenchmark
% 1.55/0.59  % (6620)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_36 on theBenchmark
% 1.55/0.59  % (6616)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_4 on theBenchmark
% 1.55/0.60  % (6612)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_5 on theBenchmark
% 1.55/0.60  % (6626)dis+11_5_av=off:bd=off:bs=unit_only:bsr=on:cond=on:lcm=reverse:nm=0:nwc=1.2_5 on theBenchmark
% 2.95/0.77  % (6658)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_4 on theBenchmark
% 3.14/0.81  % (6617)Time limit reached!
% 3.14/0.81  % (6617)------------------------------
% 3.14/0.81  % (6617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.81  % (6617)Termination reason: Time limit
% 3.14/0.81  
% 3.14/0.81  % (6617)Memory used [KB]: 7036
% 3.14/0.81  % (6617)Time elapsed: 0.406 s
% 3.14/0.81  % (6617)------------------------------
% 3.14/0.81  % (6617)------------------------------
% 3.14/0.81  % (6630)Time limit reached!
% 3.14/0.81  % (6630)------------------------------
% 3.14/0.81  % (6630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.81  % (6630)Termination reason: Time limit
% 3.14/0.81  
% 3.14/0.81  % (6630)Memory used [KB]: 8187
% 3.14/0.81  % (6630)Time elapsed: 0.413 s
% 3.14/0.81  % (6630)------------------------------
% 3.14/0.81  % (6630)------------------------------
% 3.80/0.90  % (6610)Time limit reached!
% 3.80/0.90  % (6610)------------------------------
% 3.80/0.90  % (6610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.80/0.90  % (6610)Termination reason: Time limit
% 3.80/0.90  
% 3.80/0.90  % (6610)Memory used [KB]: 7675
% 3.80/0.90  % (6610)Time elapsed: 0.503 s
% 3.80/0.90  % (6610)------------------------------
% 3.80/0.90  % (6610)------------------------------
% 3.80/0.90  % (6629)Time limit reached!
% 3.80/0.90  % (6629)------------------------------
% 3.80/0.90  % (6629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.80/0.90  % (6629)Termination reason: Time limit
% 3.80/0.90  
% 3.80/0.90  % (6629)Memory used [KB]: 8827
% 3.80/0.90  % (6629)Time elapsed: 0.506 s
% 3.80/0.90  % (6629)------------------------------
% 3.80/0.90  % (6629)------------------------------
% 3.80/0.91  % (6606)Time limit reached!
% 3.80/0.91  % (6606)------------------------------
% 3.80/0.91  % (6606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.80/0.91  % (6606)Termination reason: Time limit
% 3.80/0.91  
% 3.80/0.91  % (6606)Memory used [KB]: 13048
% 3.80/0.91  % (6606)Time elapsed: 0.513 s
% 3.80/0.91  % (6606)------------------------------
% 3.80/0.91  % (6606)------------------------------
% 3.80/0.92  % (6619)Time limit reached!
% 3.80/0.92  % (6619)------------------------------
% 3.80/0.92  % (6619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.80/0.92  % (6619)Termination reason: Time limit
% 3.80/0.92  % (6619)Termination phase: Saturation
% 3.80/0.92  
% 3.80/0.92  % (6619)Memory used [KB]: 2558
% 3.80/0.92  % (6619)Time elapsed: 0.519 s
% 3.80/0.92  % (6619)------------------------------
% 3.80/0.92  % (6619)------------------------------
% 4.36/0.93  % (6621)Time limit reached!
% 4.36/0.93  % (6621)------------------------------
% 4.36/0.93  % (6621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.93  % (6621)Termination reason: Time limit
% 4.36/0.93  % (6621)Termination phase: Saturation
% 4.36/0.93  
% 4.36/0.93  % (6621)Memory used [KB]: 7419
% 4.36/0.93  % (6621)Time elapsed: 0.500 s
% 4.36/0.93  % (6621)------------------------------
% 4.36/0.93  % (6621)------------------------------
% 4.36/0.93  % (6605)Time limit reached!
% 4.36/0.93  % (6605)------------------------------
% 4.36/0.93  % (6605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.93  % (6605)Termination reason: Time limit
% 4.36/0.93  % (6605)Termination phase: Saturation
% 4.36/0.93  
% 4.36/0.93  % (6605)Memory used [KB]: 8827
% 4.36/0.93  % (6605)Time elapsed: 0.500 s
% 4.36/0.93  % (6605)------------------------------
% 4.36/0.93  % (6605)------------------------------
% 4.36/0.93  % (6624)Time limit reached!
% 4.36/0.93  % (6624)------------------------------
% 4.36/0.93  % (6624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.93  % (6624)Termination reason: Time limit
% 4.36/0.93  
% 4.36/0.93  % (6624)Memory used [KB]: 17142
% 4.36/0.93  % (6624)Time elapsed: 0.526 s
% 4.36/0.93  % (6624)------------------------------
% 4.36/0.93  % (6624)------------------------------
% 4.36/0.94  % (6664)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_17 on theBenchmark
% 4.36/0.94  % (6622)Time limit reached!
% 4.36/0.94  % (6622)------------------------------
% 4.36/0.94  % (6622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.94  % (6622)Termination reason: Time limit
% 4.36/0.94  
% 4.36/0.94  % (6622)Memory used [KB]: 9978
% 4.36/0.94  % (6622)Time elapsed: 0.508 s
% 4.36/0.94  % (6622)------------------------------
% 4.36/0.94  % (6622)------------------------------
% 4.36/0.94  % (6663)lrs+10_1_afr=on:afp=100000:afq=1.2:amm=sco:anc=none:br=off:cond=on:gs=on:gsem=on:irw=on:nm=16:nwc=1:stl=30:sac=on:sp=occurrence:urr=on:updr=off_12 on theBenchmark
% 4.64/1.00  % (6601)Time limit reached!
% 4.64/1.00  % (6601)------------------------------
% 4.64/1.00  % (6601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.00  % (6601)Termination reason: Time limit
% 4.64/1.00  
% 4.64/1.00  % (6601)Memory used [KB]: 8571
% 4.64/1.00  % (6601)Time elapsed: 0.604 s
% 4.64/1.00  % (6601)------------------------------
% 4.64/1.00  % (6601)------------------------------
% 4.64/1.02  % (6666)dis+11_32_av=off:ep=RST:fsr=off:lwlo=on:nm=6:nwc=1.1:sd=5:ss=axioms:st=5.0:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 4.64/1.02  % (6611)Time limit reached!
% 4.64/1.02  % (6611)------------------------------
% 4.64/1.02  % (6611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.03  % (6611)Termination reason: Time limit
% 4.64/1.03  
% 4.64/1.03  % (6611)Memory used [KB]: 10106
% 4.64/1.03  % (6611)Time elapsed: 0.621 s
% 4.64/1.03  % (6611)------------------------------
% 4.64/1.03  % (6611)------------------------------
% 4.64/1.03  % (6604)Time limit reached!
% 4.64/1.03  % (6604)------------------------------
% 4.64/1.03  % (6604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.03  % (6604)Termination reason: Time limit
% 4.64/1.03  
% 4.64/1.03  % (6604)Memory used [KB]: 13432
% 4.64/1.03  % (6604)Time elapsed: 0.607 s
% 4.64/1.03  % (6604)------------------------------
% 4.64/1.03  % (6604)------------------------------
% 5.05/1.04  % (6667)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_125 on theBenchmark
% 5.05/1.05  % (6668)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_205 on theBenchmark
% 5.05/1.05  % (6672)dis+11_10_av=off:lma=on:nm=64:nwc=5:sp=reverse_arity_3 on theBenchmark
% 5.05/1.05  % (6670)dis+1002_8_add=large:afp=100000:afq=1.2:amm=off:bs=on:irw=on:nm=2:newcnf=on:nwc=1.1:sos=on:sp=reverse_arity:urr=ec_only:updr=off_259 on theBenchmark
% 5.05/1.06  % (6669)lrs+1011_2:1_av=off:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:stl=30:sd=4:ss=axioms:st=3.0:sp=occurrence_30 on theBenchmark
% 5.05/1.07  % (6665)lrs+10_2:3_afp=1000:afq=1.1:amm=sco:anc=none:er=known:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=2:stl=30:sd=5:ss=axioms:sos=theory:sac=on:sp=occurrence_233 on theBenchmark
% 5.05/1.07  % (6671)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 5.70/1.12  % (6673)ott-11_12_aac=none:afp=100000:afq=1.2:amm=sco:bs=on:bce=on:cond=fast:er=known:gs=on:gsaa=from_current:gsem=off:irw=on:nm=4:nwc=2:sas=z3:sos=all:sp=occurrence:urr=ec_only:updr=off_253 on theBenchmark
% 6.12/1.16  % (6674)ott+10_2:3_add=large:afp=40000:afq=1.1:amm=off:anc=all_dependent:bd=preordered:bs=unit_only:cond=fast:er=filter:gs=on:gsaa=from_current:lma=on:nm=32:nwc=1.1:sas=z3:sac=on:sp=occurrence:urr=ec_only:updr=off_679 on theBenchmark
% 6.36/1.17  % (6675)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_21 on theBenchmark
% 6.36/1.20  % (6609)Time limit reached!
% 6.36/1.20  % (6609)------------------------------
% 6.36/1.20  % (6609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.36/1.20  % (6609)Termination reason: Time limit
% 6.36/1.20  
% 6.36/1.20  % (6609)Memory used [KB]: 13688
% 6.36/1.20  % (6609)Time elapsed: 0.807 s
% 6.36/1.20  % (6609)------------------------------
% 6.36/1.20  % (6609)------------------------------
% 6.88/1.23  % (6616)Time limit reached!
% 6.88/1.23  % (6616)------------------------------
% 6.88/1.23  % (6616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.88/1.23  % (6616)Termination reason: Time limit
% 6.88/1.23  % (6616)Termination phase: Saturation
% 6.88/1.23  
% 6.88/1.23  % (6616)Memory used [KB]: 11385
% 6.88/1.23  % (6616)Time elapsed: 0.800 s
% 6.88/1.23  % (6616)------------------------------
% 6.88/1.23  % (6616)------------------------------
% 7.13/1.30  % (6758)lrs+10_128_acc=model:afp=100000:afq=2.0:anc=all_dependent:bs=on:bsr=on:cond=fast:er=filter:gs=on:gsem=off:lcm=reverse:lma=on:nm=32:nwc=3:stl=30:sac=on:sp=occurrence:urr=ec_only_70 on theBenchmark
% 7.13/1.31  % (6626)Time limit reached!
% 7.13/1.31  % (6626)------------------------------
% 7.13/1.31  % (6626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.13/1.31  % (6626)Termination reason: Time limit
% 7.13/1.31  % (6626)Termination phase: Saturation
% 7.13/1.31  
% 7.13/1.31  % (6626)Memory used [KB]: 7036
% 7.13/1.31  % (6626)Time elapsed: 0.900 s
% 7.13/1.31  % (6626)------------------------------
% 7.13/1.31  % (6626)------------------------------
% 7.13/1.32  % (6603)Time limit reached!
% 7.13/1.32  % (6603)------------------------------
% 7.13/1.32  % (6603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.13/1.32  % (6603)Termination reason: Time limit
% 7.13/1.32  % (6603)Termination phase: Saturation
% 7.13/1.32  
% 7.13/1.32  % (6603)Memory used [KB]: 8571
% 7.13/1.32  % (6603)Time elapsed: 0.914 s
% 7.13/1.32  % (6603)------------------------------
% 7.13/1.32  % (6603)------------------------------
% 7.13/1.33  % (6628)Time limit reached!
% 7.13/1.33  % (6628)------------------------------
% 7.13/1.33  % (6628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.13/1.33  % (6628)Termination reason: Time limit
% 7.13/1.33  % (6628)Termination phase: Saturation
% 7.13/1.33  
% 7.13/1.33  % (6628)Memory used [KB]: 9338
% 7.13/1.33  % (6628)Time elapsed: 0.914 s
% 7.13/1.33  % (6628)------------------------------
% 7.13/1.33  % (6628)------------------------------
% 7.70/1.33  % (6782)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_51 on theBenchmark
% 7.70/1.34  % (6612)Time limit reached!
% 7.70/1.34  % (6612)------------------------------
% 7.70/1.34  % (6612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.70/1.34  % (6612)Termination reason: Time limit
% 7.70/1.34  
% 7.70/1.34  % (6612)Memory used [KB]: 7931
% 7.70/1.34  % (6612)Time elapsed: 0.926 s
% 7.70/1.34  % (6612)------------------------------
% 7.70/1.34  % (6612)------------------------------
% 7.91/1.42  % (6823)lrs+1010_5:4_av=off:bd=off:bsr=on:irw=on:lwlo=on:newcnf=on:nwc=1.1:stl=90:sos=all:sp=occurrence:uhcvi=on_145 on theBenchmark
% 7.91/1.42  % (6658)Time limit reached!
% 7.91/1.42  % (6658)------------------------------
% 7.91/1.42  % (6658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.42  % (6658)Termination reason: Time limit
% 7.91/1.42  
% 7.91/1.42  % (6658)Memory used [KB]: 10746
% 7.91/1.42  % (6658)Time elapsed: 0.802 s
% 7.91/1.42  % (6658)------------------------------
% 7.91/1.42  % (6658)------------------------------
% 8.37/1.45  % (6827)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_59 on theBenchmark
% 8.37/1.45  % (6666)Time limit reached!
% 8.37/1.45  % (6666)------------------------------
% 8.37/1.45  % (6666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.37/1.46  % (6666)Termination reason: Time limit
% 8.37/1.46  
% 8.52/1.47  % (6835)dis+11_5_afp=40000:afq=1.4:anc=none:br=off:cond=on:fsr=off:irw=on:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=2.0:urr=on:updr=off_5 on theBenchmark
% 8.52/1.47  % (6666)Memory used [KB]: 6524
% 8.52/1.47  % (6666)Time elapsed: 0.515 s
% 8.52/1.47  % (6666)------------------------------
% 8.52/1.47  % (6666)------------------------------
% 8.52/1.47  % (6830)lrs+1011_14_av=off:fsr=off:irw=on:nwc=1:stl=30:sos=on:sp=occurrence:urr=ec_only:updr=off_53 on theBenchmark
% 9.12/1.57  % (6853)lrs+1_3:2_aac=none:add=large:anc=all_dependent:bce=on:cond=fast:ep=RST:fsr=off:lma=on:nm=2:nwc=1:stl=30:sos=on:sp=occurrence:urr=on:updr=off:uhcvi=on_5 on theBenchmark
% 9.12/1.58  % (6672)Time limit reached!
% 9.12/1.58  % (6672)------------------------------
% 9.12/1.58  % (6672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.12/1.58  % (6672)Termination reason: Time limit
% 9.12/1.58  % (6672)Termination phase: Saturation
% 9.12/1.58  
% 9.12/1.58  % (6672)Memory used [KB]: 5884
% 9.12/1.58  % (6672)Time elapsed: 0.618 s
% 9.12/1.58  % (6672)------------------------------
% 9.12/1.58  % (6672)------------------------------
% 9.12/1.60  % (6868)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_3 on theBenchmark
% 9.12/1.62  % (6613)Time limit reached!
% 9.12/1.62  % (6613)------------------------------
% 9.12/1.62  % (6613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.12/1.63  % (6613)Termination reason: Time limit
% 9.12/1.63  
% 9.12/1.63  % (6613)Memory used [KB]: 15735
% 9.12/1.63  % (6613)Time elapsed: 1.220 s
% 9.12/1.63  % (6613)------------------------------
% 9.12/1.63  % (6613)------------------------------
% 10.45/1.71  % (6627)Time limit reached!
% 10.45/1.71  % (6627)------------------------------
% 10.45/1.71  % (6627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.45/1.71  % (6627)Termination reason: Time limit
% 10.45/1.71  
% 10.45/1.71  % (6627)Memory used [KB]: 5500
% 10.45/1.71  % (6627)Time elapsed: 1.304 s
% 10.45/1.71  % (6627)------------------------------
% 10.45/1.71  % (6627)------------------------------
% 10.45/1.73  % (6911)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_158 on theBenchmark
% 11.82/1.85  % (6671)Time limit reached!
% 11.82/1.85  % (6671)------------------------------
% 11.82/1.85  % (6671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.82/1.87  % (6671)Termination reason: Time limit
% 11.82/1.87  
% 11.82/1.87  % (6671)Memory used [KB]: 14967
% 11.82/1.87  % (6671)Time elapsed: 0.905 s
% 11.82/1.87  % (6671)------------------------------
% 11.82/1.87  % (6671)------------------------------
% 12.51/1.97  % (6615)Time limit reached!
% 12.51/1.97  % (6615)------------------------------
% 12.51/1.97  % (6615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.86/2.00  % (6615)Termination reason: Time limit
% 12.86/2.00  % (6615)Termination phase: Saturation
% 12.86/2.00  
% 12.86/2.00  % (6615)Memory used [KB]: 20596
% 12.86/2.00  % (6615)Time elapsed: 1.500 s
% 12.86/2.00  % (6615)------------------------------
% 12.86/2.00  % (6615)------------------------------
% 13.51/2.11  % (6625)Time limit reached!
% 13.51/2.11  % (6625)------------------------------
% 13.51/2.11  % (6625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.98/2.12  % (6868)Time limit reached!
% 13.98/2.12  % (6868)------------------------------
% 13.98/2.12  % (6868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.98/2.12  % (6868)Termination reason: Time limit
% 13.98/2.12  % (6868)Termination phase: Saturation
% 13.98/2.12  
% 13.98/2.12  % (6868)Memory used [KB]: 13688
% 13.98/2.12  % (6868)Time elapsed: 0.621 s
% 13.98/2.12  % (6868)------------------------------
% 13.98/2.12  % (6868)------------------------------
% 13.98/2.13  % (6625)Termination reason: Time limit
% 13.98/2.13  
% 13.98/2.13  % (6625)Memory used [KB]: 4349
% 13.98/2.13  % (6625)Time elapsed: 1.718 s
% 13.98/2.13  % (6625)------------------------------
% 13.98/2.13  % (6625)------------------------------
% 14.98/2.27  % (6835)Time limit reached!
% 14.98/2.27  % (6835)------------------------------
% 14.98/2.27  % (6835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.98/2.27  % (6835)Termination reason: Time limit
% 14.98/2.27  
% 14.98/2.27  % (6835)Memory used [KB]: 15735
% 14.98/2.27  % (6835)Time elapsed: 0.916 s
% 14.98/2.27  % (6835)------------------------------
% 14.98/2.27  % (6835)------------------------------
% 15.88/2.37  % (6853)Time limit reached!
% 15.88/2.37  % (6853)------------------------------
% 15.88/2.37  % (6853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.88/2.37  % (6853)Termination reason: Time limit
% 15.88/2.37  % (6853)Termination phase: Saturation
% 15.88/2.37  
% 15.88/2.37  % (6853)Memory used [KB]: 26097
% 15.88/2.37  % (6853)Time elapsed: 0.900 s
% 15.88/2.37  % (6853)------------------------------
% 15.88/2.37  % (6853)------------------------------
% 16.30/2.44  % (6614)Time limit reached!
% 16.30/2.44  % (6614)------------------------------
% 16.30/2.44  % (6614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.30/2.44  % (6614)Termination reason: Time limit
% 16.30/2.44  
% 16.30/2.44  % (6614)Memory used [KB]: 16502
% 16.30/2.44  % (6614)Time elapsed: 2.008 s
% 16.30/2.44  % (6614)------------------------------
% 16.30/2.44  % (6614)------------------------------
% 16.66/2.54  % (6663)Time limit reached!
% 16.66/2.54  % (6663)------------------------------
% 16.66/2.54  % (6663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.39/2.55  % (6663)Termination reason: Time limit
% 17.39/2.55  
% 17.39/2.55  % (6663)Memory used [KB]: 29040
% 17.39/2.55  % (6663)Time elapsed: 1.710 s
% 17.39/2.55  % (6663)------------------------------
% 17.39/2.55  % (6663)------------------------------
% 17.78/2.60  % (6675)Refutation found. Thanks to Tanya!
% 17.78/2.60  % SZS status Theorem for theBenchmark
% 17.78/2.60  % SZS output start Proof for theBenchmark
% 17.78/2.60  fof(f10362,plain,(
% 17.78/2.60    $false),
% 17.78/2.60    inference(avatar_sat_refutation,[],[f227,f231,f235,f239,f243,f247,f251,f255,f259,f263,f271,f279,f283,f287,f291,f295,f315,f327,f331,f335,f339,f351,f379,f387,f391,f395,f415,f419,f427,f437,f449,f457,f473,f477,f485,f514,f519,f570,f574,f620,f623,f699,f703,f717,f747,f755,f764,f791,f841,f861,f876,f890,f908,f915,f928,f933,f964,f976,f1103,f1161,f1281,f1318,f1339,f1359,f1701,f1707,f1791,f1874,f1912,f2003,f2101,f2105,f2121,f2155,f2179,f2291,f2324,f2338,f2919,f2945,f2979,f3085,f3151,f3199,f3415,f3441,f3678,f3696,f3742,f3811,f3826,f3855,f8146,f9173,f9178,f9203,f10336,f10361])).
% 17.78/2.60  fof(f10361,plain,(
% 17.78/2.60    ~spl8_8 | ~spl8_56 | spl8_183 | ~spl8_411),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f10360])).
% 17.78/2.60  fof(f10360,plain,(
% 17.78/2.60    $false | (~spl8_8 | ~spl8_56 | spl8_183 | ~spl8_411)),
% 17.78/2.60    inference(subsumption_resolution,[],[f10359,f254])).
% 17.78/2.60  fof(f254,plain,(
% 17.78/2.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl8_8),
% 17.78/2.60    inference(avatar_component_clause,[],[f253])).
% 17.78/2.60  fof(f253,plain,(
% 17.78/2.60    spl8_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 17.78/2.60  fof(f10359,plain,(
% 17.78/2.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl8_56 | spl8_183 | ~spl8_411)),
% 17.78/2.60    inference(subsumption_resolution,[],[f10341,f1338])).
% 17.78/2.60  fof(f1338,plain,(
% 17.78/2.60    sK0 != k2_relat_1(sK1) | spl8_183),
% 17.78/2.60    inference(avatar_component_clause,[],[f1337])).
% 17.78/2.60  fof(f1337,plain,(
% 17.78/2.60    spl8_183 <=> sK0 = k2_relat_1(sK1)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_183])])).
% 17.78/2.60  fof(f10341,plain,(
% 17.78/2.60    sK0 = k2_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl8_56 | ~spl8_411)),
% 17.78/2.60    inference(superposition,[],[f448,f10335])).
% 17.78/2.60  fof(f10335,plain,(
% 17.78/2.60    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl8_411),
% 17.78/2.60    inference(avatar_component_clause,[],[f10334])).
% 17.78/2.60  fof(f10334,plain,(
% 17.78/2.60    spl8_411 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_411])])).
% 17.78/2.60  fof(f448,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_56),
% 17.78/2.60    inference(avatar_component_clause,[],[f447])).
% 17.78/2.60  fof(f447,plain,(
% 17.78/2.60    spl8_56 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 17.78/2.60  fof(f10336,plain,(
% 17.78/2.60    spl8_411 | spl8_182 | ~spl8_385 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_204 | ~spl8_237),
% 17.78/2.60    inference(avatar_split_clause,[],[f9201,f2289,f1872,f253,f249,f241,f233,f229,f8135,f1334,f10334])).
% 17.78/2.60  fof(f1334,plain,(
% 17.78/2.60    spl8_182 <=> k1_xboole_0 = sK0),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_182])])).
% 17.78/2.60  fof(f8135,plain,(
% 17.78/2.60    spl8_385 <=> sK0 = k2_relset_1(sK0,sK0,k6_relat_1(sK0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_385])])).
% 17.78/2.60  fof(f229,plain,(
% 17.78/2.60    spl8_2 <=> v1_funct_1(sK1)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 17.78/2.60  fof(f233,plain,(
% 17.78/2.60    spl8_3 <=> v1_funct_2(sK2,sK0,sK0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 17.78/2.60  fof(f241,plain,(
% 17.78/2.60    spl8_5 <=> v1_funct_2(sK1,sK0,sK0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 17.78/2.60  fof(f249,plain,(
% 17.78/2.60    spl8_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 17.78/2.60  fof(f1872,plain,(
% 17.78/2.60    spl8_204 <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_204])])).
% 17.78/2.60  fof(f2289,plain,(
% 17.78/2.60    spl8_237 <=> ! [X1,X3,X0,X2] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X0,sK2)) != X3 | ~v1_funct_1(X0) | k1_xboole_0 = X3 | k2_relset_1(X1,X2,X0) = X2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_237])])).
% 17.78/2.60  fof(f9201,plain,(
% 17.78/2.60    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | k1_xboole_0 = sK0 | sK0 = k2_relset_1(sK0,sK0,sK1) | (~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_204 | ~spl8_237)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9200,f230])).
% 17.78/2.60  fof(f230,plain,(
% 17.78/2.60    v1_funct_1(sK1) | ~spl8_2),
% 17.78/2.60    inference(avatar_component_clause,[],[f229])).
% 17.78/2.60  fof(f9200,plain,(
% 17.78/2.60    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 = k2_relset_1(sK0,sK0,sK1) | (~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_204 | ~spl8_237)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9199,f242])).
% 17.78/2.60  fof(f242,plain,(
% 17.78/2.60    v1_funct_2(sK1,sK0,sK0) | ~spl8_5),
% 17.78/2.60    inference(avatar_component_clause,[],[f241])).
% 17.78/2.60  fof(f9199,plain,(
% 17.78/2.60    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 = k2_relset_1(sK0,sK0,sK1) | (~spl8_3 | ~spl8_7 | ~spl8_8 | ~spl8_204 | ~spl8_237)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9198,f250])).
% 17.78/2.60  fof(f250,plain,(
% 17.78/2.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl8_7),
% 17.78/2.60    inference(avatar_component_clause,[],[f249])).
% 17.78/2.60  fof(f9198,plain,(
% 17.78/2.60    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 = k2_relset_1(sK0,sK0,sK1) | (~spl8_3 | ~spl8_8 | ~spl8_204 | ~spl8_237)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9197,f234])).
% 17.78/2.60  fof(f234,plain,(
% 17.78/2.60    v1_funct_2(sK2,sK0,sK0) | ~spl8_3),
% 17.78/2.60    inference(avatar_component_clause,[],[f233])).
% 17.78/2.60  fof(f9197,plain,(
% 17.78/2.60    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 = k2_relset_1(sK0,sK0,sK1) | (~spl8_8 | ~spl8_204 | ~spl8_237)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9195,f254])).
% 17.78/2.60  fof(f9195,plain,(
% 17.78/2.60    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 = k2_relset_1(sK0,sK0,sK1) | (~spl8_204 | ~spl8_237)),
% 17.78/2.60    inference(superposition,[],[f2290,f1873])).
% 17.78/2.60  fof(f1873,plain,(
% 17.78/2.60    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~spl8_204),
% 17.78/2.60    inference(avatar_component_clause,[],[f1872])).
% 17.78/2.60  fof(f2290,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X0,sK2)) != X3 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | k1_xboole_0 = X3 | k2_relset_1(X1,X2,X0) = X2) ) | ~spl8_237),
% 17.78/2.60    inference(avatar_component_clause,[],[f2289])).
% 17.78/2.60  fof(f9203,plain,(
% 17.78/2.60    ~spl8_101 | ~spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_8 | spl8_12 | ~spl8_97),
% 17.78/2.60    inference(avatar_split_clause,[],[f9108,f715,f269,f253,f245,f241,f229,f736])).
% 17.78/2.60  fof(f736,plain,(
% 17.78/2.60    spl8_101 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).
% 17.78/2.60  fof(f245,plain,(
% 17.78/2.60    spl8_6 <=> v3_funct_2(sK1,sK0,sK0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 17.78/2.60  fof(f269,plain,(
% 17.78/2.60    spl8_12 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 17.78/2.60  fof(f715,plain,(
% 17.78/2.60    spl8_97 <=> ! [X1,X0] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).
% 17.78/2.60  fof(f9108,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | (~spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_8 | spl8_12 | ~spl8_97)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9107,f230])).
% 17.78/2.60  fof(f9107,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~v1_funct_1(sK1) | (~spl8_5 | ~spl8_6 | ~spl8_8 | spl8_12 | ~spl8_97)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9106,f254])).
% 17.78/2.60  fof(f9106,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl8_5 | ~spl8_6 | spl8_12 | ~spl8_97)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9105,f246])).
% 17.78/2.60  fof(f246,plain,(
% 17.78/2.60    v3_funct_2(sK1,sK0,sK0) | ~spl8_6),
% 17.78/2.60    inference(avatar_component_clause,[],[f245])).
% 17.78/2.60  fof(f9105,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl8_5 | spl8_12 | ~spl8_97)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9104,f242])).
% 17.78/2.60  fof(f9104,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (spl8_12 | ~spl8_97)),
% 17.78/2.60    inference(superposition,[],[f270,f716])).
% 17.78/2.60  fof(f716,plain,(
% 17.78/2.60    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) ) | ~spl8_97),
% 17.78/2.60    inference(avatar_component_clause,[],[f715])).
% 17.78/2.60  fof(f270,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | spl8_12),
% 17.78/2.60    inference(avatar_component_clause,[],[f269])).
% 17.78/2.60  fof(f9178,plain,(
% 17.78/2.60    ~spl8_7 | ~spl8_49 | spl8_386),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f9177])).
% 17.78/2.60  fof(f9177,plain,(
% 17.78/2.60    $false | (~spl8_7 | ~spl8_49 | spl8_386)),
% 17.78/2.60    inference(subsumption_resolution,[],[f9175,f250])).
% 17.78/2.60  fof(f9175,plain,(
% 17.78/2.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl8_49 | spl8_386)),
% 17.78/2.60    inference(resolution,[],[f9172,f418])).
% 17.78/2.60  fof(f418,plain,(
% 17.78/2.60    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_49),
% 17.78/2.60    inference(avatar_component_clause,[],[f417])).
% 17.78/2.60  fof(f417,plain,(
% 17.78/2.60    spl8_49 <=> ! [X1,X3,X0] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 17.78/2.60  fof(f9172,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,sK2) | spl8_386),
% 17.78/2.60    inference(avatar_component_clause,[],[f9171])).
% 17.78/2.60  fof(f9171,plain,(
% 17.78/2.60    spl8_386 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_386])])).
% 17.78/2.60  fof(f9173,plain,(
% 17.78/2.60    ~spl8_386 | spl8_101 | ~spl8_181),
% 17.78/2.60    inference(avatar_split_clause,[],[f8719,f1331,f736,f9171])).
% 17.78/2.60  fof(f1331,plain,(
% 17.78/2.60    spl8_181 <=> sK2 = k2_funct_1(sK1)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_181])])).
% 17.78/2.60  fof(f8719,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,sK2) | (spl8_101 | ~spl8_181)),
% 17.78/2.60    inference(forward_demodulation,[],[f737,f1332])).
% 17.78/2.60  fof(f1332,plain,(
% 17.78/2.60    sK2 = k2_funct_1(sK1) | ~spl8_181),
% 17.78/2.60    inference(avatar_component_clause,[],[f1331])).
% 17.78/2.60  fof(f737,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | spl8_101),
% 17.78/2.60    inference(avatar_component_clause,[],[f736])).
% 17.78/2.60  fof(f8146,plain,(
% 17.78/2.60    ~spl8_27 | ~spl8_56 | ~spl8_127 | spl8_385),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f8145])).
% 17.78/2.60  fof(f8145,plain,(
% 17.78/2.60    $false | (~spl8_27 | ~spl8_56 | ~spl8_127 | spl8_385)),
% 17.78/2.60    inference(subsumption_resolution,[],[f8144,f330])).
% 17.78/2.60  fof(f330,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl8_27),
% 17.78/2.60    inference(avatar_component_clause,[],[f329])).
% 17.78/2.60  fof(f329,plain,(
% 17.78/2.60    spl8_27 <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 17.78/2.60  fof(f8144,plain,(
% 17.78/2.60    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl8_56 | ~spl8_127 | spl8_385)),
% 17.78/2.60    inference(subsumption_resolution,[],[f8143,f963])).
% 17.78/2.60  fof(f963,plain,(
% 17.78/2.60    sK0 = k2_relat_1(k6_relat_1(sK0)) | ~spl8_127),
% 17.78/2.60    inference(avatar_component_clause,[],[f962])).
% 17.78/2.60  fof(f962,plain,(
% 17.78/2.60    spl8_127 <=> sK0 = k2_relat_1(k6_relat_1(sK0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).
% 17.78/2.60  fof(f8143,plain,(
% 17.78/2.60    sK0 != k2_relat_1(k6_relat_1(sK0)) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl8_56 | spl8_385)),
% 17.78/2.60    inference(superposition,[],[f8136,f448])).
% 17.78/2.60  fof(f8136,plain,(
% 17.78/2.60    sK0 != k2_relset_1(sK0,sK0,k6_relat_1(sK0)) | spl8_385),
% 17.78/2.60    inference(avatar_component_clause,[],[f8135])).
% 17.78/2.60  fof(f3855,plain,(
% 17.78/2.60    ~spl8_53 | ~spl8_287 | ~spl8_304 | spl8_331 | ~spl8_336),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f3854])).
% 17.78/2.60  fof(f3854,plain,(
% 17.78/2.60    $false | (~spl8_53 | ~spl8_287 | ~spl8_304 | spl8_331 | ~spl8_336)),
% 17.78/2.60    inference(subsumption_resolution,[],[f3849,f2918])).
% 17.78/2.60  fof(f2918,plain,(
% 17.78/2.60    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl8_287),
% 17.78/2.60    inference(avatar_component_clause,[],[f2917])).
% 17.78/2.60  fof(f2917,plain,(
% 17.78/2.60    spl8_287 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_287])])).
% 17.78/2.60  fof(f3849,plain,(
% 17.78/2.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_53 | ~spl8_304 | spl8_331 | ~spl8_336)),
% 17.78/2.60    inference(backward_demodulation,[],[f3791,f3848])).
% 17.78/2.60  fof(f3848,plain,(
% 17.78/2.60    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl8_53 | ~spl8_304 | ~spl8_336)),
% 17.78/2.60    inference(forward_demodulation,[],[f3198,f3747])).
% 17.78/2.60  fof(f3747,plain,(
% 17.78/2.60    k1_xboole_0 = sK2 | (~spl8_53 | ~spl8_336)),
% 17.78/2.60    inference(resolution,[],[f3741,f436])).
% 17.78/2.60  fof(f436,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl8_53),
% 17.78/2.60    inference(avatar_component_clause,[],[f435])).
% 17.78/2.60  fof(f435,plain,(
% 17.78/2.60    spl8_53 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 17.78/2.60  fof(f3741,plain,(
% 17.78/2.60    ( ! [X24] : (~m1_subset_1(X24,k1_zfmisc_1(sK2)) | k1_xboole_0 = X24) ) | ~spl8_336),
% 17.78/2.60    inference(avatar_component_clause,[],[f3740])).
% 17.78/2.60  fof(f3740,plain,(
% 17.78/2.60    spl8_336 <=> ! [X24] : (~m1_subset_1(X24,k1_zfmisc_1(sK2)) | k1_xboole_0 = X24)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_336])])).
% 17.78/2.60  fof(f3198,plain,(
% 17.78/2.60    sK2 = k2_funct_1(sK2) | ~spl8_304),
% 17.78/2.60    inference(avatar_component_clause,[],[f3197])).
% 17.78/2.60  fof(f3197,plain,(
% 17.78/2.60    spl8_304 <=> sK2 = k2_funct_1(sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_304])])).
% 17.78/2.60  fof(f3791,plain,(
% 17.78/2.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) | (~spl8_53 | spl8_331 | ~spl8_336)),
% 17.78/2.60    inference(backward_demodulation,[],[f3677,f3747])).
% 17.78/2.60  fof(f3677,plain,(
% 17.78/2.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) | spl8_331),
% 17.78/2.60    inference(avatar_component_clause,[],[f3676])).
% 17.78/2.60  fof(f3676,plain,(
% 17.78/2.60    spl8_331 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_331])])).
% 17.78/2.60  fof(f3826,plain,(
% 17.78/2.60    ~spl8_53 | ~spl8_300 | spl8_303 | ~spl8_336),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f3825])).
% 17.78/2.60  fof(f3825,plain,(
% 17.78/2.60    $false | (~spl8_53 | ~spl8_300 | spl8_303 | ~spl8_336)),
% 17.78/2.60    inference(subsumption_resolution,[],[f3793,f3784])).
% 17.78/2.60  fof(f3784,plain,(
% 17.78/2.60    k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) | (~spl8_53 | spl8_303 | ~spl8_336)),
% 17.78/2.60    inference(backward_demodulation,[],[f3195,f3747])).
% 17.78/2.60  fof(f3195,plain,(
% 17.78/2.60    k1_xboole_0 != k5_relat_1(sK2,sK2) | spl8_303),
% 17.78/2.60    inference(avatar_component_clause,[],[f3194])).
% 17.78/2.60  fof(f3194,plain,(
% 17.78/2.60    spl8_303 <=> k1_xboole_0 = k5_relat_1(sK2,sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_303])])).
% 17.78/2.60  fof(f3793,plain,(
% 17.78/2.60    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) | (~spl8_53 | ~spl8_300 | ~spl8_336)),
% 17.78/2.60    inference(backward_demodulation,[],[f3695,f3747])).
% 17.78/2.60  fof(f3695,plain,(
% 17.78/2.60    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2) | ~spl8_300),
% 17.78/2.60    inference(avatar_component_clause,[],[f3184])).
% 17.78/2.60  fof(f3184,plain,(
% 17.78/2.60    spl8_300 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_300])])).
% 17.78/2.60  fof(f3811,plain,(
% 17.78/2.60    ~spl8_53 | ~spl8_200 | spl8_302 | ~spl8_336),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f3810])).
% 17.78/2.60  fof(f3810,plain,(
% 17.78/2.60    $false | (~spl8_53 | ~spl8_200 | spl8_302 | ~spl8_336)),
% 17.78/2.60    inference(subsumption_resolution,[],[f3783,f1700])).
% 17.78/2.60  fof(f1700,plain,(
% 17.78/2.60    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_200),
% 17.78/2.60    inference(avatar_component_clause,[],[f1699])).
% 17.78/2.60  fof(f1699,plain,(
% 17.78/2.60    spl8_200 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_200])])).
% 17.78/2.60  fof(f3783,plain,(
% 17.78/2.60    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl8_53 | spl8_302 | ~spl8_336)),
% 17.78/2.60    inference(backward_demodulation,[],[f3191,f3747])).
% 17.78/2.60  fof(f3191,plain,(
% 17.78/2.60    k1_xboole_0 != k1_relat_1(sK2) | spl8_302),
% 17.78/2.60    inference(avatar_component_clause,[],[f3190])).
% 17.78/2.60  fof(f3190,plain,(
% 17.78/2.60    spl8_302 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_302])])).
% 17.78/2.60  fof(f3742,plain,(
% 17.78/2.60    spl8_336 | ~spl8_205 | ~spl8_324),
% 17.78/2.60    inference(avatar_split_clause,[],[f3423,f3413,f1910,f3740])).
% 17.78/2.60  fof(f1910,plain,(
% 17.78/2.60    spl8_205 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_205])])).
% 17.78/2.60  fof(f3413,plain,(
% 17.78/2.60    spl8_324 <=> ! [X38,X37,X39] : (~m1_subset_1(X37,k1_zfmisc_1(X38)) | ~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X39,k1_xboole_0))) | k1_xboole_0 = X37)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_324])])).
% 17.78/2.60  fof(f3423,plain,(
% 17.78/2.60    ( ! [X24] : (~m1_subset_1(X24,k1_zfmisc_1(sK2)) | k1_xboole_0 = X24) ) | (~spl8_205 | ~spl8_324)),
% 17.78/2.60    inference(resolution,[],[f3414,f1911])).
% 17.78/2.60  fof(f1911,plain,(
% 17.78/2.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl8_205),
% 17.78/2.60    inference(avatar_component_clause,[],[f1910])).
% 17.78/2.60  fof(f3414,plain,(
% 17.78/2.60    ( ! [X39,X37,X38] : (~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X39,k1_xboole_0))) | ~m1_subset_1(X37,k1_zfmisc_1(X38)) | k1_xboole_0 = X37) ) | ~spl8_324),
% 17.78/2.60    inference(avatar_component_clause,[],[f3413])).
% 17.78/2.60  fof(f3696,plain,(
% 17.78/2.60    spl8_300 | ~spl8_53 | ~spl8_290 | ~spl8_325),
% 17.78/2.60    inference(avatar_split_clause,[],[f3495,f3439,f2943,f435,f3184])).
% 17.78/2.60  fof(f2943,plain,(
% 17.78/2.60    spl8_290 <=> k1_xboole_0 = k5_relat_1(sK1,sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_290])])).
% 17.78/2.60  fof(f3439,plain,(
% 17.78/2.60    spl8_325 <=> ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(sK1)) | k1_xboole_0 = X23)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_325])])).
% 17.78/2.60  fof(f3495,plain,(
% 17.78/2.60    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK2) | (~spl8_53 | ~spl8_290 | ~spl8_325)),
% 17.78/2.60    inference(backward_demodulation,[],[f2944,f3446])).
% 17.78/2.60  fof(f3446,plain,(
% 17.78/2.60    k1_xboole_0 = sK1 | (~spl8_53 | ~spl8_325)),
% 17.78/2.60    inference(resolution,[],[f3440,f436])).
% 17.78/2.60  fof(f3440,plain,(
% 17.78/2.60    ( ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(sK1)) | k1_xboole_0 = X23) ) | ~spl8_325),
% 17.78/2.60    inference(avatar_component_clause,[],[f3439])).
% 17.78/2.60  fof(f2944,plain,(
% 17.78/2.60    k1_xboole_0 = k5_relat_1(sK1,sK2) | ~spl8_290),
% 17.78/2.60    inference(avatar_component_clause,[],[f2943])).
% 17.78/2.60  fof(f3678,plain,(
% 17.78/2.60    ~spl8_331 | ~spl8_53 | spl8_215 | ~spl8_325),
% 17.78/2.60    inference(avatar_split_clause,[],[f3474,f3439,f2119,f435,f3676])).
% 17.78/2.60  fof(f2119,plain,(
% 17.78/2.60    spl8_215 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_215])])).
% 17.78/2.60  fof(f3474,plain,(
% 17.78/2.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) | (~spl8_53 | spl8_215 | ~spl8_325)),
% 17.78/2.60    inference(backward_demodulation,[],[f2120,f3446])).
% 17.78/2.60  fof(f2120,plain,(
% 17.78/2.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) | spl8_215),
% 17.78/2.60    inference(avatar_component_clause,[],[f2119])).
% 17.78/2.60  fof(f3441,plain,(
% 17.78/2.60    spl8_325 | ~spl8_208 | ~spl8_324),
% 17.78/2.60    inference(avatar_split_clause,[],[f3422,f3413,f2001,f3439])).
% 17.78/2.60  fof(f2001,plain,(
% 17.78/2.60    spl8_208 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_208])])).
% 17.78/2.60  fof(f3422,plain,(
% 17.78/2.60    ( ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(sK1)) | k1_xboole_0 = X23) ) | (~spl8_208 | ~spl8_324)),
% 17.78/2.60    inference(resolution,[],[f3414,f2002])).
% 17.78/2.60  fof(f2002,plain,(
% 17.78/2.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl8_208),
% 17.78/2.60    inference(avatar_component_clause,[],[f2001])).
% 17.78/2.60  fof(f3415,plain,(
% 17.78/2.60    spl8_324 | ~spl8_63 | ~spl8_241),
% 17.78/2.60    inference(avatar_split_clause,[],[f2334,f2322,f512,f3413])).
% 17.78/2.60  fof(f512,plain,(
% 17.78/2.60    spl8_63 <=> v1_xboole_0(k1_xboole_0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).
% 17.78/2.60  fof(f2322,plain,(
% 17.78/2.60    spl8_241 <=> ! [X16,X15,X17,X14] : (k1_xboole_0 = X14 | ~m1_subset_1(X14,k1_zfmisc_1(X15)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | ~v1_xboole_0(X17))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_241])])).
% 17.78/2.60  fof(f2334,plain,(
% 17.78/2.60    ( ! [X39,X37,X38] : (~m1_subset_1(X37,k1_zfmisc_1(X38)) | ~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X39,k1_xboole_0))) | k1_xboole_0 = X37) ) | (~spl8_63 | ~spl8_241)),
% 17.78/2.60    inference(resolution,[],[f2323,f513])).
% 17.78/2.60  fof(f513,plain,(
% 17.78/2.60    v1_xboole_0(k1_xboole_0) | ~spl8_63),
% 17.78/2.60    inference(avatar_component_clause,[],[f512])).
% 17.78/2.60  fof(f2323,plain,(
% 17.78/2.60    ( ! [X14,X17,X15,X16] : (~v1_xboole_0(X17) | ~m1_subset_1(X14,k1_zfmisc_1(X15)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | k1_xboole_0 = X14) ) | ~spl8_241),
% 17.78/2.60    inference(avatar_component_clause,[],[f2322])).
% 17.78/2.60  fof(f3199,plain,(
% 17.78/2.60    ~spl8_81 | ~spl8_303 | spl8_304 | ~spl8_302 | ~spl8_1 | ~spl8_211 | ~spl8_297),
% 17.78/2.60    inference(avatar_split_clause,[],[f3155,f3149,f2099,f225,f3190,f3197,f3194,f618])).
% 17.78/2.60  fof(f618,plain,(
% 17.78/2.60    spl8_81 <=> v1_relat_1(sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).
% 17.78/2.60  fof(f225,plain,(
% 17.78/2.60    spl8_1 <=> v1_funct_1(sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 17.78/2.60  fof(f2099,plain,(
% 17.78/2.60    spl8_211 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_211])])).
% 17.78/2.60  fof(f3149,plain,(
% 17.78/2.60    spl8_297 <=> ! [X0] : (k1_xboole_0 != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0 | k2_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_297])])).
% 17.78/2.60  fof(f3155,plain,(
% 17.78/2.60    k1_xboole_0 != k1_relat_1(sK2) | sK2 = k2_funct_1(sK2) | k1_xboole_0 != k5_relat_1(sK2,sK2) | ~v1_relat_1(sK2) | (~spl8_1 | ~spl8_211 | ~spl8_297)),
% 17.78/2.60    inference(subsumption_resolution,[],[f3153,f226])).
% 17.78/2.60  fof(f226,plain,(
% 17.78/2.60    v1_funct_1(sK2) | ~spl8_1),
% 17.78/2.60    inference(avatar_component_clause,[],[f225])).
% 17.78/2.60  fof(f3153,plain,(
% 17.78/2.60    k1_xboole_0 != k1_relat_1(sK2) | sK2 = k2_funct_1(sK2) | k1_xboole_0 != k5_relat_1(sK2,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_211 | ~spl8_297)),
% 17.78/2.60    inference(superposition,[],[f3150,f2100])).
% 17.78/2.60  fof(f2100,plain,(
% 17.78/2.60    k1_xboole_0 = k2_relat_1(sK2) | ~spl8_211),
% 17.78/2.60    inference(avatar_component_clause,[],[f2099])).
% 17.78/2.60  fof(f3150,plain,(
% 17.78/2.60    ( ! [X0] : (k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | k1_xboole_0 != k5_relat_1(X0,sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_297),
% 17.78/2.60    inference(avatar_component_clause,[],[f3149])).
% 17.78/2.60  fof(f3151,plain,(
% 17.78/2.60    spl8_297 | ~spl8_224 | ~spl8_262),
% 17.78/2.60    inference(avatar_split_clause,[],[f3005,f2539,f2177,f3149])).
% 17.78/2.60  fof(f2177,plain,(
% 17.78/2.60    spl8_224 <=> ! [X0] : (k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0 | k2_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_224])])).
% 17.78/2.60  fof(f2539,plain,(
% 17.78/2.60    spl8_262 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_262])])).
% 17.78/2.60  fof(f3005,plain,(
% 17.78/2.60    ( ! [X0] : (k1_xboole_0 != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0 | k2_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl8_224 | ~spl8_262)),
% 17.78/2.60    inference(backward_demodulation,[],[f2178,f2540])).
% 17.78/2.60  fof(f2540,plain,(
% 17.78/2.60    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl8_262),
% 17.78/2.60    inference(avatar_component_clause,[],[f2539])).
% 17.78/2.60  fof(f2178,plain,(
% 17.78/2.60    ( ! [X0] : (k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0 | k2_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_224),
% 17.78/2.60    inference(avatar_component_clause,[],[f2177])).
% 17.78/2.60  fof(f3085,plain,(
% 17.78/2.60    ~spl8_28 | ~spl8_53 | ~spl8_63 | ~spl8_242 | spl8_286),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f3081])).
% 17.78/2.60  fof(f3081,plain,(
% 17.78/2.60    $false | (~spl8_28 | ~spl8_53 | ~spl8_63 | ~spl8_242 | spl8_286)),
% 17.78/2.60    inference(unit_resulting_resolution,[],[f513,f334,f436,f3072,f2337])).
% 17.78/2.60  fof(f2337,plain,(
% 17.78/2.60    ( ! [X21,X19,X20,X18] : (~v1_xboole_0(X20) | ~m1_subset_1(X18,k1_zfmisc_1(X19)) | ~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) | k1_xboole_0 = X18) ) | ~spl8_242),
% 17.78/2.60    inference(avatar_component_clause,[],[f2336])).
% 17.78/2.60  fof(f2336,plain,(
% 17.78/2.60    spl8_242 <=> ! [X18,X20,X19,X21] : (k1_xboole_0 = X18 | ~m1_subset_1(X18,k1_zfmisc_1(X19)) | ~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) | ~v1_xboole_0(X20))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_242])])).
% 17.78/2.60  fof(f3072,plain,(
% 17.78/2.60    k1_xboole_0 != k6_partfun1(k1_xboole_0) | spl8_286),
% 17.78/2.60    inference(avatar_component_clause,[],[f2892])).
% 17.78/2.60  fof(f2892,plain,(
% 17.78/2.60    spl8_286 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_286])])).
% 17.78/2.60  fof(f334,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl8_28),
% 17.78/2.60    inference(avatar_component_clause,[],[f333])).
% 17.78/2.60  fof(f333,plain,(
% 17.78/2.60    spl8_28 <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 17.78/2.60  fof(f2979,plain,(
% 17.78/2.60    ~spl8_27 | ~spl8_53 | ~spl8_63 | ~spl8_242 | spl8_262),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f2975])).
% 17.78/2.60  fof(f2975,plain,(
% 17.78/2.60    $false | (~spl8_27 | ~spl8_53 | ~spl8_63 | ~spl8_242 | spl8_262)),
% 17.78/2.60    inference(unit_resulting_resolution,[],[f513,f330,f436,f2940,f2337])).
% 17.78/2.60  fof(f2940,plain,(
% 17.78/2.60    k1_xboole_0 != k6_relat_1(k1_xboole_0) | spl8_262),
% 17.78/2.60    inference(avatar_component_clause,[],[f2539])).
% 17.78/2.60  fof(f2945,plain,(
% 17.78/2.60    spl8_290 | ~spl8_221 | ~spl8_286),
% 17.78/2.60    inference(avatar_split_clause,[],[f2900,f2892,f2153,f2943])).
% 17.78/2.60  fof(f2153,plain,(
% 17.78/2.60    spl8_221 <=> k6_partfun1(k1_xboole_0) = k5_relat_1(sK1,sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_221])])).
% 17.78/2.60  fof(f2900,plain,(
% 17.78/2.60    k1_xboole_0 = k5_relat_1(sK1,sK2) | (~spl8_221 | ~spl8_286)),
% 17.78/2.60    inference(backward_demodulation,[],[f2154,f2893])).
% 17.78/2.60  fof(f2893,plain,(
% 17.78/2.60    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl8_286),
% 17.78/2.60    inference(avatar_component_clause,[],[f2892])).
% 17.78/2.60  fof(f2154,plain,(
% 17.78/2.60    k6_partfun1(k1_xboole_0) = k5_relat_1(sK1,sK2) | ~spl8_221),
% 17.78/2.60    inference(avatar_component_clause,[],[f2153])).
% 17.78/2.60  fof(f2919,plain,(
% 17.78/2.60    spl8_287 | ~spl8_212 | ~spl8_286),
% 17.78/2.60    inference(avatar_split_clause,[],[f2897,f2892,f2103,f2917])).
% 17.78/2.60  fof(f2103,plain,(
% 17.78/2.60    spl8_212 <=> r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_212])])).
% 17.78/2.60  fof(f2897,plain,(
% 17.78/2.60    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_212 | ~spl8_286)),
% 17.78/2.60    inference(backward_demodulation,[],[f2104,f2893])).
% 17.78/2.60  fof(f2104,plain,(
% 17.78/2.60    r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) | ~spl8_212),
% 17.78/2.60    inference(avatar_component_clause,[],[f2103])).
% 17.78/2.60  fof(f2338,plain,(
% 17.78/2.60    spl8_242 | ~spl8_43 | ~spl8_57),
% 17.78/2.60    inference(avatar_split_clause,[],[f468,f455,f393,f2336])).
% 17.78/2.60  fof(f393,plain,(
% 17.78/2.60    spl8_43 <=> ! [X1,X0,X2] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 17.78/2.60  fof(f455,plain,(
% 17.78/2.60    spl8_57 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0 | ~v1_xboole_0(X1))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 17.78/2.60  fof(f468,plain,(
% 17.78/2.60    ( ! [X21,X19,X20,X18] : (k1_xboole_0 = X18 | ~m1_subset_1(X18,k1_zfmisc_1(X19)) | ~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) | ~v1_xboole_0(X20)) ) | (~spl8_43 | ~spl8_57)),
% 17.78/2.60    inference(resolution,[],[f456,f394])).
% 17.78/2.60  fof(f394,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) ) | ~spl8_43),
% 17.78/2.60    inference(avatar_component_clause,[],[f393])).
% 17.78/2.60  fof(f456,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl8_57),
% 17.78/2.60    inference(avatar_component_clause,[],[f455])).
% 17.78/2.60  fof(f2324,plain,(
% 17.78/2.60    spl8_241 | ~spl8_42 | ~spl8_57),
% 17.78/2.60    inference(avatar_split_clause,[],[f467,f455,f389,f2322])).
% 17.78/2.60  fof(f389,plain,(
% 17.78/2.60    spl8_42 <=> ! [X1,X0,X2] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 17.78/2.60  fof(f467,plain,(
% 17.78/2.60    ( ! [X14,X17,X15,X16] : (k1_xboole_0 = X14 | ~m1_subset_1(X14,k1_zfmisc_1(X15)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | ~v1_xboole_0(X17)) ) | (~spl8_42 | ~spl8_57)),
% 17.78/2.60    inference(resolution,[],[f456,f390])).
% 17.78/2.60  fof(f390,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) ) | ~spl8_42),
% 17.78/2.60    inference(avatar_component_clause,[],[f389])).
% 17.78/2.60  fof(f2291,plain,(
% 17.78/2.60    spl8_237 | ~spl8_1 | ~spl8_74 | ~spl8_118),
% 17.78/2.60    inference(avatar_split_clause,[],[f871,f859,f572,f225,f2289])).
% 17.78/2.60  fof(f572,plain,(
% 17.78/2.60    spl8_74 <=> v2_funct_1(sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).
% 17.78/2.60  fof(f859,plain,(
% 17.78/2.60    spl8_118 <=> ! [X1,X3,X0,X2,X4] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | ~v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) = X1)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).
% 17.78/2.60  fof(f871,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X0,sK2)) != X3 | ~v1_funct_1(X0) | k1_xboole_0 = X3 | k2_relset_1(X1,X2,X0) = X2) ) | (~spl8_1 | ~spl8_74 | ~spl8_118)),
% 17.78/2.60    inference(subsumption_resolution,[],[f869,f226])).
% 17.78/2.60  fof(f869,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X0,sK2)) != X3 | ~v1_funct_1(X0) | k1_xboole_0 = X3 | k2_relset_1(X1,X2,X0) = X2) ) | (~spl8_74 | ~spl8_118)),
% 17.78/2.60    inference(resolution,[],[f860,f573])).
% 17.78/2.60  fof(f573,plain,(
% 17.78/2.60    v2_funct_1(sK2) | ~spl8_74),
% 17.78/2.60    inference(avatar_component_clause,[],[f572])).
% 17.78/2.60  fof(f860,plain,(
% 17.78/2.60    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(X4) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | ~v1_funct_1(X3) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) = X1) ) | ~spl8_118),
% 17.78/2.60    inference(avatar_component_clause,[],[f859])).
% 17.78/2.60  fof(f2179,plain,(
% 17.78/2.60    spl8_224 | ~spl8_174 | ~spl8_182),
% 17.78/2.60    inference(avatar_split_clause,[],[f2079,f1334,f1279,f2177])).
% 17.78/2.60  fof(f1279,plain,(
% 17.78/2.60    spl8_174 <=> ! [X0] : (k6_relat_1(sK0) != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0 | k2_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_174])])).
% 17.78/2.60  fof(f2079,plain,(
% 17.78/2.60    ( ! [X0] : (k6_relat_1(k1_xboole_0) != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0 | k2_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl8_174 | ~spl8_182)),
% 17.78/2.60    inference(backward_demodulation,[],[f1280,f1335])).
% 17.78/2.60  fof(f1335,plain,(
% 17.78/2.60    k1_xboole_0 = sK0 | ~spl8_182),
% 17.78/2.60    inference(avatar_component_clause,[],[f1334])).
% 17.78/2.60  fof(f1280,plain,(
% 17.78/2.60    ( ! [X0] : (k6_relat_1(sK0) != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0 | k2_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_174),
% 17.78/2.60    inference(avatar_component_clause,[],[f1279])).
% 17.78/2.60  fof(f2155,plain,(
% 17.78/2.60    spl8_221 | ~spl8_111 | ~spl8_182),
% 17.78/2.60    inference(avatar_split_clause,[],[f2068,f1334,f796,f2153])).
% 17.78/2.60  fof(f796,plain,(
% 17.78/2.60    spl8_111 <=> k6_partfun1(sK0) = k5_relat_1(sK1,sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).
% 17.78/2.60  fof(f2068,plain,(
% 17.78/2.60    k6_partfun1(k1_xboole_0) = k5_relat_1(sK1,sK2) | (~spl8_111 | ~spl8_182)),
% 17.78/2.60    inference(backward_demodulation,[],[f797,f1335])).
% 17.78/2.60  fof(f797,plain,(
% 17.78/2.60    k6_partfun1(sK0) = k5_relat_1(sK1,sK2) | ~spl8_111),
% 17.78/2.60    inference(avatar_component_clause,[],[f796])).
% 17.78/2.60  fof(f2121,plain,(
% 17.78/2.60    ~spl8_215 | spl8_101 | ~spl8_182),
% 17.78/2.60    inference(avatar_split_clause,[],[f2067,f1334,f736,f2119])).
% 17.78/2.60  fof(f2067,plain,(
% 17.78/2.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) | (spl8_101 | ~spl8_182)),
% 17.78/2.60    inference(backward_demodulation,[],[f737,f1335])).
% 17.78/2.60  fof(f2105,plain,(
% 17.78/2.60    spl8_212 | ~spl8_126 | ~spl8_182),
% 17.78/2.60    inference(avatar_split_clause,[],[f2072,f1334,f931,f2103])).
% 17.78/2.60  fof(f931,plain,(
% 17.78/2.60    spl8_126 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).
% 17.78/2.60  fof(f2072,plain,(
% 17.78/2.60    r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) | (~spl8_126 | ~spl8_182)),
% 17.78/2.60    inference(backward_demodulation,[],[f932,f1335])).
% 17.78/2.60  fof(f932,plain,(
% 17.78/2.60    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl8_126),
% 17.78/2.60    inference(avatar_component_clause,[],[f931])).
% 17.78/2.60  fof(f2101,plain,(
% 17.78/2.60    spl8_211 | ~spl8_123 | ~spl8_182),
% 17.78/2.60    inference(avatar_split_clause,[],[f2070,f1334,f906,f2099])).
% 17.78/2.60  fof(f906,plain,(
% 17.78/2.60    spl8_123 <=> sK0 = k2_relat_1(sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).
% 17.78/2.60  fof(f2070,plain,(
% 17.78/2.60    k1_xboole_0 = k2_relat_1(sK2) | (~spl8_123 | ~spl8_182)),
% 17.78/2.60    inference(backward_demodulation,[],[f907,f1335])).
% 17.78/2.60  fof(f907,plain,(
% 17.78/2.60    sK0 = k2_relat_1(sK2) | ~spl8_123),
% 17.78/2.60    inference(avatar_component_clause,[],[f906])).
% 17.78/2.60  fof(f2003,plain,(
% 17.78/2.60    spl8_208 | ~spl8_8 | ~spl8_182),
% 17.78/2.60    inference(avatar_split_clause,[],[f1968,f1334,f253,f2001])).
% 17.78/2.60  fof(f1968,plain,(
% 17.78/2.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_8 | ~spl8_182)),
% 17.78/2.60    inference(backward_demodulation,[],[f254,f1335])).
% 17.78/2.60  fof(f1912,plain,(
% 17.78/2.60    spl8_205 | ~spl8_7 | ~spl8_182),
% 17.78/2.60    inference(avatar_split_clause,[],[f1879,f1334,f249,f1910])).
% 17.78/2.60  fof(f1879,plain,(
% 17.78/2.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_7 | ~spl8_182)),
% 17.78/2.60    inference(backward_demodulation,[],[f250,f1335])).
% 17.78/2.60  fof(f1874,plain,(
% 17.78/2.60    spl8_204 | ~spl8_125 | ~spl8_179),
% 17.78/2.60    inference(avatar_split_clause,[],[f1846,f1305,f913,f1872])).
% 17.78/2.60  fof(f913,plain,(
% 17.78/2.60    spl8_125 <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_partfun1(sK0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_125])])).
% 17.78/2.60  fof(f1305,plain,(
% 17.78/2.60    spl8_179 <=> k6_partfun1(sK0) = k6_relat_1(sK0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_179])])).
% 17.78/2.60  fof(f1846,plain,(
% 17.78/2.60    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | (~spl8_125 | ~spl8_179)),
% 17.78/2.60    inference(backward_demodulation,[],[f914,f1790])).
% 17.78/2.60  fof(f1790,plain,(
% 17.78/2.60    k6_partfun1(sK0) = k6_relat_1(sK0) | ~spl8_179),
% 17.78/2.60    inference(avatar_component_clause,[],[f1305])).
% 17.78/2.60  fof(f914,plain,(
% 17.78/2.60    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_partfun1(sK0) | ~spl8_125),
% 17.78/2.60    inference(avatar_component_clause,[],[f913])).
% 17.78/2.60  fof(f1791,plain,(
% 17.78/2.60    spl8_182 | spl8_179 | ~spl8_3 | ~spl8_7 | ~spl8_122 | ~spl8_201),
% 17.78/2.60    inference(avatar_split_clause,[],[f1714,f1705,f888,f249,f233,f1305,f1334])).
% 17.78/2.60  fof(f888,plain,(
% 17.78/2.60    spl8_122 <=> sK0 = k2_relset_1(sK0,sK0,sK2)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).
% 17.78/2.60  fof(f1705,plain,(
% 17.78/2.60    spl8_201 <=> ! [X1,X0] : (k6_partfun1(X1) = k6_relat_1(sK0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | k1_xboole_0 = X1)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_201])])).
% 17.78/2.60  fof(f1714,plain,(
% 17.78/2.60    k6_partfun1(sK0) = k6_relat_1(sK0) | k1_xboole_0 = sK0 | (~spl8_3 | ~spl8_7 | ~spl8_122 | ~spl8_201)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1713,f250])).
% 17.78/2.60  fof(f1713,plain,(
% 17.78/2.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k6_relat_1(sK0) | k1_xboole_0 = sK0 | (~spl8_3 | ~spl8_122 | ~spl8_201)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1710,f234])).
% 17.78/2.60  fof(f1710,plain,(
% 17.78/2.60    ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k6_relat_1(sK0) | k1_xboole_0 = sK0 | (~spl8_122 | ~spl8_201)),
% 17.78/2.60    inference(trivial_inequality_removal,[],[f1709])).
% 17.78/2.60  fof(f1709,plain,(
% 17.78/2.60    sK0 != sK0 | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k6_relat_1(sK0) | k1_xboole_0 = sK0 | (~spl8_122 | ~spl8_201)),
% 17.78/2.60    inference(superposition,[],[f1706,f889])).
% 17.78/2.60  fof(f889,plain,(
% 17.78/2.60    sK0 = k2_relset_1(sK0,sK0,sK2) | ~spl8_122),
% 17.78/2.60    inference(avatar_component_clause,[],[f888])).
% 17.78/2.60  fof(f1706,plain,(
% 17.78/2.60    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_partfun1(X1) = k6_relat_1(sK0) | k1_xboole_0 = X1) ) | ~spl8_201),
% 17.78/2.60    inference(avatar_component_clause,[],[f1705])).
% 17.78/2.60  fof(f1707,plain,(
% 17.78/2.60    spl8_201 | ~spl8_1 | ~spl8_7 | ~spl8_56 | ~spl8_74 | ~spl8_80 | ~spl8_109 | ~spl8_122),
% 17.78/2.60    inference(avatar_split_clause,[],[f897,f888,f789,f615,f572,f447,f249,f225,f1705])).
% 17.78/2.60  fof(f615,plain,(
% 17.78/2.60    spl8_80 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).
% 17.78/2.60  fof(f789,plain,(
% 17.78/2.60    spl8_109 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).
% 17.78/2.60  fof(f897,plain,(
% 17.78/2.60    ( ! [X0,X1] : (k6_partfun1(X1) = k6_relat_1(sK0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | k1_xboole_0 = X1) ) | (~spl8_1 | ~spl8_7 | ~spl8_56 | ~spl8_74 | ~spl8_80 | ~spl8_109 | ~spl8_122)),
% 17.78/2.60    inference(backward_demodulation,[],[f808,f896])).
% 17.78/2.60  fof(f896,plain,(
% 17.78/2.60    sK0 = k2_relat_1(sK2) | (~spl8_7 | ~spl8_56 | ~spl8_122)),
% 17.78/2.60    inference(subsumption_resolution,[],[f891,f250])).
% 17.78/2.60  fof(f891,plain,(
% 17.78/2.60    sK0 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl8_56 | ~spl8_122)),
% 17.78/2.60    inference(superposition,[],[f889,f448])).
% 17.78/2.60  fof(f808,plain,(
% 17.78/2.60    ( ! [X0,X1] : (k6_partfun1(X1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | k1_xboole_0 = X1) ) | (~spl8_1 | ~spl8_74 | ~spl8_80 | ~spl8_109)),
% 17.78/2.60    inference(forward_demodulation,[],[f807,f616])).
% 17.78/2.60  fof(f616,plain,(
% 17.78/2.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~spl8_80),
% 17.78/2.60    inference(avatar_component_clause,[],[f615])).
% 17.78/2.60  fof(f807,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(sK2),sK2)) ) | (~spl8_1 | ~spl8_74 | ~spl8_109)),
% 17.78/2.60    inference(subsumption_resolution,[],[f805,f226])).
% 17.78/2.60  fof(f805,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(sK2),sK2)) ) | (~spl8_74 | ~spl8_109)),
% 17.78/2.60    inference(resolution,[],[f790,f573])).
% 17.78/2.60  fof(f790,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) ) | ~spl8_109),
% 17.78/2.60    inference(avatar_component_clause,[],[f789])).
% 17.78/2.60  fof(f1701,plain,(
% 17.78/2.60    spl8_200 | ~spl8_152 | ~spl8_185),
% 17.78/2.60    inference(avatar_split_clause,[],[f1369,f1357,f1159,f1699])).
% 17.78/2.60  fof(f1159,plain,(
% 17.78/2.60    spl8_152 <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_152])])).
% 17.78/2.60  fof(f1357,plain,(
% 17.78/2.60    spl8_185 <=> ! [X8] : (~r1_tarski(X8,k1_xboole_0) | k1_xboole_0 = X8)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_185])])).
% 17.78/2.60  fof(f1369,plain,(
% 17.78/2.60    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl8_152 | ~spl8_185)),
% 17.78/2.60    inference(resolution,[],[f1358,f1160])).
% 17.78/2.60  fof(f1160,plain,(
% 17.78/2.60    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | ~spl8_152),
% 17.78/2.60    inference(avatar_component_clause,[],[f1159])).
% 17.78/2.60  fof(f1358,plain,(
% 17.78/2.60    ( ! [X8] : (~r1_tarski(X8,k1_xboole_0) | k1_xboole_0 = X8) ) | ~spl8_185),
% 17.78/2.60    inference(avatar_component_clause,[],[f1357])).
% 17.78/2.60  fof(f1359,plain,(
% 17.78/2.60    spl8_185 | ~spl8_32 | ~spl8_53 | ~spl8_60),
% 17.78/2.60    inference(avatar_split_clause,[],[f506,f475,f435,f349,f1357])).
% 17.78/2.60  fof(f349,plain,(
% 17.78/2.60    spl8_32 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 17.78/2.60  fof(f475,plain,(
% 17.78/2.60    spl8_60 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(sK4(X1))))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 17.78/2.60  fof(f506,plain,(
% 17.78/2.60    ( ! [X8] : (~r1_tarski(X8,k1_xboole_0) | k1_xboole_0 = X8) ) | (~spl8_32 | ~spl8_53 | ~spl8_60)),
% 17.78/2.60    inference(forward_demodulation,[],[f493,f486])).
% 17.78/2.60  fof(f486,plain,(
% 17.78/2.60    ( ! [X0] : (k1_xboole_0 = sK4(X0)) ) | (~spl8_53 | ~spl8_60)),
% 17.78/2.60    inference(resolution,[],[f476,f436])).
% 17.78/2.60  fof(f476,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK4(X1))) | k1_xboole_0 = X0) ) | ~spl8_60),
% 17.78/2.60    inference(avatar_component_clause,[],[f475])).
% 17.78/2.60  fof(f493,plain,(
% 17.78/2.60    ( ! [X8,X9] : (k1_xboole_0 = X8 | ~r1_tarski(X8,sK4(X9))) ) | (~spl8_32 | ~spl8_60)),
% 17.78/2.60    inference(resolution,[],[f476,f350])).
% 17.78/2.60  fof(f350,plain,(
% 17.78/2.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl8_32),
% 17.78/2.60    inference(avatar_component_clause,[],[f349])).
% 17.78/2.60  fof(f1339,plain,(
% 17.78/2.60    spl8_181 | spl8_182 | ~spl8_183 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_125 | ~spl8_126 | ~spl8_180),
% 17.78/2.60    inference(avatar_split_clause,[],[f1329,f1316,f931,f913,f253,f249,f241,f233,f229,f225,f1337,f1334,f1331])).
% 17.78/2.60  fof(f1316,plain,(
% 17.78/2.60    spl8_180 <=> ! [X1,X3,X0,X2] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_180])])).
% 17.78/2.60  fof(f1329,plain,(
% 17.78/2.60    sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_125 | ~spl8_126 | ~spl8_180)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1328,f230])).
% 17.78/2.60  fof(f1328,plain,(
% 17.78/2.60    ~v1_funct_1(sK1) | sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_1 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_125 | ~spl8_126 | ~spl8_180)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1327,f250])).
% 17.78/2.60  fof(f1327,plain,(
% 17.78/2.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_1 | ~spl8_3 | ~spl8_5 | ~spl8_8 | ~spl8_125 | ~spl8_126 | ~spl8_180)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1326,f234])).
% 17.78/2.60  fof(f1326,plain,(
% 17.78/2.60    ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_1 | ~spl8_5 | ~spl8_8 | ~spl8_125 | ~spl8_126 | ~spl8_180)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1325,f226])).
% 17.78/2.60  fof(f1325,plain,(
% 17.78/2.60    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_5 | ~spl8_8 | ~spl8_125 | ~spl8_126 | ~spl8_180)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1324,f254])).
% 17.78/2.60  fof(f1324,plain,(
% 17.78/2.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_5 | ~spl8_125 | ~spl8_126 | ~spl8_180)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1323,f242])).
% 17.78/2.60  fof(f1323,plain,(
% 17.78/2.60    ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_125 | ~spl8_126 | ~spl8_180)),
% 17.78/2.60    inference(subsumption_resolution,[],[f1321,f932])).
% 17.78/2.60  fof(f1321,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_125 | ~spl8_180)),
% 17.78/2.60    inference(duplicate_literal_removal,[],[f1320])).
% 17.78/2.60  fof(f1320,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl8_125 | ~spl8_180)),
% 17.78/2.60    inference(superposition,[],[f1317,f914])).
% 17.78/2.60  fof(f1317,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relat_1(X2) != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3) ) | ~spl8_180),
% 17.78/2.60    inference(avatar_component_clause,[],[f1316])).
% 17.78/2.60  fof(f1318,plain,(
% 17.78/2.60    spl8_180 | ~spl8_56 | ~spl8_119),
% 17.78/2.60    inference(avatar_split_clause,[],[f882,f874,f447,f1316])).
% 17.78/2.60  fof(f874,plain,(
% 17.78/2.60    spl8_119 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).
% 17.78/2.60  fof(f882,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3) ) | (~spl8_56 | ~spl8_119)),
% 17.78/2.60    inference(duplicate_literal_removal,[],[f881])).
% 17.78/2.60  fof(f881,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl8_56 | ~spl8_119)),
% 17.78/2.60    inference(superposition,[],[f875,f448])).
% 17.78/2.60  fof(f875,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3) ) | ~spl8_119),
% 17.78/2.60    inference(avatar_component_clause,[],[f874])).
% 17.78/2.60  fof(f1281,plain,(
% 17.78/2.60    ~spl8_81 | spl8_174 | ~spl8_1 | ~spl8_7 | ~spl8_56 | ~spl8_74 | ~spl8_102 | ~spl8_122),
% 17.78/2.60    inference(avatar_split_clause,[],[f898,f888,f745,f572,f447,f249,f225,f1279,f618])).
% 17.78/2.60  fof(f745,plain,(
% 17.78/2.60    spl8_102 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).
% 17.78/2.60  fof(f898,plain,(
% 17.78/2.60    ( ! [X0] : (k6_relat_1(sK0) != k5_relat_1(X0,sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0) ) | (~spl8_1 | ~spl8_7 | ~spl8_56 | ~spl8_74 | ~spl8_102 | ~spl8_122)),
% 17.78/2.60    inference(backward_demodulation,[],[f759,f896])).
% 17.78/2.60  fof(f759,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k2_relat_1(X0) != k1_relat_1(sK2) | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0) ) | (~spl8_1 | ~spl8_74 | ~spl8_102)),
% 17.78/2.60    inference(subsumption_resolution,[],[f757,f226])).
% 17.78/2.60  fof(f757,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k2_relat_1(X0) != k1_relat_1(sK2) | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(X0,sK2) | k2_funct_1(sK2) = X0) ) | (~spl8_74 | ~spl8_102)),
% 17.78/2.60    inference(resolution,[],[f746,f573])).
% 17.78/2.60  fof(f746,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1) ) | ~spl8_102),
% 17.78/2.60    inference(avatar_component_clause,[],[f745])).
% 17.78/2.60  fof(f1161,plain,(
% 17.78/2.60    spl8_152 | ~spl8_14 | ~spl8_15 | ~spl8_23 | ~spl8_129),
% 17.78/2.60    inference(avatar_split_clause,[],[f984,f974,f313,f281,f277,f1159])).
% 17.78/2.60  fof(f277,plain,(
% 17.78/2.60    spl8_14 <=> ! [X0] : v1_relat_1(sK3(X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 17.78/2.60  fof(f281,plain,(
% 17.78/2.60    spl8_15 <=> ! [X0] : v1_funct_1(sK3(X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 17.78/2.60  fof(f313,plain,(
% 17.78/2.60    spl8_23 <=> ! [X0] : k1_relat_1(sK3(X0)) = X0),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 17.78/2.60  fof(f974,plain,(
% 17.78/2.60    spl8_129 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).
% 17.78/2.60  fof(f984,plain,(
% 17.78/2.60    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | (~spl8_14 | ~spl8_15 | ~spl8_23 | ~spl8_129)),
% 17.78/2.60    inference(subsumption_resolution,[],[f983,f282])).
% 17.78/2.60  fof(f282,plain,(
% 17.78/2.60    ( ! [X0] : (v1_funct_1(sK3(X0))) ) | ~spl8_15),
% 17.78/2.60    inference(avatar_component_clause,[],[f281])).
% 17.78/2.60  fof(f983,plain,(
% 17.78/2.60    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_funct_1(sK3(X0))) ) | (~spl8_14 | ~spl8_23 | ~spl8_129)),
% 17.78/2.60    inference(subsumption_resolution,[],[f981,f278])).
% 17.78/2.60  fof(f278,plain,(
% 17.78/2.60    ( ! [X0] : (v1_relat_1(sK3(X0))) ) | ~spl8_14),
% 17.78/2.60    inference(avatar_component_clause,[],[f277])).
% 17.78/2.60  fof(f981,plain,(
% 17.78/2.60    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(sK3(X0)) | ~v1_funct_1(sK3(X0))) ) | (~spl8_23 | ~spl8_129)),
% 17.78/2.60    inference(superposition,[],[f975,f314])).
% 17.78/2.60  fof(f314,plain,(
% 17.78/2.60    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) ) | ~spl8_23),
% 17.78/2.60    inference(avatar_component_clause,[],[f313])).
% 17.78/2.60  fof(f975,plain,(
% 17.78/2.60    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) ) | ~spl8_129),
% 17.78/2.60    inference(avatar_component_clause,[],[f974])).
% 17.78/2.60  fof(f1103,plain,(
% 17.78/2.60    spl8_111 | ~spl8_1 | ~spl8_2 | ~spl8_7 | ~spl8_8 | ~spl8_104 | ~spl8_125),
% 17.78/2.60    inference(avatar_split_clause,[],[f945,f913,f753,f253,f249,f229,f225,f796])).
% 17.78/2.60  fof(f753,plain,(
% 17.78/2.60    spl8_104 <=> ! [X1,X3,X5,X0,X2,X4] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).
% 17.78/2.60  fof(f945,plain,(
% 17.78/2.60    k6_partfun1(sK0) = k5_relat_1(sK1,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_7 | ~spl8_8 | ~spl8_104 | ~spl8_125)),
% 17.78/2.60    inference(subsumption_resolution,[],[f944,f230])).
% 17.78/2.60  fof(f944,plain,(
% 17.78/2.60    k6_partfun1(sK0) = k5_relat_1(sK1,sK2) | ~v1_funct_1(sK1) | (~spl8_1 | ~spl8_7 | ~spl8_8 | ~spl8_104 | ~spl8_125)),
% 17.78/2.60    inference(subsumption_resolution,[],[f943,f250])).
% 17.78/2.60  fof(f943,plain,(
% 17.78/2.60    k6_partfun1(sK0) = k5_relat_1(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl8_1 | ~spl8_8 | ~spl8_104 | ~spl8_125)),
% 17.78/2.60    inference(subsumption_resolution,[],[f942,f226])).
% 17.78/2.60  fof(f942,plain,(
% 17.78/2.60    k6_partfun1(sK0) = k5_relat_1(sK1,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl8_8 | ~spl8_104 | ~spl8_125)),
% 17.78/2.60    inference(subsumption_resolution,[],[f936,f254])).
% 17.78/2.60  fof(f936,plain,(
% 17.78/2.60    k6_partfun1(sK0) = k5_relat_1(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl8_104 | ~spl8_125)),
% 17.78/2.60    inference(superposition,[],[f914,f754])).
% 17.78/2.60  fof(f754,plain,(
% 17.78/2.60    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) ) | ~spl8_104),
% 17.78/2.60    inference(avatar_component_clause,[],[f753])).
% 17.78/2.60  fof(f976,plain,(
% 17.78/2.60    spl8_129 | ~spl8_9 | ~spl8_10 | ~spl8_29 | ~spl8_73),
% 17.78/2.60    inference(avatar_split_clause,[],[f645,f568,f337,f261,f257,f974])).
% 17.78/2.60  fof(f257,plain,(
% 17.78/2.60    spl8_9 <=> v1_relat_1(k1_xboole_0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 17.78/2.60  fof(f261,plain,(
% 17.78/2.60    spl8_10 <=> v1_funct_1(k1_xboole_0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 17.78/2.60  fof(f337,plain,(
% 17.78/2.60    spl8_29 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v5_funct_1(k1_xboole_0,X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 17.78/2.60  fof(f568,plain,(
% 17.78/2.60    spl8_73 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v5_funct_1(X1,X0) | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).
% 17.78/2.60  fof(f645,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))) ) | (~spl8_9 | ~spl8_10 | ~spl8_29 | ~spl8_73)),
% 17.78/2.60    inference(subsumption_resolution,[],[f644,f262])).
% 17.78/2.60  fof(f262,plain,(
% 17.78/2.60    v1_funct_1(k1_xboole_0) | ~spl8_10),
% 17.78/2.60    inference(avatar_component_clause,[],[f261])).
% 17.78/2.60  fof(f644,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))) ) | (~spl8_9 | ~spl8_29 | ~spl8_73)),
% 17.78/2.60    inference(subsumption_resolution,[],[f643,f258])).
% 17.78/2.60  fof(f258,plain,(
% 17.78/2.60    v1_relat_1(k1_xboole_0) | ~spl8_9),
% 17.78/2.60    inference(avatar_component_clause,[],[f257])).
% 17.78/2.60  fof(f643,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0))) ) | (~spl8_29 | ~spl8_73)),
% 17.78/2.60    inference(duplicate_literal_removal,[],[f642])).
% 17.78/2.60  fof(f642,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl8_29 | ~spl8_73)),
% 17.78/2.60    inference(resolution,[],[f569,f338])).
% 17.78/2.60  fof(f338,plain,(
% 17.78/2.60    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_29),
% 17.78/2.60    inference(avatar_component_clause,[],[f337])).
% 17.78/2.60  fof(f569,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~v5_funct_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(X1),k1_relat_1(X0))) ) | ~spl8_73),
% 17.78/2.60    inference(avatar_component_clause,[],[f568])).
% 17.78/2.60  fof(f964,plain,(
% 17.78/2.60    spl8_127 | ~spl8_7 | ~spl8_56 | ~spl8_94 | ~spl8_122),
% 17.78/2.60    inference(avatar_split_clause,[],[f899,f888,f697,f447,f249,f962])).
% 17.78/2.60  fof(f697,plain,(
% 17.78/2.60    spl8_94 <=> k2_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).
% 17.78/2.60  fof(f899,plain,(
% 17.78/2.60    sK0 = k2_relat_1(k6_relat_1(sK0)) | (~spl8_7 | ~spl8_56 | ~spl8_94 | ~spl8_122)),
% 17.78/2.60    inference(backward_demodulation,[],[f698,f896])).
% 17.78/2.60  fof(f698,plain,(
% 17.78/2.60    k2_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) | ~spl8_94),
% 17.78/2.60    inference(avatar_component_clause,[],[f697])).
% 17.78/2.60  fof(f933,plain,(
% 17.78/2.60    spl8_126 | ~spl8_17 | ~spl8_125),
% 17.78/2.60    inference(avatar_split_clause,[],[f929,f913,f289,f931])).
% 17.78/2.60  fof(f289,plain,(
% 17.78/2.60    spl8_17 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 17.78/2.60  fof(f929,plain,(
% 17.78/2.60    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (~spl8_17 | ~spl8_125)),
% 17.78/2.60    inference(backward_demodulation,[],[f290,f914])).
% 17.78/2.60  fof(f290,plain,(
% 17.78/2.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) | ~spl8_17),
% 17.78/2.60    inference(avatar_component_clause,[],[f289])).
% 17.78/2.60  fof(f928,plain,(
% 17.78/2.60    ~spl8_1 | ~spl8_2 | ~spl8_7 | ~spl8_8 | ~spl8_105 | spl8_124),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f927])).
% 17.78/2.60  fof(f927,plain,(
% 17.78/2.60    $false | (~spl8_1 | ~spl8_2 | ~spl8_7 | ~spl8_8 | ~spl8_105 | spl8_124)),
% 17.78/2.60    inference(subsumption_resolution,[],[f926,f230])).
% 17.78/2.60  fof(f926,plain,(
% 17.78/2.60    ~v1_funct_1(sK1) | (~spl8_1 | ~spl8_7 | ~spl8_8 | ~spl8_105 | spl8_124)),
% 17.78/2.60    inference(subsumption_resolution,[],[f925,f250])).
% 17.78/2.60  fof(f925,plain,(
% 17.78/2.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl8_1 | ~spl8_8 | ~spl8_105 | spl8_124)),
% 17.78/2.60    inference(subsumption_resolution,[],[f924,f226])).
% 17.78/2.60  fof(f924,plain,(
% 17.78/2.60    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl8_8 | ~spl8_105 | spl8_124)),
% 17.78/2.60    inference(subsumption_resolution,[],[f917,f254])).
% 17.78/2.60  fof(f917,plain,(
% 17.78/2.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl8_105 | spl8_124)),
% 17.78/2.60    inference(resolution,[],[f911,f763])).
% 17.78/2.60  fof(f763,plain,(
% 17.78/2.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) ) | ~spl8_105),
% 17.78/2.60    inference(avatar_component_clause,[],[f762])).
% 17.78/2.60  fof(f762,plain,(
% 17.78/2.60    spl8_105 <=> ! [X1,X3,X5,X0,X2,X4] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).
% 17.78/2.60  fof(f911,plain,(
% 17.78/2.60    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl8_124),
% 17.78/2.60    inference(avatar_component_clause,[],[f910])).
% 17.78/2.60  fof(f910,plain,(
% 17.78/2.60    spl8_124 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).
% 17.78/2.60  fof(f915,plain,(
% 17.78/2.60    ~spl8_124 | spl8_125 | ~spl8_17 | ~spl8_28 | ~spl8_95),
% 17.78/2.60    inference(avatar_split_clause,[],[f713,f701,f333,f289,f913,f910])).
% 17.78/2.60  fof(f701,plain,(
% 17.78/2.60    spl8_95 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).
% 17.78/2.60  fof(f713,plain,(
% 17.78/2.60    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl8_17 | ~spl8_28 | ~spl8_95)),
% 17.78/2.60    inference(subsumption_resolution,[],[f710,f334])).
% 17.78/2.60  fof(f710,plain,(
% 17.78/2.60    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl8_17 | ~spl8_95)),
% 17.78/2.60    inference(resolution,[],[f702,f290])).
% 17.78/2.60  fof(f702,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_95),
% 17.78/2.60    inference(avatar_component_clause,[],[f701])).
% 17.78/2.60  fof(f908,plain,(
% 17.78/2.60    spl8_123 | ~spl8_7 | ~spl8_56 | ~spl8_122),
% 17.78/2.60    inference(avatar_split_clause,[],[f896,f888,f447,f249,f906])).
% 17.78/2.60  fof(f890,plain,(
% 17.78/2.60    spl8_122 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_17 | ~spl8_117),
% 17.78/2.60    inference(avatar_split_clause,[],[f850,f839,f289,f253,f249,f241,f233,f229,f225,f888])).
% 17.78/2.60  fof(f839,plain,(
% 17.78/2.60    spl8_117 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).
% 17.78/2.60  fof(f850,plain,(
% 17.78/2.60    sK0 = k2_relset_1(sK0,sK0,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_17 | ~spl8_117)),
% 17.78/2.60    inference(subsumption_resolution,[],[f849,f226])).
% 17.78/2.60  fof(f849,plain,(
% 17.78/2.60    ~v1_funct_1(sK2) | sK0 = k2_relset_1(sK0,sK0,sK2) | (~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_17 | ~spl8_117)),
% 17.78/2.60    inference(subsumption_resolution,[],[f848,f254])).
% 17.78/2.60  fof(f848,plain,(
% 17.78/2.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | sK0 = k2_relset_1(sK0,sK0,sK2) | (~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_7 | ~spl8_17 | ~spl8_117)),
% 17.78/2.60    inference(subsumption_resolution,[],[f847,f242])).
% 17.78/2.60  fof(f847,plain,(
% 17.78/2.60    ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | sK0 = k2_relset_1(sK0,sK0,sK2) | (~spl8_2 | ~spl8_3 | ~spl8_7 | ~spl8_17 | ~spl8_117)),
% 17.78/2.60    inference(subsumption_resolution,[],[f846,f230])).
% 17.78/2.60  fof(f846,plain,(
% 17.78/2.60    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | sK0 = k2_relset_1(sK0,sK0,sK2) | (~spl8_3 | ~spl8_7 | ~spl8_17 | ~spl8_117)),
% 17.78/2.60    inference(subsumption_resolution,[],[f845,f250])).
% 17.78/2.60  fof(f845,plain,(
% 17.78/2.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | sK0 = k2_relset_1(sK0,sK0,sK2) | (~spl8_3 | ~spl8_17 | ~spl8_117)),
% 17.78/2.60    inference(subsumption_resolution,[],[f842,f234])).
% 17.78/2.60  fof(f842,plain,(
% 17.78/2.60    ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | sK0 = k2_relset_1(sK0,sK0,sK2) | (~spl8_17 | ~spl8_117)),
% 17.78/2.60    inference(resolution,[],[f840,f290])).
% 17.78/2.60  fof(f840,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) ) | ~spl8_117),
% 17.78/2.60    inference(avatar_component_clause,[],[f839])).
% 17.78/2.60  fof(f876,plain,(
% 17.78/2.60    spl8_119),
% 17.78/2.60    inference(avatar_split_clause,[],[f223,f874])).
% 17.78/2.60  fof(f223,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3) )),
% 17.78/2.60    inference(subsumption_resolution,[],[f199,f197])).
% 17.78/2.60  fof(f197,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | v2_funct_1(X2)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f102])).
% 17.78/2.60  fof(f102,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 17.78/2.60    inference(flattening,[],[f101])).
% 17.78/2.60  fof(f101,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 17.78/2.60    inference(ennf_transformation,[],[f47])).
% 17.78/2.60  fof(f47,axiom,(
% 17.78/2.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 17.78/2.60  fof(f199,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~v2_funct_1(X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3) )),
% 17.78/2.60    inference(cnf_transformation,[],[f104])).
% 17.78/2.60  fof(f104,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 17.78/2.60    inference(flattening,[],[f103])).
% 17.78/2.60  fof(f103,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 17.78/2.60    inference(ennf_transformation,[],[f49])).
% 17.78/2.60  fof(f49,axiom,(
% 17.78/2.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 17.78/2.60  fof(f861,plain,(
% 17.78/2.60    spl8_118),
% 17.78/2.60    inference(avatar_split_clause,[],[f203,f859])).
% 17.78/2.60  fof(f203,plain,(
% 17.78/2.60    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | ~v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) = X1) )),
% 17.78/2.60    inference(cnf_transformation,[],[f111])).
% 17.78/2.60  fof(f111,plain,(
% 17.78/2.60    ! [X0,X1,X2,X3] : (! [X4] : (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2 | ~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 17.78/2.60    inference(flattening,[],[f110])).
% 17.78/2.60  fof(f110,plain,(
% 17.78/2.60    ! [X0,X1,X2,X3] : (! [X4] : (((k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2) | (~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 17.78/2.60    inference(ennf_transformation,[],[f46])).
% 17.78/2.60  fof(f46,axiom,(
% 17.78/2.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).
% 17.78/2.60  fof(f841,plain,(
% 17.78/2.60    spl8_117),
% 17.78/2.60    inference(avatar_split_clause,[],[f196,f839])).
% 17.78/2.60  fof(f196,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 17.78/2.60    inference(cnf_transformation,[],[f100])).
% 17.78/2.60  fof(f100,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 17.78/2.60    inference(flattening,[],[f99])).
% 17.78/2.60  fof(f99,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 17.78/2.60    inference(ennf_transformation,[],[f45])).
% 17.78/2.60  fof(f45,axiom,(
% 17.78/2.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 17.78/2.60  fof(f791,plain,(
% 17.78/2.60    spl8_109),
% 17.78/2.60    inference(avatar_split_clause,[],[f195,f789])).
% 17.78/2.60  fof(f195,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f98])).
% 17.78/2.60  fof(f98,plain,(
% 17.78/2.60    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 17.78/2.60    inference(flattening,[],[f97])).
% 17.78/2.60  fof(f97,plain,(
% 17.78/2.60    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 17.78/2.60    inference(ennf_transformation,[],[f48])).
% 17.78/2.60  fof(f48,axiom,(
% 17.78/2.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 17.78/2.60  fof(f764,plain,(
% 17.78/2.60    spl8_105),
% 17.78/2.60    inference(avatar_split_clause,[],[f209,f762])).
% 17.78/2.60  fof(f209,plain,(
% 17.78/2.60    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f119])).
% 17.78/2.60  fof(f119,plain,(
% 17.78/2.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 17.78/2.60    inference(flattening,[],[f118])).
% 17.78/2.60  fof(f118,plain,(
% 17.78/2.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 17.78/2.60    inference(ennf_transformation,[],[f41])).
% 17.78/2.60  fof(f41,axiom,(
% 17.78/2.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 17.78/2.60  fof(f755,plain,(
% 17.78/2.60    spl8_104),
% 17.78/2.60    inference(avatar_split_clause,[],[f207,f753])).
% 17.78/2.60  fof(f207,plain,(
% 17.78/2.60    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f117])).
% 17.78/2.60  fof(f117,plain,(
% 17.78/2.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 17.78/2.60    inference(flattening,[],[f116])).
% 17.78/2.60  fof(f116,plain,(
% 17.78/2.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 17.78/2.60    inference(ennf_transformation,[],[f43])).
% 17.78/2.60  fof(f43,axiom,(
% 17.78/2.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 17.78/2.60  fof(f747,plain,(
% 17.78/2.60    spl8_102),
% 17.78/2.60    inference(avatar_split_clause,[],[f148,f745])).
% 17.78/2.60  fof(f148,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1) )),
% 17.78/2.60    inference(cnf_transformation,[],[f66])).
% 17.78/2.60  fof(f66,plain,(
% 17.78/2.60    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.78/2.60    inference(flattening,[],[f65])).
% 17.78/2.60  fof(f65,plain,(
% 17.78/2.60    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 17.78/2.60    inference(ennf_transformation,[],[f27])).
% 17.78/2.60  fof(f27,axiom,(
% 17.78/2.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 17.78/2.60  fof(f717,plain,(
% 17.78/2.60    spl8_97),
% 17.78/2.60    inference(avatar_split_clause,[],[f179,f715])).
% 17.78/2.60  fof(f179,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f86])).
% 17.78/2.60  fof(f86,plain,(
% 17.78/2.60    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 17.78/2.60    inference(flattening,[],[f85])).
% 17.78/2.60  fof(f85,plain,(
% 17.78/2.60    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 17.78/2.60    inference(ennf_transformation,[],[f44])).
% 17.78/2.60  fof(f44,axiom,(
% 17.78/2.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 17.78/2.60  fof(f703,plain,(
% 17.78/2.60    spl8_95),
% 17.78/2.60    inference(avatar_split_clause,[],[f205,f701])).
% 17.78/2.60  fof(f205,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f113])).
% 17.78/2.60  fof(f113,plain,(
% 17.78/2.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.78/2.60    inference(flattening,[],[f112])).
% 17.78/2.60  fof(f112,plain,(
% 17.78/2.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 17.78/2.60    inference(ennf_transformation,[],[f33])).
% 17.78/2.60  fof(f33,axiom,(
% 17.78/2.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 17.78/2.60  fof(f699,plain,(
% 17.78/2.60    ~spl8_81 | spl8_94 | ~spl8_1 | ~spl8_59 | ~spl8_74 | ~spl8_80),
% 17.78/2.60    inference(avatar_split_clause,[],[f625,f615,f572,f471,f225,f697,f618])).
% 17.78/2.60  fof(f471,plain,(
% 17.78/2.60    spl8_59 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 17.78/2.60  fof(f625,plain,(
% 17.78/2.60    k2_relat_1(sK2) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) | ~v1_relat_1(sK2) | (~spl8_1 | ~spl8_59 | ~spl8_74 | ~spl8_80)),
% 17.78/2.60    inference(backward_demodulation,[],[f585,f616])).
% 17.78/2.60  fof(f585,plain,(
% 17.78/2.60    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | (~spl8_1 | ~spl8_59 | ~spl8_74)),
% 17.78/2.60    inference(subsumption_resolution,[],[f581,f226])).
% 17.78/2.60  fof(f581,plain,(
% 17.78/2.60    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) | (~spl8_59 | ~spl8_74)),
% 17.78/2.60    inference(resolution,[],[f573,f472])).
% 17.78/2.60  fof(f472,plain,(
% 17.78/2.60    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))) ) | ~spl8_59),
% 17.78/2.60    inference(avatar_component_clause,[],[f471])).
% 17.78/2.60  fof(f623,plain,(
% 17.78/2.60    ~spl8_7 | ~spl8_39 | spl8_81),
% 17.78/2.60    inference(avatar_contradiction_clause,[],[f621])).
% 17.78/2.60  fof(f621,plain,(
% 17.78/2.60    $false | (~spl8_7 | ~spl8_39 | spl8_81)),
% 17.78/2.60    inference(unit_resulting_resolution,[],[f250,f619,f378])).
% 17.78/2.60  fof(f378,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_39),
% 17.78/2.60    inference(avatar_component_clause,[],[f377])).
% 17.78/2.60  fof(f377,plain,(
% 17.78/2.60    spl8_39 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 17.78/2.60  fof(f619,plain,(
% 17.78/2.60    ~v1_relat_1(sK2) | spl8_81),
% 17.78/2.60    inference(avatar_component_clause,[],[f618])).
% 17.78/2.60  fof(f620,plain,(
% 17.78/2.60    spl8_80 | ~spl8_81 | ~spl8_1 | ~spl8_62 | ~spl8_74),
% 17.78/2.60    inference(avatar_split_clause,[],[f583,f572,f483,f225,f618,f615])).
% 17.78/2.60  fof(f483,plain,(
% 17.78/2.60    spl8_62 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 17.78/2.60  fof(f583,plain,(
% 17.78/2.60    ~v1_relat_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | (~spl8_1 | ~spl8_62 | ~spl8_74)),
% 17.78/2.60    inference(subsumption_resolution,[],[f579,f226])).
% 17.78/2.60  fof(f579,plain,(
% 17.78/2.60    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | (~spl8_62 | ~spl8_74)),
% 17.78/2.60    inference(resolution,[],[f573,f484])).
% 17.78/2.60  fof(f484,plain,(
% 17.78/2.60    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) ) | ~spl8_62),
% 17.78/2.60    inference(avatar_component_clause,[],[f483])).
% 17.78/2.60  fof(f574,plain,(
% 17.78/2.60    spl8_74 | ~spl8_1 | ~spl8_4 | ~spl8_7 | ~spl8_64),
% 17.78/2.60    inference(avatar_split_clause,[],[f564,f517,f249,f237,f225,f572])).
% 17.78/2.60  fof(f237,plain,(
% 17.78/2.60    spl8_4 <=> v3_funct_2(sK2,sK0,sK0)),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 17.78/2.60  fof(f517,plain,(
% 17.78/2.60    spl8_64 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).
% 17.78/2.60  fof(f564,plain,(
% 17.78/2.60    v2_funct_1(sK2) | (~spl8_1 | ~spl8_4 | ~spl8_7 | ~spl8_64)),
% 17.78/2.60    inference(subsumption_resolution,[],[f563,f250])).
% 17.78/2.60  fof(f563,plain,(
% 17.78/2.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v2_funct_1(sK2) | (~spl8_1 | ~spl8_4 | ~spl8_64)),
% 17.78/2.60    inference(subsumption_resolution,[],[f561,f226])).
% 17.78/2.60  fof(f561,plain,(
% 17.78/2.60    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v2_funct_1(sK2) | (~spl8_4 | ~spl8_64)),
% 17.78/2.60    inference(resolution,[],[f518,f238])).
% 17.78/2.60  fof(f238,plain,(
% 17.78/2.60    v3_funct_2(sK2,sK0,sK0) | ~spl8_4),
% 17.78/2.60    inference(avatar_component_clause,[],[f237])).
% 17.78/2.60  fof(f518,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_1(X2)) ) | ~spl8_64),
% 17.78/2.60    inference(avatar_component_clause,[],[f517])).
% 17.78/2.60  fof(f570,plain,(
% 17.78/2.60    spl8_73),
% 17.78/2.60    inference(avatar_split_clause,[],[f147,f568])).
% 17.78/2.60  fof(f147,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v5_funct_1(X1,X0) | r1_tarski(k1_relat_1(X1),k1_relat_1(X0))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f64])).
% 17.78/2.60  fof(f64,plain,(
% 17.78/2.60    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) | ~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.78/2.60    inference(flattening,[],[f63])).
% 17.78/2.60  fof(f63,plain,(
% 17.78/2.60    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) | (~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 17.78/2.60    inference(ennf_transformation,[],[f23])).
% 17.78/2.60  fof(f23,axiom,(
% 17.78/2.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v5_funct_1(X1,X0) & v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(X1),k1_relat_1(X0))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).
% 17.78/2.60  fof(f519,plain,(
% 17.78/2.60    spl8_64),
% 17.78/2.60    inference(avatar_split_clause,[],[f192,f517])).
% 17.78/2.60  fof(f192,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f96])).
% 17.78/2.60  fof(f96,plain,(
% 17.78/2.60    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.78/2.60    inference(flattening,[],[f95])).
% 17.78/2.60  fof(f95,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.78/2.60    inference(ennf_transformation,[],[f39])).
% 17.78/2.60  fof(f39,axiom,(
% 17.78/2.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 17.78/2.60  fof(f514,plain,(
% 17.78/2.60    spl8_63 | ~spl8_16 | ~spl8_53 | ~spl8_60),
% 17.78/2.60    inference(avatar_split_clause,[],[f499,f475,f435,f285,f512])).
% 17.78/2.60  fof(f285,plain,(
% 17.78/2.60    spl8_16 <=> ! [X0] : v1_xboole_0(sK4(X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 17.78/2.60  fof(f499,plain,(
% 17.78/2.60    v1_xboole_0(k1_xboole_0) | (~spl8_16 | ~spl8_53 | ~spl8_60)),
% 17.78/2.60    inference(backward_demodulation,[],[f286,f486])).
% 17.78/2.60  fof(f286,plain,(
% 17.78/2.60    ( ! [X0] : (v1_xboole_0(sK4(X0))) ) | ~spl8_16),
% 17.78/2.60    inference(avatar_component_clause,[],[f285])).
% 17.78/2.60  fof(f485,plain,(
% 17.78/2.60    spl8_62),
% 17.78/2.60    inference(avatar_split_clause,[],[f146,f483])).
% 17.78/2.60  fof(f146,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f62])).
% 17.78/2.60  fof(f62,plain,(
% 17.78/2.60    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.78/2.60    inference(flattening,[],[f61])).
% 17.78/2.60  fof(f61,plain,(
% 17.78/2.60    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 17.78/2.60    inference(ennf_transformation,[],[f26])).
% 17.78/2.60  fof(f26,axiom,(
% 17.78/2.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 17.78/2.60  fof(f477,plain,(
% 17.78/2.60    spl8_60 | ~spl8_16 | ~spl8_57),
% 17.78/2.60    inference(avatar_split_clause,[],[f462,f455,f285,f475])).
% 17.78/2.60  fof(f462,plain,(
% 17.78/2.60    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(sK4(X1)))) ) | (~spl8_16 | ~spl8_57)),
% 17.78/2.60    inference(resolution,[],[f456,f286])).
% 17.78/2.60  fof(f473,plain,(
% 17.78/2.60    spl8_59),
% 17.78/2.60    inference(avatar_split_clause,[],[f144,f471])).
% 17.78/2.60  fof(f144,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f60])).
% 17.78/2.60  fof(f60,plain,(
% 17.78/2.60    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.78/2.60    inference(flattening,[],[f59])).
% 17.78/2.60  fof(f59,plain,(
% 17.78/2.60    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 17.78/2.60    inference(ennf_transformation,[],[f25])).
% 17.78/2.60  fof(f25,axiom,(
% 17.78/2.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 17.78/2.60  fof(f457,plain,(
% 17.78/2.60    spl8_57 | ~spl8_41 | ~spl8_51),
% 17.78/2.60    inference(avatar_split_clause,[],[f453,f425,f385,f455])).
% 17.78/2.60  fof(f385,plain,(
% 17.78/2.60    spl8_41 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 17.78/2.60  fof(f425,plain,(
% 17.78/2.60    spl8_51 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK6(X0,X1),X1))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 17.78/2.60  fof(f453,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0 | ~v1_xboole_0(X1)) ) | (~spl8_41 | ~spl8_51)),
% 17.78/2.60    inference(condensation,[],[f451])).
% 17.78/2.60  fof(f451,plain,(
% 17.78/2.60    ( ! [X4,X5,X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X5)) | ~v1_xboole_0(X5)) ) | (~spl8_41 | ~spl8_51)),
% 17.78/2.60    inference(resolution,[],[f426,f386])).
% 17.78/2.60  fof(f386,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) | ~spl8_41),
% 17.78/2.60    inference(avatar_component_clause,[],[f385])).
% 17.78/2.60  fof(f426,plain,(
% 17.78/2.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl8_51),
% 17.78/2.60    inference(avatar_component_clause,[],[f425])).
% 17.78/2.60  fof(f449,plain,(
% 17.78/2.60    spl8_56),
% 17.78/2.60    inference(avatar_split_clause,[],[f184,f447])).
% 17.78/2.60  fof(f184,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f90])).
% 17.78/2.60  fof(f90,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.78/2.60    inference(ennf_transformation,[],[f32])).
% 17.78/2.60  fof(f32,axiom,(
% 17.78/2.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 17.78/2.60  fof(f437,plain,(
% 17.78/2.60    spl8_53 | ~spl8_18 | ~spl8_26 | ~spl8_48),
% 17.78/2.60    inference(avatar_split_clause,[],[f433,f413,f325,f293,f435])).
% 17.78/2.60  fof(f293,plain,(
% 17.78/2.60    spl8_18 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 17.78/2.60  fof(f325,plain,(
% 17.78/2.60    spl8_26 <=> ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 17.78/2.60  fof(f413,plain,(
% 17.78/2.60    spl8_48 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 17.78/2.60    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 17.78/2.60  fof(f433,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl8_18 | ~spl8_26 | ~spl8_48)),
% 17.78/2.60    inference(subsumption_resolution,[],[f432,f294])).
% 17.78/2.60  fof(f294,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl8_18),
% 17.78/2.60    inference(avatar_component_clause,[],[f293])).
% 17.78/2.60  fof(f432,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl8_26 | ~spl8_48)),
% 17.78/2.60    inference(superposition,[],[f414,f326])).
% 17.78/2.60  fof(f326,plain,(
% 17.78/2.60    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) ) | ~spl8_26),
% 17.78/2.60    inference(avatar_component_clause,[],[f325])).
% 17.78/2.60  fof(f414,plain,(
% 17.78/2.60    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl8_48),
% 17.78/2.60    inference(avatar_component_clause,[],[f413])).
% 17.78/2.60  fof(f427,plain,(
% 17.78/2.60    spl8_51),
% 17.78/2.60    inference(avatar_split_clause,[],[f171,f425])).
% 17.78/2.60  fof(f171,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f78])).
% 17.78/2.60  fof(f78,plain,(
% 17.78/2.60    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 17.78/2.60    inference(flattening,[],[f77])).
% 17.78/2.60  fof(f77,plain,(
% 17.78/2.60    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 17.78/2.60    inference(ennf_transformation,[],[f5])).
% 17.78/2.60  fof(f5,axiom,(
% 17.78/2.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 17.78/2.60  fof(f419,plain,(
% 17.78/2.60    spl8_49),
% 17.78/2.60    inference(avatar_split_clause,[],[f219,f417])).
% 17.78/2.60  fof(f219,plain,(
% 17.78/2.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 17.78/2.60    inference(duplicate_literal_removal,[],[f218])).
% 17.78/2.60  fof(f218,plain,(
% 17.78/2.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 17.78/2.60    inference(equality_resolution,[],[f204])).
% 17.78/2.60  fof(f204,plain,(
% 17.78/2.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f113])).
% 17.78/2.60  fof(f415,plain,(
% 17.78/2.60    spl8_48),
% 17.78/2.60    inference(avatar_split_clause,[],[f176,f413])).
% 17.78/2.60  fof(f176,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f83])).
% 17.78/2.60  fof(f83,plain,(
% 17.78/2.60    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 17.78/2.60    inference(ennf_transformation,[],[f15])).
% 17.78/2.60  fof(f15,axiom,(
% 17.78/2.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 17.78/2.60  fof(f395,plain,(
% 17.78/2.60    spl8_43),
% 17.78/2.60    inference(avatar_split_clause,[],[f163,f393])).
% 17.78/2.60  fof(f163,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f72])).
% 17.78/2.60  fof(f72,plain,(
% 17.78/2.60    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 17.78/2.60    inference(ennf_transformation,[],[f30])).
% 17.78/2.60  fof(f30,axiom,(
% 17.78/2.60    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 17.78/2.60  fof(f391,plain,(
% 17.78/2.60    spl8_42),
% 17.78/2.60    inference(avatar_split_clause,[],[f162,f389])).
% 17.78/2.60  fof(f162,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f71])).
% 17.78/2.60  fof(f71,plain,(
% 17.78/2.60    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 17.78/2.60    inference(ennf_transformation,[],[f31])).
% 17.78/2.60  fof(f31,axiom,(
% 17.78/2.60    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 17.78/2.60  fof(f387,plain,(
% 17.78/2.60    spl8_41),
% 17.78/2.60    inference(avatar_split_clause,[],[f201,f385])).
% 17.78/2.60  fof(f201,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f107])).
% 17.78/2.60  fof(f107,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 17.78/2.60    inference(ennf_transformation,[],[f19])).
% 17.78/2.60  fof(f19,axiom,(
% 17.78/2.60    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 17.78/2.60  fof(f379,plain,(
% 17.78/2.60    spl8_39),
% 17.78/2.60    inference(avatar_split_clause,[],[f183,f377])).
% 17.78/2.60  fof(f183,plain,(
% 17.78/2.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f89])).
% 17.78/2.60  fof(f89,plain,(
% 17.78/2.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.78/2.60    inference(ennf_transformation,[],[f29])).
% 17.78/2.60  fof(f29,axiom,(
% 17.78/2.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 17.78/2.60  fof(f351,plain,(
% 17.78/2.60    spl8_32),
% 17.78/2.60    inference(avatar_split_clause,[],[f180,f349])).
% 17.78/2.60  fof(f180,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f17])).
% 17.78/2.60  fof(f17,axiom,(
% 17.78/2.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 17.78/2.60  fof(f339,plain,(
% 17.78/2.60    spl8_29),
% 17.78/2.60    inference(avatar_split_clause,[],[f142,f337])).
% 17.78/2.60  fof(f142,plain,(
% 17.78/2.60    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 17.78/2.60    inference(cnf_transformation,[],[f58])).
% 17.78/2.60  fof(f58,plain,(
% 17.78/2.60    ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.78/2.60    inference(flattening,[],[f57])).
% 17.78/2.60  fof(f57,plain,(
% 17.78/2.60    ! [X0] : (v5_funct_1(k1_xboole_0,X0) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 17.78/2.60    inference(ennf_transformation,[],[f22])).
% 17.78/2.60  fof(f22,axiom,(
% 17.78/2.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 17.78/2.60  fof(f335,plain,(
% 17.78/2.60    spl8_28),
% 17.78/2.60    inference(avatar_split_clause,[],[f139,f333])).
% 17.78/2.60  fof(f139,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f42])).
% 17.78/2.60  fof(f42,axiom,(
% 17.78/2.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 17.78/2.60  fof(f331,plain,(
% 17.78/2.60    spl8_27),
% 17.78/2.60    inference(avatar_split_clause,[],[f133,f329])).
% 17.78/2.60  fof(f133,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f36])).
% 17.78/2.60  fof(f36,axiom,(
% 17.78/2.60    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 17.78/2.60  fof(f327,plain,(
% 17.78/2.60    spl8_26),
% 17.78/2.60    inference(avatar_split_clause,[],[f221,f325])).
% 17.78/2.60  fof(f221,plain,(
% 17.78/2.60    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 17.78/2.60    inference(subsumption_resolution,[],[f212,f130])).
% 17.78/2.60  fof(f130,plain,(
% 17.78/2.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f10])).
% 17.78/2.60  fof(f10,axiom,(
% 17.78/2.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 17.78/2.60  fof(f212,plain,(
% 17.78/2.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 17.78/2.60    inference(equality_resolution,[],[f177])).
% 17.78/2.60  fof(f177,plain,(
% 17.78/2.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 17.78/2.60    inference(cnf_transformation,[],[f84])).
% 17.78/2.60  fof(f84,plain,(
% 17.78/2.60    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 17.78/2.60    inference(ennf_transformation,[],[f14])).
% 17.78/2.60  fof(f14,axiom,(
% 17.78/2.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 17.78/2.60  fof(f315,plain,(
% 17.78/2.60    spl8_23),
% 17.78/2.60    inference(avatar_split_clause,[],[f153,f313])).
% 17.78/2.60  fof(f153,plain,(
% 17.78/2.60    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 17.78/2.60    inference(cnf_transformation,[],[f69])).
% 17.78/2.60  fof(f69,plain,(
% 17.78/2.60    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 17.78/2.60    inference(ennf_transformation,[],[f21])).
% 17.78/2.60  fof(f21,axiom,(
% 17.78/2.60    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).
% 17.78/2.60  fof(f295,plain,(
% 17.78/2.60    spl8_18),
% 17.78/2.60    inference(avatar_split_clause,[],[f130,f293])).
% 17.78/2.60  fof(f291,plain,(
% 17.78/2.60    spl8_17),
% 17.78/2.60    inference(avatar_split_clause,[],[f124,f289])).
% 17.78/2.60  fof(f124,plain,(
% 17.78/2.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f53,plain,(
% 17.78/2.60    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 17.78/2.60    inference(flattening,[],[f52])).
% 17.78/2.60  fof(f52,plain,(
% 17.78/2.60    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 17.78/2.60    inference(ennf_transformation,[],[f51])).
% 17.78/2.60  fof(f51,negated_conjecture,(
% 17.78/2.60    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 17.78/2.60    inference(negated_conjecture,[],[f50])).
% 17.78/2.60  fof(f50,conjecture,(
% 17.78/2.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 17.78/2.60  fof(f287,plain,(
% 17.78/2.60    spl8_16),
% 17.78/2.60    inference(avatar_split_clause,[],[f155,f285])).
% 17.78/2.60  fof(f155,plain,(
% 17.78/2.60    ( ! [X0] : (v1_xboole_0(sK4(X0))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f4])).
% 17.78/2.60  fof(f4,axiom,(
% 17.78/2.60    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 17.78/2.60  fof(f283,plain,(
% 17.78/2.60    spl8_15),
% 17.78/2.60    inference(avatar_split_clause,[],[f152,f281])).
% 17.78/2.60  fof(f152,plain,(
% 17.78/2.60    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f69])).
% 17.78/2.60  fof(f279,plain,(
% 17.78/2.60    spl8_14),
% 17.78/2.60    inference(avatar_split_clause,[],[f151,f277])).
% 17.78/2.60  fof(f151,plain,(
% 17.78/2.60    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 17.78/2.60    inference(cnf_transformation,[],[f69])).
% 17.78/2.60  fof(f271,plain,(
% 17.78/2.60    ~spl8_12),
% 17.78/2.60    inference(avatar_split_clause,[],[f125,f269])).
% 17.78/2.60  fof(f125,plain,(
% 17.78/2.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f263,plain,(
% 17.78/2.60    spl8_10),
% 17.78/2.60    inference(avatar_split_clause,[],[f136,f261])).
% 17.78/2.60  fof(f136,plain,(
% 17.78/2.60    v1_funct_1(k1_xboole_0)),
% 17.78/2.60    inference(cnf_transformation,[],[f28])).
% 17.78/2.60  fof(f28,axiom,(
% 17.78/2.60    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 17.78/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 17.78/2.60  fof(f259,plain,(
% 17.78/2.60    spl8_9),
% 17.78/2.60    inference(avatar_split_clause,[],[f134,f257])).
% 17.78/2.60  fof(f134,plain,(
% 17.78/2.60    v1_relat_1(k1_xboole_0)),
% 17.78/2.60    inference(cnf_transformation,[],[f28])).
% 17.78/2.60  fof(f255,plain,(
% 17.78/2.60    spl8_8),
% 17.78/2.60    inference(avatar_split_clause,[],[f129,f253])).
% 17.78/2.60  fof(f129,plain,(
% 17.78/2.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f251,plain,(
% 17.78/2.60    spl8_7),
% 17.78/2.60    inference(avatar_split_clause,[],[f123,f249])).
% 17.78/2.60  fof(f123,plain,(
% 17.78/2.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f247,plain,(
% 17.78/2.60    spl8_6),
% 17.78/2.60    inference(avatar_split_clause,[],[f128,f245])).
% 17.78/2.60  fof(f128,plain,(
% 17.78/2.60    v3_funct_2(sK1,sK0,sK0)),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f243,plain,(
% 17.78/2.60    spl8_5),
% 17.78/2.60    inference(avatar_split_clause,[],[f127,f241])).
% 17.78/2.60  fof(f127,plain,(
% 17.78/2.60    v1_funct_2(sK1,sK0,sK0)),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f239,plain,(
% 17.78/2.60    spl8_4),
% 17.78/2.60    inference(avatar_split_clause,[],[f122,f237])).
% 17.78/2.60  fof(f122,plain,(
% 17.78/2.60    v3_funct_2(sK2,sK0,sK0)),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f235,plain,(
% 17.78/2.60    spl8_3),
% 17.78/2.60    inference(avatar_split_clause,[],[f121,f233])).
% 17.78/2.60  fof(f121,plain,(
% 17.78/2.60    v1_funct_2(sK2,sK0,sK0)),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f231,plain,(
% 17.78/2.60    spl8_2),
% 17.78/2.60    inference(avatar_split_clause,[],[f126,f229])).
% 17.78/2.60  fof(f126,plain,(
% 17.78/2.60    v1_funct_1(sK1)),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  fof(f227,plain,(
% 17.78/2.60    spl8_1),
% 17.78/2.60    inference(avatar_split_clause,[],[f120,f225])).
% 17.78/2.60  fof(f120,plain,(
% 17.78/2.60    v1_funct_1(sK2)),
% 17.78/2.60    inference(cnf_transformation,[],[f53])).
% 17.78/2.60  % SZS output end Proof for theBenchmark
% 17.78/2.60  % (6675)------------------------------
% 17.78/2.60  % (6675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.78/2.60  % (6675)Termination reason: Refutation
% 17.78/2.60  
% 17.78/2.60  % (6675)Memory used [KB]: 17526
% 17.78/2.60  % (6675)Time elapsed: 1.556 s
% 17.78/2.60  % (6675)------------------------------
% 17.78/2.60  % (6675)------------------------------
% 17.78/2.61  % (6600)Success in time 2.261 s
%------------------------------------------------------------------------------
