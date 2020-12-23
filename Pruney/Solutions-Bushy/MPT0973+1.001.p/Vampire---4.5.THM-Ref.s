%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0973+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:59 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  432 ( 860 expanded)
%              Number of leaves         :  101 ( 418 expanded)
%              Depth                    :   11
%              Number of atoms          : 1457 (2784 expanded)
%              Number of equality atoms :  215 ( 527 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f101,f111,f115,f131,f143,f149,f162,f166,f174,f178,f187,f197,f201,f206,f210,f214,f225,f243,f247,f257,f265,f290,f294,f313,f333,f351,f355,f369,f387,f403,f417,f503,f530,f578,f582,f594,f634,f670,f685,f689,f697,f749,f768,f777,f791,f795,f803,f814,f822,f826,f838,f1040,f1105,f1308,f1320,f1393,f1417,f1430,f1449,f1718,f1772,f1859,f2101,f2138,f2508,f2701,f2713,f2735,f2748,f2752,f2779,f2788,f2793,f2802,f2849,f2896,f2981,f3024,f3083,f3089,f3173,f3178])).

fof(f3178,plain,
    ( ~ spl7_4
    | ~ spl7_81
    | spl7_282 ),
    inference(avatar_contradiction_clause,[],[f3174])).

fof(f3174,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_81
    | spl7_282 ),
    inference(unit_resulting_resolution,[],[f96,f2980,f684])).

fof(f684,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f683])).

fof(f683,plain,
    ( spl7_81
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f2980,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | spl7_282 ),
    inference(avatar_component_clause,[],[f2979])).

fof(f2979,plain,
    ( spl7_282
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_282])])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f3173,plain,
    ( ~ spl7_4
    | spl7_68
    | ~ spl7_82
    | ~ spl7_101
    | ~ spl7_236 ),
    inference(avatar_contradiction_clause,[],[f3172])).

fof(f3172,plain,
    ( $false
    | ~ spl7_4
    | spl7_68
    | ~ spl7_82
    | ~ spl7_101
    | ~ spl7_236 ),
    inference(subsumption_resolution,[],[f3171,f837])).

fof(f837,plain,
    ( ! [X2] : m1_subset_1(X2,k1_zfmisc_1(X2))
    | ~ spl7_101 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl7_101
  <=> ! [X2] : m1_subset_1(X2,k1_zfmisc_1(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f3171,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_4
    | spl7_68
    | ~ spl7_82
    | ~ spl7_236 ),
    inference(subsumption_resolution,[],[f3170,f96])).

fof(f3170,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl7_68
    | ~ spl7_82
    | ~ spl7_236 ),
    inference(subsumption_resolution,[],[f3168,f688])).

fof(f688,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl7_82
  <=> ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f3168,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl7_68
    | ~ spl7_236 ),
    inference(superposition,[],[f577,f2507])).

fof(f2507,plain,
    ( ! [X24,X23,X21,X22,X20] :
        ( k1_xboole_0 = k4_relset_1(X21,X22,X24,k1_xboole_0,X20,X23)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl7_236 ),
    inference(avatar_component_clause,[],[f2506])).

fof(f2506,plain,
    ( spl7_236
  <=> ! [X20,X22,X21,X23,X24] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | k1_xboole_0 = k4_relset_1(X21,X22,X24,k1_xboole_0,X20,X23) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_236])])).

fof(f577,plain,
    ( ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,k1_xboole_0,sK3,k1_xboole_0),sK0,k1_xboole_0)
    | spl7_68 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl7_68
  <=> v1_funct_2(k4_relset_1(sK0,sK1,sK1,k1_xboole_0,sK3,k1_xboole_0),sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f3089,plain,
    ( ~ spl7_4
    | ~ spl7_291 ),
    inference(avatar_contradiction_clause,[],[f3084])).

fof(f3084,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_291 ),
    inference(unit_resulting_resolution,[],[f96,f3082])).

fof(f3082,plain,
    ( ! [X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ spl7_291 ),
    inference(avatar_component_clause,[],[f3081])).

fof(f3081,plain,
    ( spl7_291
  <=> ! [X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_291])])).

fof(f3083,plain,
    ( spl7_291
    | spl7_259
    | spl7_7
    | ~ spl7_281
    | ~ spl7_55
    | spl7_64
    | ~ spl7_69
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f3019,f2746,f580,f528,f385,f2973,f106,f2730,f3081])).

fof(f2730,plain,
    ( spl7_259
  <=> ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_259])])).

fof(f106,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f2973,plain,
    ( spl7_281
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_281])])).

fof(f385,plain,
    ( spl7_55
  <=> sK1 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f528,plain,
    ( spl7_64
  <=> v1_funct_2(k5_relat_1(sK3,sK4),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f580,plain,
    ( spl7_69
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f2746,plain,
    ( spl7_262
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( k1_xboole_0 = X0
        | k1_relat_1(X1) != X2
        | v1_funct_2(k5_relat_1(X1,X3),X2,X0)
        | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_262])])).

fof(f3019,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK1)
        | k1_xboole_0 = sK2
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
    | ~ spl7_55
    | spl7_64
    | ~ spl7_69
    | ~ spl7_262 ),
    inference(forward_demodulation,[],[f3018,f386])).

fof(f386,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f385])).

fof(f3018,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = sK2
        | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
    | spl7_64
    | ~ spl7_69
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f3016,f581])).

fof(f581,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f580])).

fof(f3016,plain,
    ( ! [X0,X1] :
        ( sK0 != k1_relat_1(sK3)
        | k1_xboole_0 = sK2
        | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
    | spl7_64
    | ~ spl7_262 ),
    inference(resolution,[],[f529,f2747])).

fof(f2747,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_2(k5_relat_1(X1,X3),X2,X0)
        | k1_relat_1(X1) != X2
        | k1_xboole_0 = X0
        | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) )
    | ~ spl7_262 ),
    inference(avatar_component_clause,[],[f2746])).

fof(f529,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,sK2)
    | spl7_64 ),
    inference(avatar_component_clause,[],[f528])).

fof(f3024,plain,
    ( spl7_47
    | ~ spl7_2
    | ~ spl7_4
    | spl7_8
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f2814,f292,f109,f95,f87,f315])).

fof(f315,plain,
    ( spl7_47
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f87,plain,
    ( spl7_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f109,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f292,plain,
    ( spl7_44
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f2814,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_4
    | spl7_8
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f705,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK1
    | spl7_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f705,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f635,f96])).

fof(f635,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_2
    | ~ spl7_44 ),
    inference(resolution,[],[f88,f293])).

fof(f293,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f292])).

fof(f88,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f2981,plain,
    ( ~ spl7_282
    | ~ spl7_20
    | spl7_281 ),
    inference(avatar_split_clause,[],[f2976,f2973,f160,f2979])).

fof(f160,plain,
    ( spl7_20
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f2976,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl7_20
    | spl7_281 ),
    inference(resolution,[],[f2974,f161])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f2974,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | spl7_281 ),
    inference(avatar_component_clause,[],[f2973])).

fof(f2896,plain,
    ( ~ spl7_58
    | ~ spl7_3
    | ~ spl7_46
    | ~ spl7_49
    | spl7_51 ),
    inference(avatar_split_clause,[],[f2803,f349,f331,f311,f91,f414])).

fof(f414,plain,
    ( spl7_58
  <=> v1_funct_2(k5_relat_1(sK3,sK4),k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f91,plain,
    ( spl7_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f311,plain,
    ( spl7_46
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f331,plain,
    ( spl7_49
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f349,plain,
    ( spl7_51
  <=> v1_funct_2(k4_relset_1(k1_xboole_0,sK1,sK1,sK2,sK3,sK4),k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f2803,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),k1_xboole_0,sK2)
    | ~ spl7_3
    | ~ spl7_46
    | ~ spl7_49
    | spl7_51 ),
    inference(subsumption_resolution,[],[f379,f332])).

fof(f332,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f331])).

fof(f379,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_3
    | ~ spl7_46
    | spl7_51 ),
    inference(subsumption_resolution,[],[f378,f92])).

fof(f92,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f378,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),k1_xboole_0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_46
    | spl7_51 ),
    inference(superposition,[],[f350,f312])).

fof(f312,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f311])).

fof(f350,plain,
    ( ~ v1_funct_2(k4_relset_1(k1_xboole_0,sK1,sK1,sK2,sK3,sK4),k1_xboole_0,sK2)
    | spl7_51 ),
    inference(avatar_component_clause,[],[f349])).

fof(f2849,plain,
    ( spl7_78
    | ~ spl7_13
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f2821,f632,f129,f659])).

fof(f659,plain,
    ( spl7_78
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f129,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f632,plain,
    ( spl7_74
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f2821,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_13
    | ~ spl7_74 ),
    inference(resolution,[],[f633,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f633,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f632])).

fof(f2802,plain,
    ( ~ spl7_101
    | ~ spl7_167
    | ~ spl7_258 ),
    inference(avatar_contradiction_clause,[],[f2801])).

fof(f2801,plain,
    ( $false
    | ~ spl7_101
    | ~ spl7_167
    | ~ spl7_258 ),
    inference(subsumption_resolution,[],[f2798,f837])).

fof(f2798,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_167
    | ~ spl7_258 ),
    inference(superposition,[],[f2728,f1717])).

fof(f1717,plain,
    ( ! [X8] : k1_xboole_0 = k2_zfmisc_1(X8,k1_xboole_0)
    | ~ spl7_167 ),
    inference(avatar_component_clause,[],[f1716])).

fof(f1716,plain,
    ( spl7_167
  <=> ! [X8] : k1_xboole_0 = k2_zfmisc_1(X8,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_167])])).

fof(f2728,plain,
    ( ! [X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ spl7_258 ),
    inference(avatar_component_clause,[],[f2727])).

fof(f2727,plain,
    ( spl7_258
  <=> ! [X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).

fof(f2793,plain,
    ( ~ spl7_3
    | ~ spl7_259 ),
    inference(avatar_contradiction_clause,[],[f2789])).

fof(f2789,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_259 ),
    inference(unit_resulting_resolution,[],[f92,f2731])).

fof(f2731,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl7_259 ),
    inference(avatar_component_clause,[],[f2730])).

fof(f2788,plain,
    ( ~ spl7_101
    | ~ spl7_167
    | ~ spl7_266 ),
    inference(avatar_contradiction_clause,[],[f2787])).

fof(f2787,plain,
    ( $false
    | ~ spl7_101
    | ~ spl7_167
    | ~ spl7_266 ),
    inference(subsumption_resolution,[],[f2786,f837])).

fof(f2786,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_167
    | ~ spl7_266 ),
    inference(superposition,[],[f2778,f1717])).

fof(f2778,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl7_266 ),
    inference(avatar_component_clause,[],[f2777])).

fof(f2777,plain,
    ( spl7_266
  <=> ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_266])])).

fof(f2779,plain,
    ( spl7_266
    | ~ spl7_99
    | spl7_263 ),
    inference(avatar_split_clause,[],[f2765,f2750,f824,f2777])).

fof(f824,plain,
    ( spl7_99
  <=> ! [X3,X4] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f2750,plain,
    ( spl7_263
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_263])])).

fof(f2765,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl7_99
    | spl7_263 ),
    inference(resolution,[],[f2751,f825])).

fof(f825,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl7_99 ),
    inference(avatar_component_clause,[],[f824])).

fof(f2751,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl7_263 ),
    inference(avatar_component_clause,[],[f2750])).

fof(f2752,plain,
    ( ~ spl7_263
    | ~ spl7_20
    | spl7_260 ),
    inference(avatar_split_clause,[],[f2740,f2733,f160,f2750])).

fof(f2733,plain,
    ( spl7_260
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_260])])).

fof(f2740,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl7_20
    | spl7_260 ),
    inference(resolution,[],[f2734,f161])).

fof(f2734,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl7_260 ),
    inference(avatar_component_clause,[],[f2733])).

fof(f2748,plain,
    ( spl7_262
    | ~ spl7_24
    | ~ spl7_94
    | ~ spl7_137 ),
    inference(avatar_split_clause,[],[f1434,f1428,f789,f176,f2746])).

fof(f176,plain,
    ( spl7_24
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f789,plain,
    ( spl7_94
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f1428,plain,
    ( spl7_137
  <=> ! [X1,X3,X0,X2] :
        ( k1_relat_1(X0) != X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_2(k5_relat_1(X0,X1),X2,X3)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_137])])).

fof(f1434,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k1_xboole_0 = X0
        | k1_relat_1(X1) != X2
        | v1_funct_2(k5_relat_1(X1,X3),X2,X0)
        | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) )
    | ~ spl7_24
    | ~ spl7_94
    | ~ spl7_137 ),
    inference(subsumption_resolution,[],[f1433,f177])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f176])).

fof(f1433,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k1_xboole_0 = X0
        | k1_relat_1(X1) != X2
        | v1_funct_2(k5_relat_1(X1,X3),X2,X0)
        | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X3))
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) )
    | ~ spl7_24
    | ~ spl7_94
    | ~ spl7_137 ),
    inference(subsumption_resolution,[],[f1431,f177])).

fof(f1431,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k1_xboole_0 = X0
        | k1_relat_1(X1) != X2
        | v1_funct_2(k5_relat_1(X1,X3),X2,X0)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X3))
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) )
    | ~ spl7_94
    | ~ spl7_137 ),
    inference(resolution,[],[f1429,f790])).

fof(f790,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f789])).

fof(f1429,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_xboole_0 = X3
        | k1_relat_1(X0) != X2
        | v1_funct_2(k5_relat_1(X0,X1),X2,X3)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl7_137 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f2735,plain,
    ( spl7_258
    | spl7_259
    | ~ spl7_260
    | ~ spl7_55
    | spl7_106
    | ~ spl7_203
    | ~ spl7_257 ),
    inference(avatar_split_clause,[],[f2722,f2711,f2136,f1103,f385,f2733,f2730,f2727])).

fof(f1103,plain,
    ( spl7_106
  <=> v1_funct_2(k5_relat_1(k1_xboole_0,sK4),k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f2136,plain,
    ( spl7_203
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_203])])).

fof(f2711,plain,
    ( spl7_257
  <=> ! [X1,X3,X0,X2,X4] :
        ( v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_257])])).

fof(f2722,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl7_55
    | spl7_106
    | ~ spl7_203
    | ~ spl7_257 ),
    inference(forward_demodulation,[],[f2721,f2137])).

fof(f2137,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_203 ),
    inference(avatar_component_clause,[],[f2136])).

fof(f2721,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl7_55
    | spl7_106
    | ~ spl7_257 ),
    inference(forward_demodulation,[],[f2714,f386])).

fof(f2714,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | spl7_106
    | ~ spl7_257 ),
    inference(resolution,[],[f2712,f1104])).

fof(f1104,plain,
    ( ~ v1_funct_2(k5_relat_1(k1_xboole_0,sK4),k1_xboole_0,sK2)
    | spl7_106 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f2712,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) )
    | ~ spl7_257 ),
    inference(avatar_component_clause,[],[f2711])).

fof(f2713,plain,
    ( spl7_257
    | ~ spl7_169
    | ~ spl7_256 ),
    inference(avatar_split_clause,[],[f2702,f2699,f1770,f2711])).

fof(f1770,plain,
    ( spl7_169
  <=> ! [X16,X14] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X16)))
        | k1_xboole_0 = k1_relat_1(X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).

fof(f2699,plain,
    ( spl7_256
  <=> ! [X1,X3,X0,X2,X4] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_256])])).

fof(f2702,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) )
    | ~ spl7_169
    | ~ spl7_256 ),
    inference(subsumption_resolution,[],[f2700,f1771])).

fof(f1771,plain,
    ( ! [X14,X16] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X16)))
        | k1_xboole_0 = k1_relat_1(X14) )
    | ~ spl7_169 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f2700,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) )
    | ~ spl7_256 ),
    inference(avatar_component_clause,[],[f2699])).

fof(f2701,plain,
    ( spl7_256
    | ~ spl7_24
    | ~ spl7_94
    | ~ spl7_135 ),
    inference(avatar_split_clause,[],[f1425,f1415,f789,f176,f2699])).

fof(f1415,plain,
    ( spl7_135
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
        | v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f1425,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) )
    | ~ spl7_24
    | ~ spl7_94
    | ~ spl7_135 ),
    inference(subsumption_resolution,[],[f1424,f177])).

fof(f1424,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) )
    | ~ spl7_24
    | ~ spl7_94
    | ~ spl7_135 ),
    inference(subsumption_resolution,[],[f1422,f177])).

fof(f1422,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) )
    | ~ spl7_94
    | ~ spl7_135 ),
    inference(resolution,[],[f1416,f790])).

fof(f1416,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
        | k1_xboole_0 != k1_relat_1(X0)
        | v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl7_135 ),
    inference(avatar_component_clause,[],[f1415])).

fof(f2508,plain,
    ( spl7_236
    | ~ spl7_13
    | ~ spl7_132
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f1492,f1447,f1391,f129,f2506])).

fof(f1391,plain,
    ( spl7_132
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | v1_xboole_0(k4_relset_1(X3,X4,X1,k1_xboole_0,X2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f1447,plain,
    ( spl7_140
  <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f1492,plain,
    ( ! [X24,X23,X21,X22,X20] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | k1_xboole_0 = k4_relset_1(X21,X22,X24,k1_xboole_0,X20,X23) )
    | ~ spl7_13
    | ~ spl7_132
    | ~ spl7_140 ),
    inference(backward_demodulation,[],[f1397,f1453])).

fof(f1453,plain,
    ( ! [X8] : k1_xboole_0 = k2_zfmisc_1(X8,k1_xboole_0)
    | ~ spl7_13
    | ~ spl7_140 ),
    inference(resolution,[],[f1448,f130])).

fof(f1448,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl7_140 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f1397,plain,
    ( ! [X24,X23,X21,X22,X20] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,k1_xboole_0)))
        | k1_xboole_0 = k4_relset_1(X21,X22,X24,k1_xboole_0,X20,X23) )
    | ~ spl7_13
    | ~ spl7_132 ),
    inference(resolution,[],[f1392,f130])).

fof(f1392,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_xboole_0(k4_relset_1(X3,X4,X1,k1_xboole_0,X2,X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) )
    | ~ spl7_132 ),
    inference(avatar_component_clause,[],[f1391])).

fof(f2138,plain,
    ( spl7_203
    | ~ spl7_17
    | ~ spl7_201 ),
    inference(avatar_split_clause,[],[f2114,f2099,f147,f2136])).

fof(f147,plain,
    ( spl7_17
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f2099,plain,
    ( spl7_201
  <=> ! [X0] :
        ( k2_relat_1(k1_xboole_0) = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_201])])).

fof(f2114,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_17
    | ~ spl7_201 ),
    inference(resolution,[],[f2100,f148])).

fof(f148,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f2100,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k2_relat_1(k1_xboole_0) = X0 )
    | ~ spl7_201 ),
    inference(avatar_component_clause,[],[f2099])).

fof(f2101,plain,
    ( spl7_201
    | ~ spl7_101
    | ~ spl7_178 ),
    inference(avatar_split_clause,[],[f1864,f1857,f836,f2099])).

fof(f1857,plain,
    ( spl7_178
  <=> ! [X13,X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | k2_relat_1(X10) = X13
        | ~ v1_xboole_0(X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).

fof(f1864,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl7_101
    | ~ spl7_178 ),
    inference(resolution,[],[f1858,f837])).

fof(f1858,plain,
    ( ! [X10,X13] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | k2_relat_1(X10) = X13
        | ~ v1_xboole_0(X13) )
    | ~ spl7_178 ),
    inference(avatar_component_clause,[],[f1857])).

fof(f1859,plain,
    ( spl7_178
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_122
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f1502,f1447,f1306,f164,f129,f1857])).

fof(f164,plain,
    ( spl7_21
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f1306,plain,
    ( spl7_122
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,k1_xboole_0))))
        | v1_xboole_0(k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f1502,plain,
    ( ! [X10,X13] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
        | k2_relat_1(X10) = X13
        | ~ v1_xboole_0(X13) )
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_122
    | ~ spl7_140 ),
    inference(forward_demodulation,[],[f1464,f1453])).

fof(f1464,plain,
    ( ! [X10,X13,X11] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,k1_xboole_0)))
        | k2_relat_1(X10) = X13
        | ~ v1_xboole_0(X13) )
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_122
    | ~ spl7_140 ),
    inference(backward_demodulation,[],[f1311,f1453])).

fof(f1311,plain,
    ( ! [X12,X10,X13,X11] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,k2_zfmisc_1(X12,k1_xboole_0))))
        | k2_relat_1(X10) = X13
        | ~ v1_xboole_0(X13) )
    | ~ spl7_21
    | ~ spl7_122 ),
    inference(resolution,[],[f1307,f165])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f164])).

fof(f1307,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k2_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,k1_xboole_0)))) )
    | ~ spl7_122 ),
    inference(avatar_component_clause,[],[f1306])).

fof(f1772,plain,
    ( spl7_169
    | ~ spl7_13
    | ~ spl7_124
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f1470,f1447,f1318,f129,f1770])).

fof(f1318,plain,
    ( spl7_124
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)))
        | v1_xboole_0(k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f1470,plain,
    ( ! [X14,X16] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X16)))
        | k1_xboole_0 = k1_relat_1(X14) )
    | ~ spl7_13
    | ~ spl7_124
    | ~ spl7_140 ),
    inference(backward_demodulation,[],[f1326,f1453])).

fof(f1326,plain,
    ( ! [X14,X15,X16] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,k1_xboole_0),X16)))
        | k1_xboole_0 = k1_relat_1(X14) )
    | ~ spl7_13
    | ~ spl7_124 ),
    inference(resolution,[],[f1319,f130])).

fof(f1319,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2))) )
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1718,plain,
    ( spl7_167
    | ~ spl7_13
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f1453,f1447,f129,f1716])).

fof(f1449,plain,
    ( spl7_140
    | ~ spl7_31
    | ~ spl7_101 ),
    inference(avatar_split_clause,[],[f1263,f836,f208,f1447])).

fof(f208,plain,
    ( spl7_31
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f1263,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl7_31
    | ~ spl7_101 ),
    inference(resolution,[],[f837,f209])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f208])).

fof(f1430,plain,
    ( spl7_137
    | ~ spl7_36
    | ~ spl7_93 ),
    inference(avatar_split_clause,[],[f778,f775,f245,f1428])).

fof(f245,plain,
    ( spl7_36
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f775,plain,
    ( spl7_93
  <=> ! [X1,X0,X2] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f778,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relat_1(X0) != X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_2(k5_relat_1(X0,X1),X2,X3)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl7_36
    | ~ spl7_93 ),
    inference(superposition,[],[f776,f246])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f245])).

fof(f776,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl7_93 ),
    inference(avatar_component_clause,[],[f775])).

fof(f1417,plain,
    ( spl7_135
    | ~ spl7_36
    | ~ spl7_91 ),
    inference(avatar_split_clause,[],[f769,f766,f245,f1415])).

fof(f766,plain,
    ( spl7_91
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f769,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
        | v1_funct_2(k5_relat_1(X0,X1),k1_xboole_0,X2)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl7_36
    | ~ spl7_91 ),
    inference(superposition,[],[f767,f246])).

fof(f767,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f766])).

fof(f1393,plain,
    ( spl7_132
    | ~ spl7_31
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f381,f353,f208,f1391])).

fof(f353,plain,
    ( spl7_52
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f381,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | v1_xboole_0(k4_relset_1(X3,X4,X1,k1_xboole_0,X2,X0)) )
    | ~ spl7_31
    | ~ spl7_52 ),
    inference(resolution,[],[f354,f209])).

fof(f354,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f353])).

fof(f1320,plain,
    ( spl7_124
    | ~ spl7_31
    | ~ spl7_83 ),
    inference(avatar_split_clause,[],[f698,f695,f208,f1318])).

fof(f695,plain,
    ( spl7_83
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f698,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)))
        | v1_xboole_0(k1_relat_1(X0)) )
    | ~ spl7_31
    | ~ spl7_83 ),
    inference(resolution,[],[f696,f209])).

fof(f696,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f695])).

fof(f1308,plain,
    ( spl7_122
    | ~ spl7_31
    | ~ spl7_81 ),
    inference(avatar_split_clause,[],[f690,f683,f208,f1306])).

fof(f690,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,k1_xboole_0))))
        | v1_xboole_0(k2_relat_1(X0)) )
    | ~ spl7_31
    | ~ spl7_81 ),
    inference(resolution,[],[f684,f209])).

fof(f1105,plain,
    ( ~ spl7_106
    | spl7_58
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f1066,f659,f414,f1103])).

fof(f1066,plain,
    ( ~ v1_funct_2(k5_relat_1(k1_xboole_0,sK4),k1_xboole_0,sK2)
    | spl7_58
    | ~ spl7_78 ),
    inference(forward_demodulation,[],[f415,f660])).

fof(f660,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f659])).

fof(f415,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),k1_xboole_0,sK2)
    | spl7_58 ),
    inference(avatar_component_clause,[],[f414])).

fof(f1040,plain,
    ( spl7_9
    | ~ spl7_23
    | ~ spl7_91
    | ~ spl7_98
    | ~ spl7_100 ),
    inference(avatar_contradiction_clause,[],[f1039])).

fof(f1039,plain,
    ( $false
    | spl7_9
    | ~ spl7_23
    | ~ spl7_91
    | ~ spl7_98
    | ~ spl7_100 ),
    inference(subsumption_resolution,[],[f1038,f962])).

fof(f962,plain,
    ( ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)
    | ~ spl7_23
    | ~ spl7_91
    | ~ spl7_98
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f961,f834])).

fof(f834,plain,
    ( ! [X3] : k1_xboole_0 = X3
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f833])).

fof(f833,plain,
    ( spl7_100
  <=> ! [X3] : k1_xboole_0 = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f961,plain,
    ( ! [X4,X3] : v1_funct_2(sK6(k1_xboole_0,X3),k1_xboole_0,X4)
    | ~ spl7_23
    | ~ spl7_91
    | ~ spl7_98
    | ~ spl7_100 ),
    inference(subsumption_resolution,[],[f960,f902])).

fof(f902,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f901,f834])).

fof(f901,plain,
    ( ! [X0,X1] : m1_subset_1(sK6(X0,X1),k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f839,f834])).

fof(f839,plain,
    ( ! [X0,X1] : m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_23
    | ~ spl7_100 ),
    inference(backward_demodulation,[],[f173,f834])).

fof(f173,plain,
    ( ! [X0,X1] : m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_23
  <=> ! [X1,X0] : m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f960,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
        | v1_funct_2(sK6(k1_xboole_0,X3),k1_xboole_0,X4) )
    | ~ spl7_91
    | ~ spl7_98
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f959,f834])).

fof(f959,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK6(k1_xboole_0,X3),k1_xboole_0)
        | v1_funct_2(sK6(k1_xboole_0,X3),k1_xboole_0,X4) )
    | ~ spl7_91
    | ~ spl7_98
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f872,f834])).

fof(f872,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK6(k1_xboole_0,X3),k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK6(k1_xboole_0,X3),k1_xboole_0,X4) )
    | ~ spl7_91
    | ~ spl7_98
    | ~ spl7_100 ),
    inference(backward_demodulation,[],[f831,f834])).

fof(f831,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK6(k1_xboole_0,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
        | v1_funct_2(sK6(k1_xboole_0,X3),k1_xboole_0,X4) )
    | ~ spl7_91
    | ~ spl7_98 ),
    inference(trivial_inequality_removal,[],[f829])).

fof(f829,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(sK6(k1_xboole_0,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
        | v1_funct_2(sK6(k1_xboole_0,X3),k1_xboole_0,X4) )
    | ~ spl7_91
    | ~ spl7_98 ),
    inference(superposition,[],[f767,f821])).

fof(f821,plain,
    ( ! [X1] : k1_xboole_0 = k1_relat_1(sK6(k1_xboole_0,X1))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f820])).

fof(f820,plain,
    ( spl7_98
  <=> ! [X1] : k1_xboole_0 = k1_relat_1(sK6(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f1038,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_9
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f1037,f834])).

fof(f1037,plain,
    ( ~ v1_funct_2(k4_relset_1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK3,sK4),k1_xboole_0,k1_xboole_0)
    | spl7_9
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f1036,f834])).

fof(f1036,plain,
    ( ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,k1_xboole_0,sK3,sK4),sK0,k1_xboole_0)
    | spl7_9
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f114,f834])).

fof(f114,plain,
    ( ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),sK0,sK2)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_9
  <=> v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f838,plain,
    ( spl7_100
    | spl7_101
    | ~ spl7_23
    | ~ spl7_32
    | ~ spl7_89 ),
    inference(avatar_split_clause,[],[f764,f747,f212,f172,f836,f833])).

fof(f212,plain,
    ( spl7_32
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f747,plain,
    ( spl7_89
  <=> ! [X1,X2] :
        ( k1_xboole_0 = X1
        | k1_relset_1(X2,X1,sK6(X2,X1)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f764,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(X2,k1_zfmisc_1(X2))
        | k1_xboole_0 = X3 )
    | ~ spl7_23
    | ~ spl7_32
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f757,f173])).

fof(f757,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(X2,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK6(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_xboole_0 = X3 )
    | ~ spl7_32
    | ~ spl7_89 ),
    inference(superposition,[],[f213,f748])).

fof(f748,plain,
    ( ! [X2,X1] :
        ( k1_relset_1(X2,X1,sK6(X2,X1)) = X2
        | k1_xboole_0 = X1 )
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f747])).

fof(f213,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f212])).

fof(f826,plain,
    ( spl7_99
    | ~ spl7_83
    | ~ spl7_97 ),
    inference(avatar_split_clause,[],[f817,f812,f695,f824])).

fof(f812,plain,
    ( spl7_97
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f817,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl7_83
    | ~ spl7_97 ),
    inference(superposition,[],[f696,f813])).

fof(f813,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f812])).

fof(f822,plain,
    ( spl7_98
    | ~ spl7_23
    | ~ spl7_29
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f680,f668,f199,f172,f820])).

fof(f199,plain,
    ( spl7_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f668,plain,
    ( spl7_80
  <=> ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK6(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f680,plain,
    ( ! [X1] : k1_xboole_0 = k1_relat_1(sK6(k1_xboole_0,X1))
    | ~ spl7_23
    | ~ spl7_29
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f673,f173])).

fof(f673,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_relat_1(sK6(k1_xboole_0,X1))
        | ~ m1_subset_1(sK6(k1_xboole_0,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl7_29
    | ~ spl7_80 ),
    inference(superposition,[],[f669,f200])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f199])).

fof(f669,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK6(k1_xboole_0,X0))
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f668])).

fof(f814,plain,
    ( spl7_97
    | ~ spl7_29
    | ~ spl7_77
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f810,f793,f654,f199,f812])).

fof(f654,plain,
    ( spl7_77
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f793,plain,
    ( spl7_95
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f810,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_29
    | ~ spl7_77
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f804,f794])).

fof(f794,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f793])).

fof(f804,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_29
    | ~ spl7_77 ),
    inference(superposition,[],[f655,f200])).

fof(f655,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f654])).

fof(f803,plain,
    ( spl7_77
    | ~ spl7_35
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f672,f668,f241,f654])).

fof(f241,plain,
    ( spl7_35
  <=> ! [X8] : k1_xboole_0 = sK6(X8,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f672,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_35
    | ~ spl7_80 ),
    inference(superposition,[],[f669,f242])).

fof(f242,plain,
    ( ! [X8] : k1_xboole_0 = sK6(X8,k1_xboole_0)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f241])).

fof(f795,plain,
    ( spl7_95
    | ~ spl7_23
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f248,f241,f172,f793])).

fof(f248,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_23
    | ~ spl7_35 ),
    inference(superposition,[],[f173,f242])).

fof(f791,plain,
    ( spl7_94
    | ~ spl7_46
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f383,f353,f311,f789])).

fof(f383,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_46
    | ~ spl7_52 ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_46
    | ~ spl7_52 ),
    inference(superposition,[],[f354,f312])).

fof(f777,plain,
    ( spl7_93
    | ~ spl7_29
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f296,f288,f199,f775])).

fof(f288,plain,
    ( spl7_43
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) != X0
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f296,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl7_29
    | ~ spl7_43 ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_29
    | ~ spl7_43 ),
    inference(superposition,[],[f289,f200])).

fof(f289,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f288])).

fof(f768,plain,
    ( spl7_91
    | ~ spl7_29
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f279,f263,f199,f766])).

fof(f263,plain,
    ( spl7_39
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl7_29
    | ~ spl7_39 ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl7_29
    | ~ spl7_39 ),
    inference(superposition,[],[f264,f200])).

fof(f264,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f263])).

fof(f749,plain,
    ( spl7_89
    | ~ spl7_16
    | ~ spl7_23
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f309,f292,f172,f141,f747])).

fof(f141,plain,
    ( spl7_16
  <=> ! [X1,X0] : v1_funct_2(sK6(X0,X1),X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f309,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = X1
        | k1_relset_1(X2,X1,sK6(X2,X1)) = X2 )
    | ~ spl7_16
    | ~ spl7_23
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f304,f173])).

fof(f304,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = X1
        | k1_relset_1(X2,X1,sK6(X2,X1)) = X2
        | ~ m1_subset_1(sK6(X2,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl7_16
    | ~ spl7_44 ),
    inference(resolution,[],[f293,f142])).

fof(f142,plain,
    ( ! [X0,X1] : v1_funct_2(sK6(X0,X1),X0,X1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f697,plain,
    ( spl7_83
    | ~ spl7_29
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f239,f212,f199,f695])).

fof(f239,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_29
    | ~ spl7_32 ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_29
    | ~ spl7_32 ),
    inference(superposition,[],[f213,f200])).

fof(f689,plain,
    ( spl7_82
    | ~ spl7_16
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f249,f241,f141,f687])).

fof(f249,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl7_16
    | ~ spl7_35 ),
    inference(superposition,[],[f142,f242])).

fof(f685,plain,
    ( spl7_81
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f228,f204,f195,f683])).

fof(f195,plain,
    ( spl7_28
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f204,plain,
    ( spl7_30
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f228,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(superposition,[],[f205,f196])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f195])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f204])).

fof(f670,plain,
    ( spl7_80
    | ~ spl7_16
    | ~ spl7_23
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f277,f255,f172,f141,f668])).

fof(f255,plain,
    ( spl7_37
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f277,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK6(k1_xboole_0,X0))
    | ~ spl7_16
    | ~ spl7_23
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f275,f173])).

fof(f275,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK6(k1_xboole_0,X0))
        | ~ m1_subset_1(sK6(k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl7_16
    | ~ spl7_37 ),
    inference(resolution,[],[f256,f142])).

fof(f256,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(X2,k1_xboole_0,X1)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f255])).

fof(f634,plain,
    ( spl7_74
    | ~ spl7_31
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f612,f592,f208,f632])).

fof(f592,plain,
    ( spl7_70
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f612,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_31
    | ~ spl7_70 ),
    inference(resolution,[],[f593,f209])).

fof(f593,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f592])).

fof(f594,plain,
    ( spl7_70
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f584,f109,f95,f592])).

fof(f584,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f96,f418])).

fof(f418,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f582,plain,
    ( spl7_69
    | ~ spl7_4
    | ~ spl7_29
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f515,f315,f199,f95,f580])).

fof(f515,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_4
    | ~ spl7_29
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f510,f96])).

fof(f510,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_29
    | ~ spl7_47 ),
    inference(superposition,[],[f316,f200])).

fof(f316,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f315])).

fof(f578,plain,
    ( ~ spl7_68
    | ~ spl7_7
    | spl7_9
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f558,f501,f113,f106,f576])).

fof(f501,plain,
    ( spl7_63
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f558,plain,
    ( ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,k1_xboole_0,sK3,k1_xboole_0),sK0,k1_xboole_0)
    | ~ spl7_7
    | spl7_9
    | ~ spl7_63 ),
    inference(backward_demodulation,[],[f538,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f538,plain,
    ( ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,k1_xboole_0),sK0,sK2)
    | spl7_9
    | ~ spl7_63 ),
    inference(backward_demodulation,[],[f114,f502])).

fof(f502,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f501])).

fof(f530,plain,
    ( ~ spl7_64
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f519,f311,f113,f95,f91,f528])).

fof(f519,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,sK2)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f518,f96])).

fof(f518,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3
    | spl7_9
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f517,f92])).

fof(f517,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_9
    | ~ spl7_46 ),
    inference(superposition,[],[f114,f312])).

fof(f503,plain,
    ( spl7_63
    | ~ spl7_13
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f459,f401,f129,f501])).

fof(f401,plain,
    ( spl7_57
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f459,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_13
    | ~ spl7_57 ),
    inference(resolution,[],[f402,f130])).

fof(f402,plain,
    ( v1_xboole_0(sK4)
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f401])).

fof(f417,plain,
    ( spl7_53
    | spl7_7
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f388,f292,f91,f83,f106,f357])).

fof(f357,plain,
    ( spl7_53
  <=> sK1 = k1_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f83,plain,
    ( spl7_1
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f388,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f370,f92])).

fof(f370,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_44 ),
    inference(resolution,[],[f84,f293])).

fof(f84,plain,
    ( v1_funct_2(sK4,sK1,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f403,plain,
    ( spl7_57
    | ~ spl7_31
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f394,f367,f208,f401])).

fof(f367,plain,
    ( spl7_54
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f394,plain,
    ( v1_xboole_0(sK4)
    | ~ spl7_31
    | ~ spl7_54 ),
    inference(resolution,[],[f368,f209])).

fof(f368,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f367])).

fof(f387,plain,
    ( spl7_55
    | ~ spl7_3
    | ~ spl7_29
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f376,f357,f199,f91,f385])).

fof(f376,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ spl7_3
    | ~ spl7_29
    | ~ spl7_53 ),
    inference(subsumption_resolution,[],[f371,f92])).

fof(f371,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_29
    | ~ spl7_53 ),
    inference(superposition,[],[f358,f200])).

fof(f358,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f357])).

fof(f369,plain,
    ( spl7_54
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f361,f106,f91,f367])).

fof(f361,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f92,f107])).

fof(f355,plain,(
    spl7_52 ),
    inference(avatar_split_clause,[],[f76,f353])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f351,plain,
    ( ~ spl7_51
    | ~ spl7_6
    | spl7_9 ),
    inference(avatar_split_clause,[],[f343,f113,f103,f349])).

fof(f103,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f343,plain,
    ( ~ v1_funct_2(k4_relset_1(k1_xboole_0,sK1,sK1,sK2,sK3,sK4),k1_xboole_0,sK2)
    | ~ spl7_6
    | spl7_9 ),
    inference(backward_demodulation,[],[f114,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f333,plain,
    ( spl7_49
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f321,f103,f95,f331])).

fof(f321,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f96,f104])).

fof(f313,plain,(
    spl7_46 ),
    inference(avatar_split_clause,[],[f75,f311])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f294,plain,(
    spl7_44 ),
    inference(avatar_split_clause,[],[f73,f292])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f290,plain,(
    spl7_43 ),
    inference(avatar_split_clause,[],[f72,f288])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f265,plain,(
    spl7_39 ),
    inference(avatar_split_clause,[],[f78,f263])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f257,plain,(
    spl7_37 ),
    inference(avatar_split_clause,[],[f77,f255])).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f247,plain,(
    spl7_36 ),
    inference(avatar_split_clause,[],[f49,f245])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f243,plain,
    ( spl7_35
    | ~ spl7_13
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f232,f223,f129,f241])).

fof(f223,plain,
    ( spl7_34
  <=> ! [X0] : v1_xboole_0(sK6(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f232,plain,
    ( ! [X8] : k1_xboole_0 = sK6(X8,k1_xboole_0)
    | ~ spl7_13
    | ~ spl7_34 ),
    inference(resolution,[],[f224,f130])).

fof(f224,plain,
    ( ! [X0] : v1_xboole_0(sK6(X0,k1_xboole_0))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl7_34
    | ~ spl7_23
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f219,f208,f172,f223])).

fof(f219,plain,
    ( ! [X0] : v1_xboole_0(sK6(X0,k1_xboole_0))
    | ~ spl7_23
    | ~ spl7_31 ),
    inference(resolution,[],[f209,f173])).

fof(f214,plain,(
    spl7_32 ),
    inference(avatar_split_clause,[],[f67,f212])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f210,plain,
    ( spl7_31
    | ~ spl7_17
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f189,f185,f147,f208])).

fof(f185,plain,
    ( spl7_26
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl7_17
    | ~ spl7_26 ),
    inference(resolution,[],[f186,f148])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X2) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f185])).

fof(f206,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f66,f204])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f201,plain,(
    spl7_29 ),
    inference(avatar_split_clause,[],[f65,f199])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f197,plain,(
    spl7_28 ),
    inference(avatar_split_clause,[],[f64,f195])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f187,plain,(
    spl7_26 ),
    inference(avatar_split_clause,[],[f52,f185])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f178,plain,(
    spl7_24 ),
    inference(avatar_split_clause,[],[f63,f176])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f174,plain,(
    spl7_23 ),
    inference(avatar_split_clause,[],[f57,f172])).

fof(f57,plain,(
    ! [X0,X1] : m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f166,plain,(
    spl7_21 ),
    inference(avatar_split_clause,[],[f56,f164])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f162,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f55,f160])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f149,plain,
    ( spl7_17
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f145,f129,f99,f147])).

fof(f99,plain,
    ( spl7_5
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f145,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(backward_demodulation,[],[f100,f144])).

fof(f144,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(resolution,[],[f130,f100])).

fof(f100,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f143,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f62,f141])).

fof(f62,plain,(
    ! [X0,X1] : v1_funct_2(sK6(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f131,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f50,f129])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f115,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f45,f113])).

fof(f45,plain,(
    ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 = X2
            | k1_xboole_0 != X1 )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 = X2
            | k1_xboole_0 != X1 )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2) )
           => ( ~ ( k1_xboole_0 != X0
                  & k1_xboole_0 != X2
                  & k1_xboole_0 = X1 )
             => v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2) )
         => ( ~ ( k1_xboole_0 != X0
                & k1_xboole_0 != X2
                & k1_xboole_0 = X1 )
           => v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_funct_2)).

fof(f111,plain,
    ( spl7_6
    | spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f42,f109,f106,f103])).

fof(f42,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f97,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f47,f95])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
