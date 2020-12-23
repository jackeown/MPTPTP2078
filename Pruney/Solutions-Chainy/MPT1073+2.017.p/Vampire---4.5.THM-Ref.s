%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:58 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 386 expanded)
%              Number of leaves         :   58 ( 185 expanded)
%              Depth                    :    7
%              Number of atoms          :  731 (1216 expanded)
%              Number of equality atoms :  103 ( 175 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f97,f109,f113,f118,f122,f131,f140,f144,f156,f164,f171,f175,f179,f195,f198,f202,f234,f266,f289,f297,f324,f370,f386,f401,f436,f449,f510,f535,f571,f575,f623,f661,f791,f803,f928,f1055,f1100,f1114,f1134,f1141])).

fof(f1141,plain,
    ( ~ spl9_24
    | ~ spl9_138 ),
    inference(avatar_contradiction_clause,[],[f1140])).

fof(f1140,plain,
    ( $false
    | ~ spl9_24
    | ~ spl9_138 ),
    inference(subsumption_resolution,[],[f1139,f174])).

fof(f174,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl9_24
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f1139,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl9_138 ),
    inference(equality_resolution,[],[f1133])).

fof(f1133,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl9_138 ),
    inference(avatar_component_clause,[],[f1132])).

fof(f1132,plain,
    ( spl9_138
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | sK0 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).

fof(f1134,plain,
    ( spl9_138
    | ~ spl9_59
    | ~ spl9_81
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f1117,f1112,f659,f384,f1132])).

fof(f384,plain,
    ( spl9_59
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK8(X0,X1,sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f659,plain,
    ( spl9_81
  <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f1112,plain,
    ( spl9_136
  <=> ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(sK8(X0,sK1,sK3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f1117,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | sK0 != X0 )
    | ~ spl9_59
    | ~ spl9_81
    | ~ spl9_136 ),
    inference(duplicate_literal_removal,[],[f1116])).

fof(f1116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(X0,k2_relat_1(sK3))
        | sK0 != X0 )
    | ~ spl9_59
    | ~ spl9_81
    | ~ spl9_136 ),
    inference(forward_demodulation,[],[f1115,f660])).

fof(f660,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK1)
    | ~ spl9_81 ),
    inference(avatar_component_clause,[],[f659])).

fof(f1115,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | sK0 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK1)) )
    | ~ spl9_59
    | ~ spl9_136 ),
    inference(resolution,[],[f1113,f385])).

fof(f385,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK8(X0,X1,sK3),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl9_59 ),
    inference(avatar_component_clause,[],[f384])).

fof(f1113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(X0,sK1,sK3),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK3))
        | sK0 != X0 )
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1114,plain,
    ( spl9_136
    | ~ spl9_9
    | ~ spl9_133 ),
    inference(avatar_split_clause,[],[f1102,f1098,f107,f1112])).

fof(f107,plain,
    ( spl9_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1098,plain,
    ( spl9_133
  <=> ! [X2] :
        ( sK0 != X2
        | ~ m1_subset_1(sK8(X2,sK1,sK3),sK1)
        | ~ r2_hidden(X2,k2_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f1102,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(sK8(X0,sK1,sK3),sK1) )
    | ~ spl9_9
    | ~ spl9_133 ),
    inference(resolution,[],[f1099,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f1099,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK8(X2,sK1,sK3),sK1)
        | sK0 != X2
        | ~ r2_hidden(X2,k2_relat_1(sK3)) )
    | ~ spl9_133 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f1100,plain,
    ( spl9_133
    | ~ spl9_5
    | ~ spl9_127 ),
    inference(avatar_split_clause,[],[f1062,f1053,f91,f1098])).

fof(f91,plain,
    ( spl9_5
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | sK0 != k1_funct_1(sK3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f1053,plain,
    ( spl9_127
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK8(X0,sK1,sK3)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f1062,plain,
    ( ! [X2] :
        ( sK0 != X2
        | ~ m1_subset_1(sK8(X2,sK1,sK3),sK1)
        | ~ r2_hidden(X2,k2_relat_1(sK3)) )
    | ~ spl9_5
    | ~ spl9_127 ),
    inference(superposition,[],[f92,f1054])).

fof(f1054,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,sK8(X0,sK1,sK3)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl9_127 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f92,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f1055,plain,
    ( spl9_127
    | ~ spl9_81
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f933,f926,f659,f1053])).

fof(f926,plain,
    ( spl9_110
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK8(X0,X1,sK3)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f933,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK8(X0,sK1,sK3)) = X0 )
    | ~ spl9_81
    | ~ spl9_110 ),
    inference(superposition,[],[f927,f660])).

fof(f927,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK8(X0,X1,sK3)) = X0 )
    | ~ spl9_110 ),
    inference(avatar_component_clause,[],[f926])).

fof(f928,plain,
    ( spl9_110
    | ~ spl9_28
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f406,f399,f190,f926])).

fof(f190,plain,
    ( spl9_28
  <=> ! [X1,X0] :
        ( k1_funct_1(sK3,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f399,plain,
    ( spl9_62
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(k4_tarski(sK8(X0,X1,sK3),X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f406,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK8(X0,X1,sK3)) = X0 )
    | ~ spl9_28
    | ~ spl9_62 ),
    inference(resolution,[],[f400,f191])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f190])).

fof(f400,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK8(X0,X1,sK3),X0),sK3)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f399])).

fof(f803,plain,
    ( ~ spl9_24
    | ~ spl9_94 ),
    inference(avatar_contradiction_clause,[],[f796])).

fof(f796,plain,
    ( $false
    | ~ spl9_24
    | ~ spl9_94 ),
    inference(unit_resulting_resolution,[],[f174,f790])).

fof(f790,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(sK3))
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f789])).

fof(f789,plain,
    ( spl9_94
  <=> ! [X2] : ~ r2_hidden(X2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f791,plain,
    ( spl9_94
    | ~ spl9_29
    | ~ spl9_1
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f691,f569,f162,f75,f193,f789])).

fof(f193,plain,
    ( spl9_29
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f75,plain,
    ( spl9_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f162,plain,
    ( spl9_22
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK5(X0,X2),k1_relat_1(X0))
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f569,plain,
    ( spl9_76
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f691,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(X2,k2_relat_1(sK3)) )
    | ~ spl9_1
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(subsumption_resolution,[],[f685,f76])).

fof(f76,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f685,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X2,k2_relat_1(sK3)) )
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(resolution,[],[f570,f163])).

fof(f163,plain,
    ( ! [X2,X0] :
        ( r2_hidden(sK5(X0,X2),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f162])).

fof(f570,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ spl9_76 ),
    inference(avatar_component_clause,[],[f569])).

fof(f661,plain,
    ( spl9_81
    | ~ spl9_77
    | ~ spl9_79 ),
    inference(avatar_split_clause,[],[f646,f621,f573,f659])).

fof(f573,plain,
    ( spl9_77
  <=> k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f621,plain,
    ( spl9_79
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f646,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK1)
    | ~ spl9_77
    | ~ spl9_79 ),
    inference(forward_demodulation,[],[f574,f622])).

fof(f622,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl9_79 ),
    inference(avatar_component_clause,[],[f621])).

fof(f574,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl9_77 ),
    inference(avatar_component_clause,[],[f573])).

fof(f623,plain,
    ( spl9_79
    | ~ spl9_3
    | ~ spl9_17
    | ~ spl9_77 ),
    inference(avatar_split_clause,[],[f605,f573,f142,f83,f621])).

fof(f83,plain,
    ( spl9_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f142,plain,
    ( spl9_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f605,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl9_3
    | ~ spl9_17
    | ~ spl9_77 ),
    inference(backward_demodulation,[],[f574,f601])).

fof(f601,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK1)
    | ~ spl9_3
    | ~ spl9_17
    | ~ spl9_77 ),
    inference(subsumption_resolution,[],[f599,f84])).

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f599,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl9_17
    | ~ spl9_77 ),
    inference(superposition,[],[f574,f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f575,plain,
    ( spl9_77
    | ~ spl9_47
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f557,f533,f295,f573])).

fof(f295,plain,
    ( spl9_47
  <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f533,plain,
    ( spl9_74
  <=> k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) = k9_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f557,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl9_47
    | ~ spl9_74 ),
    inference(backward_demodulation,[],[f296,f534])).

fof(f534,plain,
    ( k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) = k9_relat_1(sK3,sK1)
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f533])).

fof(f296,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2))
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f295])).

fof(f571,plain,
    ( spl9_76
    | ~ spl9_12
    | ~ spl9_67
    | ~ spl9_73 ),
    inference(avatar_split_clause,[],[f556,f508,f434,f120,f569])).

fof(f120,plain,
    ( spl9_12
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f434,plain,
    ( spl9_67
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f508,plain,
    ( spl9_73
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f556,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ spl9_12
    | ~ spl9_67
    | ~ spl9_73 ),
    inference(subsumption_resolution,[],[f547,f121])).

fof(f121,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f547,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl9_67
    | ~ spl9_73 ),
    inference(resolution,[],[f509,f435])).

fof(f435,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl9_67 ),
    inference(avatar_component_clause,[],[f434])).

fof(f509,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl9_73 ),
    inference(avatar_component_clause,[],[f508])).

fof(f535,plain,
    ( spl9_74
    | ~ spl9_3
    | ~ spl9_25
    | ~ spl9_47
    | ~ spl9_69 ),
    inference(avatar_split_clause,[],[f525,f447,f295,f177,f83,f533])).

fof(f177,plain,
    ( spl9_25
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f447,plain,
    ( spl9_69
  <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f525,plain,
    ( k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) = k9_relat_1(sK3,sK1)
    | ~ spl9_3
    | ~ spl9_25
    | ~ spl9_47
    | ~ spl9_69 ),
    inference(backward_demodulation,[],[f296,f523])).

fof(f523,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl9_3
    | ~ spl9_25
    | ~ spl9_69 ),
    inference(subsumption_resolution,[],[f520,f84])).

fof(f520,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl9_25
    | ~ spl9_69 ),
    inference(superposition,[],[f448,f178])).

fof(f178,plain,
    ( ! [X2,X0,X3,X1] :
        ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f177])).

fof(f448,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl9_69 ),
    inference(avatar_component_clause,[],[f447])).

fof(f510,plain,
    ( spl9_73
    | ~ spl9_3
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f497,f444,f83,f508])).

fof(f444,plain,
    ( spl9_68
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f497,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl9_3
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f84,f445])).

fof(f445,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f444])).

fof(f449,plain,
    ( spl9_68
    | spl9_69
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_42
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f304,f295,f264,f83,f79,f75,f447,f444])).

fof(f79,plain,
    ( spl9_2
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f264,plain,
    ( spl9_42
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f304,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | k1_xboole_0 = sK2
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_42
    | ~ spl9_47 ),
    inference(subsumption_resolution,[],[f303,f76])).

fof(f303,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_42
    | ~ spl9_47 ),
    inference(subsumption_resolution,[],[f302,f84])).

fof(f302,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ spl9_2
    | ~ spl9_42
    | ~ spl9_47 ),
    inference(subsumption_resolution,[],[f299,f80])).

fof(f80,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f299,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ spl9_42
    | ~ spl9_47 ),
    inference(superposition,[],[f296,f265])).

fof(f265,plain,
    ( ! [X2,X0,X1] :
        ( k8_relset_1(X0,X1,X2,X1) = X0
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X2) )
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f264])).

fof(f436,plain,
    ( spl9_67
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f293,f287,f129,f434])).

fof(f129,plain,
    ( spl9_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f287,plain,
    ( spl9_46
  <=> ! [X1,X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ r2_hidden(X1,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f293,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(resolution,[],[f288,f130])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f288,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ r2_hidden(X1,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X1),X0) )
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f287])).

fof(f401,plain,
    ( spl9_62
    | ~ spl9_3
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f371,f368,f83,f399])).

fof(f368,plain,
    ( spl9_56
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f371,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(k4_tarski(sK8(X0,X1,sK3),X0),sK3) )
    | ~ spl9_3
    | ~ spl9_56 ),
    inference(resolution,[],[f369,f84])).

fof(f369,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) )
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f368])).

fof(f386,plain,
    ( spl9_59
    | ~ spl9_3
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f358,f322,f83,f384])).

fof(f322,plain,
    ( spl9_50
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_hidden(sK8(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f358,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK8(X0,X1,sK3),X1) )
    | ~ spl9_3
    | ~ spl9_50 ),
    inference(resolution,[],[f323,f84])).

fof(f323,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | r2_hidden(sK8(X0,X1,X2),X1) )
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f322])).

fof(f370,plain,
    ( spl9_56
    | ~ spl9_11
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f203,f169,f116,f368])).

fof(f116,plain,
    ( spl9_11
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f169,plain,
    ( spl9_23
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f203,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl9_11
    | ~ spl9_23 ),
    inference(resolution,[],[f170,f117])).

% (9589)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f169])).

fof(f324,plain,
    ( spl9_50
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f165,f138,f116,f322])).

fof(f138,plain,
    ( spl9_16
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK8(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f165,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(sK8(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(resolution,[],[f139,f117])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK8(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f297,plain,
    ( spl9_47
    | ~ spl9_3
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f251,f232,f83,f295])).

fof(f232,plain,
    ( spl9_36
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f251,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2))
    | ~ spl9_3
    | ~ spl9_36 ),
    inference(resolution,[],[f233,f84])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f232])).

fof(f289,plain,
    ( ~ spl9_29
    | spl9_46
    | ~ spl9_1
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f210,f200,f75,f287,f193])).

fof(f200,plain,
    ( spl9_30
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | r2_hidden(k1_funct_1(X1,X2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X1,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X1),X0) )
    | ~ spl9_1
    | ~ spl9_30 ),
    inference(resolution,[],[f201,f76])).

fof(f201,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | r2_hidden(k1_funct_1(X1,X2),X0) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f200])).

fof(f266,plain,(
    spl9_42 ),
    inference(avatar_split_clause,[],[f65,f264])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f234,plain,(
    spl9_36 ),
    inference(avatar_split_clause,[],[f60,f232])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f202,plain,(
    spl9_30 ),
    inference(avatar_split_clause,[],[f50,f200])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f198,plain,
    ( ~ spl9_3
    | ~ spl9_11
    | spl9_29 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_11
    | spl9_29 ),
    inference(unit_resulting_resolution,[],[f84,f194,f117])).

fof(f194,plain,
    ( ~ v1_relat_1(sK3)
    | spl9_29 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( spl9_28
    | ~ spl9_29
    | ~ spl9_1
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f188,f154,f75,f193,f190])).

fof(f154,plain,
    ( spl9_20
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_funct_1(X2,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) )
    | ~ spl9_1
    | ~ spl9_20 ),
    inference(resolution,[],[f155,f76])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | k1_funct_1(X2,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f154])).

fof(f179,plain,(
    spl9_25 ),
    inference(avatar_split_clause,[],[f67,f177])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f175,plain,
    ( spl9_24
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f167,f142,f87,f83,f173])).

fof(f87,plain,
    ( spl9_4
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f167,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f166,f84])).

fof(f166,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl9_4
    | ~ spl9_17 ),
    inference(superposition,[],[f88,f143])).

fof(f88,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f171,plain,(
    spl9_23 ),
    inference(avatar_split_clause,[],[f53,f169])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f164,plain,(
    spl9_22 ),
    inference(avatar_split_clause,[],[f71,f162])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f156,plain,(
    spl9_20 ),
    inference(avatar_split_clause,[],[f63,f154])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f144,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f57,f142])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f140,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f54,f138])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f131,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f59,f129])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f122,plain,
    ( spl9_12
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f114,f111,f95,f120])).

fof(f95,plain,
    ( spl9_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f111,plain,
    ( spl9_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f114,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(resolution,[],[f112,f96])).

fof(f96,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f56,f116])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f113,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f109,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f49,f107])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f97,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f40,f95])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f93,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f35,f91])).

fof(f35,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | sK0 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f89,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f39,f87])).

fof(f39,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f37,f79])).

fof(f37,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (9576)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (9574)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (9574)Refutation not found, incomplete strategy% (9574)------------------------------
% 0.22/0.50  % (9574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9587)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (9574)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9574)Memory used [KB]: 10618
% 0.22/0.51  % (9574)Time elapsed: 0.073 s
% 0.22/0.51  % (9574)------------------------------
% 0.22/0.51  % (9574)------------------------------
% 0.22/0.52  % (9582)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.53  % (9591)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (9579)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.54  % (9575)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (9577)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.54  % (9583)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.54  % (9581)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.54  % (9583)Refutation not found, incomplete strategy% (9583)------------------------------
% 0.22/0.54  % (9583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9583)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9583)Memory used [KB]: 6140
% 0.22/0.54  % (9583)Time elapsed: 0.100 s
% 0.22/0.54  % (9583)------------------------------
% 0.22/0.54  % (9583)------------------------------
% 0.22/0.55  % (9588)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.55  % (9578)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (9573)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (9586)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.55  % (9585)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (9590)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.56  % (9584)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.56  % (9580)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.57/0.56  % (9593)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.57/0.57  % (9582)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f1142,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f97,f109,f113,f118,f122,f131,f140,f144,f156,f164,f171,f175,f179,f195,f198,f202,f234,f266,f289,f297,f324,f370,f386,f401,f436,f449,f510,f535,f571,f575,f623,f661,f791,f803,f928,f1055,f1100,f1114,f1134,f1141])).
% 1.57/0.57  fof(f1141,plain,(
% 1.57/0.57    ~spl9_24 | ~spl9_138),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f1140])).
% 1.57/0.57  fof(f1140,plain,(
% 1.57/0.57    $false | (~spl9_24 | ~spl9_138)),
% 1.57/0.57    inference(subsumption_resolution,[],[f1139,f174])).
% 1.57/0.57  fof(f174,plain,(
% 1.57/0.57    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl9_24),
% 1.57/0.57    inference(avatar_component_clause,[],[f173])).
% 1.57/0.57  fof(f173,plain,(
% 1.57/0.57    spl9_24 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 1.57/0.57  fof(f1139,plain,(
% 1.57/0.57    ~r2_hidden(sK0,k2_relat_1(sK3)) | ~spl9_138),
% 1.57/0.57    inference(equality_resolution,[],[f1133])).
% 1.57/0.57  fof(f1133,plain,(
% 1.57/0.57    ( ! [X0] : (sK0 != X0 | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl9_138),
% 1.57/0.57    inference(avatar_component_clause,[],[f1132])).
% 1.57/0.57  fof(f1132,plain,(
% 1.57/0.57    spl9_138 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | sK0 != X0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).
% 1.57/0.57  fof(f1134,plain,(
% 1.57/0.57    spl9_138 | ~spl9_59 | ~spl9_81 | ~spl9_136),
% 1.57/0.57    inference(avatar_split_clause,[],[f1117,f1112,f659,f384,f1132])).
% 1.57/0.57  fof(f384,plain,(
% 1.57/0.57    spl9_59 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK8(X0,X1,sK3),X1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 1.57/0.57  fof(f659,plain,(
% 1.57/0.57    spl9_81 <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).
% 1.57/0.57  fof(f1112,plain,(
% 1.57/0.57    spl9_136 <=> ! [X0] : (sK0 != X0 | ~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(sK8(X0,sK1,sK3),sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).
% 1.57/0.57  fof(f1117,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | sK0 != X0) ) | (~spl9_59 | ~spl9_81 | ~spl9_136)),
% 1.57/0.57    inference(duplicate_literal_removal,[],[f1116])).
% 1.57/0.57  fof(f1116,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(X0,k2_relat_1(sK3)) | sK0 != X0) ) | (~spl9_59 | ~spl9_81 | ~spl9_136)),
% 1.57/0.57    inference(forward_demodulation,[],[f1115,f660])).
% 1.57/0.57  fof(f660,plain,(
% 1.57/0.57    k2_relat_1(sK3) = k9_relat_1(sK3,sK1) | ~spl9_81),
% 1.57/0.57    inference(avatar_component_clause,[],[f659])).
% 1.57/0.57  fof(f1115,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | sK0 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK1))) ) | (~spl9_59 | ~spl9_136)),
% 1.57/0.57    inference(resolution,[],[f1113,f385])).
% 1.57/0.57  fof(f385,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1,sK3),X1) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl9_59),
% 1.57/0.57    inference(avatar_component_clause,[],[f384])).
% 1.57/0.57  fof(f1113,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(sK8(X0,sK1,sK3),sK1) | ~r2_hidden(X0,k2_relat_1(sK3)) | sK0 != X0) ) | ~spl9_136),
% 1.57/0.57    inference(avatar_component_clause,[],[f1112])).
% 1.57/0.57  fof(f1114,plain,(
% 1.57/0.57    spl9_136 | ~spl9_9 | ~spl9_133),
% 1.57/0.57    inference(avatar_split_clause,[],[f1102,f1098,f107,f1112])).
% 1.57/0.57  fof(f107,plain,(
% 1.57/0.57    spl9_9 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.57/0.57  fof(f1098,plain,(
% 1.57/0.57    spl9_133 <=> ! [X2] : (sK0 != X2 | ~m1_subset_1(sK8(X2,sK1,sK3),sK1) | ~r2_hidden(X2,k2_relat_1(sK3)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).
% 1.57/0.57  fof(f1102,plain,(
% 1.57/0.57    ( ! [X0] : (sK0 != X0 | ~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(sK8(X0,sK1,sK3),sK1)) ) | (~spl9_9 | ~spl9_133)),
% 1.57/0.57    inference(resolution,[],[f1099,f108])).
% 1.57/0.57  fof(f108,plain,(
% 1.57/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl9_9),
% 1.57/0.57    inference(avatar_component_clause,[],[f107])).
% 1.57/0.57  fof(f1099,plain,(
% 1.57/0.57    ( ! [X2] : (~m1_subset_1(sK8(X2,sK1,sK3),sK1) | sK0 != X2 | ~r2_hidden(X2,k2_relat_1(sK3))) ) | ~spl9_133),
% 1.57/0.57    inference(avatar_component_clause,[],[f1098])).
% 1.57/0.57  fof(f1100,plain,(
% 1.57/0.57    spl9_133 | ~spl9_5 | ~spl9_127),
% 1.57/0.57    inference(avatar_split_clause,[],[f1062,f1053,f91,f1098])).
% 1.57/0.57  fof(f91,plain,(
% 1.57/0.57    spl9_5 <=> ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.57/0.57  fof(f1053,plain,(
% 1.57/0.57    spl9_127 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK8(X0,sK1,sK3)) = X0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).
% 1.57/0.57  fof(f1062,plain,(
% 1.57/0.57    ( ! [X2] : (sK0 != X2 | ~m1_subset_1(sK8(X2,sK1,sK3),sK1) | ~r2_hidden(X2,k2_relat_1(sK3))) ) | (~spl9_5 | ~spl9_127)),
% 1.57/0.57    inference(superposition,[],[f92,f1054])).
% 1.57/0.57  fof(f1054,plain,(
% 1.57/0.57    ( ! [X0] : (k1_funct_1(sK3,sK8(X0,sK1,sK3)) = X0 | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl9_127),
% 1.57/0.57    inference(avatar_component_clause,[],[f1053])).
% 1.57/0.57  fof(f92,plain,(
% 1.57/0.57    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) ) | ~spl9_5),
% 1.57/0.57    inference(avatar_component_clause,[],[f91])).
% 1.57/0.57  fof(f1055,plain,(
% 1.57/0.57    spl9_127 | ~spl9_81 | ~spl9_110),
% 1.57/0.57    inference(avatar_split_clause,[],[f933,f926,f659,f1053])).
% 1.57/0.57  fof(f926,plain,(
% 1.57/0.57    spl9_110 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK8(X0,X1,sK3)) = X0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).
% 1.57/0.57  fof(f933,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK8(X0,sK1,sK3)) = X0) ) | (~spl9_81 | ~spl9_110)),
% 1.57/0.57    inference(superposition,[],[f927,f660])).
% 1.57/0.57  fof(f927,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK8(X0,X1,sK3)) = X0) ) | ~spl9_110),
% 1.57/0.57    inference(avatar_component_clause,[],[f926])).
% 1.57/0.57  fof(f928,plain,(
% 1.57/0.57    spl9_110 | ~spl9_28 | ~spl9_62),
% 1.57/0.57    inference(avatar_split_clause,[],[f406,f399,f190,f926])).
% 1.57/0.57  fof(f190,plain,(
% 1.57/0.57    spl9_28 <=> ! [X1,X0] : (k1_funct_1(sK3,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK3))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 1.57/0.57  fof(f399,plain,(
% 1.57/0.57    spl9_62 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,sK3),X0),sK3))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 1.57/0.57  fof(f406,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK8(X0,X1,sK3)) = X0) ) | (~spl9_28 | ~spl9_62)),
% 1.57/0.57    inference(resolution,[],[f400,f191])).
% 1.57/0.57  fof(f191,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1) ) | ~spl9_28),
% 1.57/0.57    inference(avatar_component_clause,[],[f190])).
% 1.57/0.57  fof(f400,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,sK3),X0),sK3) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl9_62),
% 1.57/0.57    inference(avatar_component_clause,[],[f399])).
% 1.57/0.57  fof(f803,plain,(
% 1.57/0.57    ~spl9_24 | ~spl9_94),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f796])).
% 1.57/0.57  fof(f796,plain,(
% 1.57/0.57    $false | (~spl9_24 | ~spl9_94)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f174,f790])).
% 1.57/0.57  fof(f790,plain,(
% 1.57/0.57    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK3))) ) | ~spl9_94),
% 1.57/0.57    inference(avatar_component_clause,[],[f789])).
% 1.57/0.57  fof(f789,plain,(
% 1.57/0.57    spl9_94 <=> ! [X2] : ~r2_hidden(X2,k2_relat_1(sK3))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).
% 1.57/0.57  fof(f791,plain,(
% 1.57/0.57    spl9_94 | ~spl9_29 | ~spl9_1 | ~spl9_22 | ~spl9_76),
% 1.57/0.57    inference(avatar_split_clause,[],[f691,f569,f162,f75,f193,f789])).
% 1.57/0.57  fof(f193,plain,(
% 1.57/0.57    spl9_29 <=> v1_relat_1(sK3)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 1.57/0.57  fof(f75,plain,(
% 1.57/0.57    spl9_1 <=> v1_funct_1(sK3)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.57/0.57  fof(f162,plain,(
% 1.57/0.57    spl9_22 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 1.57/0.57  fof(f569,plain,(
% 1.57/0.57    spl9_76 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(sK3))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).
% 1.57/0.57  fof(f691,plain,(
% 1.57/0.57    ( ! [X2] : (~v1_relat_1(sK3) | ~r2_hidden(X2,k2_relat_1(sK3))) ) | (~spl9_1 | ~spl9_22 | ~spl9_76)),
% 1.57/0.57    inference(subsumption_resolution,[],[f685,f76])).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    v1_funct_1(sK3) | ~spl9_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f75])).
% 1.57/0.57  fof(f685,plain,(
% 1.57/0.57    ( ! [X2] : (~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X2,k2_relat_1(sK3))) ) | (~spl9_22 | ~spl9_76)),
% 1.57/0.57    inference(resolution,[],[f570,f163])).
% 1.57/0.57  fof(f163,plain,(
% 1.57/0.57    ( ! [X2,X0] : (r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) ) | ~spl9_22),
% 1.57/0.57    inference(avatar_component_clause,[],[f162])).
% 1.57/0.57  fof(f570,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl9_76),
% 1.57/0.57    inference(avatar_component_clause,[],[f569])).
% 1.57/0.57  fof(f661,plain,(
% 1.57/0.57    spl9_81 | ~spl9_77 | ~spl9_79),
% 1.57/0.57    inference(avatar_split_clause,[],[f646,f621,f573,f659])).
% 1.57/0.57  fof(f573,plain,(
% 1.57/0.57    spl9_77 <=> k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).
% 1.57/0.57  fof(f621,plain,(
% 1.57/0.57    spl9_79 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).
% 1.57/0.57  fof(f646,plain,(
% 1.57/0.57    k2_relat_1(sK3) = k9_relat_1(sK3,sK1) | (~spl9_77 | ~spl9_79)),
% 1.57/0.57    inference(forward_demodulation,[],[f574,f622])).
% 1.57/0.57  fof(f622,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl9_79),
% 1.57/0.57    inference(avatar_component_clause,[],[f621])).
% 1.57/0.57  fof(f574,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | ~spl9_77),
% 1.57/0.57    inference(avatar_component_clause,[],[f573])).
% 1.57/0.57  fof(f623,plain,(
% 1.57/0.57    spl9_79 | ~spl9_3 | ~spl9_17 | ~spl9_77),
% 1.57/0.57    inference(avatar_split_clause,[],[f605,f573,f142,f83,f621])).
% 1.57/0.57  fof(f83,plain,(
% 1.57/0.57    spl9_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.57/0.57  fof(f142,plain,(
% 1.57/0.57    spl9_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.57/0.57  fof(f605,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | (~spl9_3 | ~spl9_17 | ~spl9_77)),
% 1.57/0.57    inference(backward_demodulation,[],[f574,f601])).
% 1.57/0.57  fof(f601,plain,(
% 1.57/0.57    k2_relat_1(sK3) = k9_relat_1(sK3,sK1) | (~spl9_3 | ~spl9_17 | ~spl9_77)),
% 1.57/0.57    inference(subsumption_resolution,[],[f599,f84])).
% 1.57/0.57  fof(f84,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl9_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f83])).
% 1.57/0.57  fof(f599,plain,(
% 1.57/0.57    k2_relat_1(sK3) = k9_relat_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl9_17 | ~spl9_77)),
% 1.57/0.57    inference(superposition,[],[f574,f143])).
% 1.57/0.57  fof(f143,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_17),
% 1.57/0.57    inference(avatar_component_clause,[],[f142])).
% 1.57/0.57  fof(f575,plain,(
% 1.57/0.57    spl9_77 | ~spl9_47 | ~spl9_74),
% 1.57/0.57    inference(avatar_split_clause,[],[f557,f533,f295,f573])).
% 1.57/0.57  fof(f295,plain,(
% 1.57/0.57    spl9_47 <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 1.57/0.57  fof(f533,plain,(
% 1.57/0.57    spl9_74 <=> k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) = k9_relat_1(sK3,sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).
% 1.57/0.57  fof(f557,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | (~spl9_47 | ~spl9_74)),
% 1.57/0.57    inference(backward_demodulation,[],[f296,f534])).
% 1.57/0.57  fof(f534,plain,(
% 1.57/0.57    k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) = k9_relat_1(sK3,sK1) | ~spl9_74),
% 1.57/0.57    inference(avatar_component_clause,[],[f533])).
% 1.57/0.57  fof(f296,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) | ~spl9_47),
% 1.57/0.57    inference(avatar_component_clause,[],[f295])).
% 1.57/0.57  fof(f571,plain,(
% 1.57/0.57    spl9_76 | ~spl9_12 | ~spl9_67 | ~spl9_73),
% 1.57/0.57    inference(avatar_split_clause,[],[f556,f508,f434,f120,f569])).
% 1.57/0.57  fof(f120,plain,(
% 1.57/0.57    spl9_12 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.57/0.57  fof(f434,plain,(
% 1.57/0.57    spl9_67 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).
% 1.57/0.57  fof(f508,plain,(
% 1.57/0.57    spl9_73 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).
% 1.57/0.57  fof(f556,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3))) ) | (~spl9_12 | ~spl9_67 | ~spl9_73)),
% 1.57/0.57    inference(subsumption_resolution,[],[f547,f121])).
% 1.57/0.57  fof(f121,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl9_12),
% 1.57/0.57    inference(avatar_component_clause,[],[f120])).
% 1.57/0.57  fof(f547,plain,(
% 1.57/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | (~spl9_67 | ~spl9_73)),
% 1.57/0.57    inference(resolution,[],[f509,f435])).
% 1.57/0.57  fof(f435,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r2_hidden(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl9_67),
% 1.57/0.57    inference(avatar_component_clause,[],[f434])).
% 1.57/0.57  fof(f509,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl9_73),
% 1.57/0.57    inference(avatar_component_clause,[],[f508])).
% 1.57/0.57  fof(f535,plain,(
% 1.57/0.57    spl9_74 | ~spl9_3 | ~spl9_25 | ~spl9_47 | ~spl9_69),
% 1.57/0.57    inference(avatar_split_clause,[],[f525,f447,f295,f177,f83,f533])).
% 1.57/0.57  fof(f177,plain,(
% 1.57/0.57    spl9_25 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 1.57/0.57  fof(f447,plain,(
% 1.57/0.57    spl9_69 <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).
% 1.57/0.57  fof(f525,plain,(
% 1.57/0.57    k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) = k9_relat_1(sK3,sK1) | (~spl9_3 | ~spl9_25 | ~spl9_47 | ~spl9_69)),
% 1.57/0.57    inference(backward_demodulation,[],[f296,f523])).
% 1.57/0.57  fof(f523,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | (~spl9_3 | ~spl9_25 | ~spl9_69)),
% 1.57/0.57    inference(subsumption_resolution,[],[f520,f84])).
% 1.57/0.57  fof(f520,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl9_25 | ~spl9_69)),
% 1.57/0.57    inference(superposition,[],[f448,f178])).
% 1.57/0.57  fof(f178,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_25),
% 1.57/0.57    inference(avatar_component_clause,[],[f177])).
% 1.57/0.57  fof(f448,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl9_69),
% 1.57/0.57    inference(avatar_component_clause,[],[f447])).
% 1.57/0.57  fof(f510,plain,(
% 1.57/0.57    spl9_73 | ~spl9_3 | ~spl9_68),
% 1.57/0.57    inference(avatar_split_clause,[],[f497,f444,f83,f508])).
% 1.57/0.57  fof(f444,plain,(
% 1.57/0.57    spl9_68 <=> k1_xboole_0 = sK2),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).
% 1.57/0.57  fof(f497,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl9_3 | ~spl9_68)),
% 1.57/0.57    inference(backward_demodulation,[],[f84,f445])).
% 1.57/0.57  fof(f445,plain,(
% 1.57/0.57    k1_xboole_0 = sK2 | ~spl9_68),
% 1.57/0.57    inference(avatar_component_clause,[],[f444])).
% 1.57/0.57  fof(f449,plain,(
% 1.57/0.57    spl9_68 | spl9_69 | ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_42 | ~spl9_47),
% 1.57/0.57    inference(avatar_split_clause,[],[f304,f295,f264,f83,f79,f75,f447,f444])).
% 1.57/0.57  fof(f79,plain,(
% 1.57/0.57    spl9_2 <=> v1_funct_2(sK3,sK1,sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.57/0.57  fof(f264,plain,(
% 1.57/0.57    spl9_42 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 1.57/0.57  fof(f304,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | k1_xboole_0 = sK2 | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_42 | ~spl9_47)),
% 1.57/0.57    inference(subsumption_resolution,[],[f303,f76])).
% 1.57/0.57  fof(f303,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | (~spl9_2 | ~spl9_3 | ~spl9_42 | ~spl9_47)),
% 1.57/0.57    inference(subsumption_resolution,[],[f302,f84])).
% 1.57/0.57  fof(f302,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | (~spl9_2 | ~spl9_42 | ~spl9_47)),
% 1.57/0.57    inference(subsumption_resolution,[],[f299,f80])).
% 1.57/0.57  fof(f80,plain,(
% 1.57/0.57    v1_funct_2(sK3,sK1,sK2) | ~spl9_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f79])).
% 1.57/0.57  fof(f299,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | (~spl9_42 | ~spl9_47)),
% 1.57/0.57    inference(superposition,[],[f296,f265])).
% 1.57/0.57  fof(f265,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_1(X2)) ) | ~spl9_42),
% 1.57/0.57    inference(avatar_component_clause,[],[f264])).
% 1.57/0.57  fof(f436,plain,(
% 1.57/0.57    spl9_67 | ~spl9_14 | ~spl9_46),
% 1.57/0.57    inference(avatar_split_clause,[],[f293,f287,f129,f434])).
% 1.57/0.57  fof(f129,plain,(
% 1.57/0.57    spl9_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.57/0.57  fof(f287,plain,(
% 1.57/0.57    spl9_46 <=> ! [X1,X0] : (~v5_relat_1(sK3,X0) | ~r2_hidden(X1,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X1),X0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 1.57/0.57  fof(f293,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | (~spl9_14 | ~spl9_46)),
% 1.57/0.57    inference(resolution,[],[f288,f130])).
% 1.57/0.57  fof(f130,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_14),
% 1.57/0.57    inference(avatar_component_clause,[],[f129])).
% 1.57/0.57  fof(f288,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | ~r2_hidden(X1,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X1),X0)) ) | ~spl9_46),
% 1.57/0.57    inference(avatar_component_clause,[],[f287])).
% 1.57/0.57  fof(f401,plain,(
% 1.57/0.57    spl9_62 | ~spl9_3 | ~spl9_56),
% 1.57/0.57    inference(avatar_split_clause,[],[f371,f368,f83,f399])).
% 1.57/0.57  fof(f368,plain,(
% 1.57/0.57    spl9_56 <=> ! [X1,X3,X0,X2,X4] : (r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).
% 1.57/0.57  fof(f371,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,sK3),X0),sK3)) ) | (~spl9_3 | ~spl9_56)),
% 1.57/0.57    inference(resolution,[],[f369,f84])).
% 1.57/0.57  fof(f369,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)) ) | ~spl9_56),
% 1.57/0.57    inference(avatar_component_clause,[],[f368])).
% 1.57/0.57  fof(f386,plain,(
% 1.57/0.57    spl9_59 | ~spl9_3 | ~spl9_50),
% 1.57/0.57    inference(avatar_split_clause,[],[f358,f322,f83,f384])).
% 1.57/0.57  fof(f322,plain,(
% 1.57/0.57    spl9_50 <=> ! [X1,X3,X0,X2,X4] : (r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 1.57/0.57  fof(f358,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK8(X0,X1,sK3),X1)) ) | (~spl9_3 | ~spl9_50)),
% 1.57/0.57    inference(resolution,[],[f323,f84])).
% 1.57/0.57  fof(f323,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),X1)) ) | ~spl9_50),
% 1.57/0.57    inference(avatar_component_clause,[],[f322])).
% 1.57/0.57  fof(f370,plain,(
% 1.57/0.57    spl9_56 | ~spl9_11 | ~spl9_23),
% 1.57/0.57    inference(avatar_split_clause,[],[f203,f169,f116,f368])).
% 1.57/0.57  fof(f116,plain,(
% 1.57/0.57    spl9_11 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.57/0.57  fof(f169,plain,(
% 1.57/0.57    spl9_23 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 1.57/0.57  fof(f203,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | (~spl9_11 | ~spl9_23)),
% 1.57/0.57    inference(resolution,[],[f170,f117])).
% 1.57/0.57  % (9589)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.57/0.57  fof(f117,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_11),
% 1.57/0.57    inference(avatar_component_clause,[],[f116])).
% 1.57/0.57  fof(f170,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) ) | ~spl9_23),
% 1.57/0.57    inference(avatar_component_clause,[],[f169])).
% 1.57/0.57  fof(f324,plain,(
% 1.57/0.57    spl9_50 | ~spl9_11 | ~spl9_16),
% 1.57/0.57    inference(avatar_split_clause,[],[f165,f138,f116,f322])).
% 1.57/0.57  fof(f138,plain,(
% 1.57/0.57    spl9_16 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.57/0.57  fof(f165,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | (~spl9_11 | ~spl9_16)),
% 1.57/0.57    inference(resolution,[],[f139,f117])).
% 1.57/0.57  fof(f139,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) ) | ~spl9_16),
% 1.57/0.57    inference(avatar_component_clause,[],[f138])).
% 1.57/0.57  fof(f297,plain,(
% 1.57/0.57    spl9_47 | ~spl9_3 | ~spl9_36),
% 1.57/0.57    inference(avatar_split_clause,[],[f251,f232,f83,f295])).
% 1.57/0.57  fof(f232,plain,(
% 1.57/0.57    spl9_36 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 1.57/0.57  fof(f251,plain,(
% 1.57/0.57    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,k8_relset_1(sK1,sK2,sK3,sK2)) | (~spl9_3 | ~spl9_36)),
% 1.57/0.57    inference(resolution,[],[f233,f84])).
% 1.57/0.57  fof(f233,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) ) | ~spl9_36),
% 1.57/0.57    inference(avatar_component_clause,[],[f232])).
% 1.57/0.57  fof(f289,plain,(
% 1.57/0.57    ~spl9_29 | spl9_46 | ~spl9_1 | ~spl9_30),
% 1.57/0.57    inference(avatar_split_clause,[],[f210,f200,f75,f287,f193])).
% 1.57/0.57  fof(f200,plain,(
% 1.57/0.57    spl9_30 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.57/0.57  fof(f210,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3) | ~r2_hidden(X1,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X1),X0)) ) | (~spl9_1 | ~spl9_30)),
% 1.57/0.57    inference(resolution,[],[f201,f76])).
% 1.57/0.57  fof(f201,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0)) ) | ~spl9_30),
% 1.57/0.57    inference(avatar_component_clause,[],[f200])).
% 1.57/0.57  fof(f266,plain,(
% 1.57/0.57    spl9_42),
% 1.57/0.57    inference(avatar_split_clause,[],[f65,f264])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.57/0.57    inference(flattening,[],[f32])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.57/0.57    inference(ennf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 1.57/0.57  fof(f234,plain,(
% 1.57/0.57    spl9_36),
% 1.57/0.57    inference(avatar_split_clause,[],[f60,f232])).
% 1.57/0.57  fof(f60,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.57/0.57    inference(ennf_transformation,[],[f13])).
% 1.57/0.57  fof(f13,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 1.57/0.57  fof(f202,plain,(
% 1.57/0.57    spl9_30),
% 1.57/0.57    inference(avatar_split_clause,[],[f50,f200])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.57    inference(flattening,[],[f22])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.57/0.57  fof(f198,plain,(
% 1.57/0.57    ~spl9_3 | ~spl9_11 | spl9_29),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f196])).
% 1.57/0.57  fof(f196,plain,(
% 1.57/0.57    $false | (~spl9_3 | ~spl9_11 | spl9_29)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f84,f194,f117])).
% 1.57/0.57  fof(f194,plain,(
% 1.57/0.57    ~v1_relat_1(sK3) | spl9_29),
% 1.57/0.57    inference(avatar_component_clause,[],[f193])).
% 1.57/0.57  fof(f195,plain,(
% 1.57/0.57    spl9_28 | ~spl9_29 | ~spl9_1 | ~spl9_20),
% 1.57/0.57    inference(avatar_split_clause,[],[f188,f154,f75,f193,f190])).
% 1.57/0.57  fof(f154,plain,(
% 1.57/0.57    spl9_20 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.57/0.57  fof(f188,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK3)) ) | (~spl9_1 | ~spl9_20)),
% 1.57/0.57    inference(resolution,[],[f155,f76])).
% 1.57/0.57  fof(f155,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) ) | ~spl9_20),
% 1.57/0.57    inference(avatar_component_clause,[],[f154])).
% 1.57/0.57  fof(f179,plain,(
% 1.57/0.57    spl9_25),
% 1.57/0.57    inference(avatar_split_clause,[],[f67,f177])).
% 1.57/0.57  fof(f67,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f12])).
% 1.57/0.57  fof(f12,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.57/0.57  fof(f175,plain,(
% 1.57/0.57    spl9_24 | ~spl9_3 | ~spl9_4 | ~spl9_17),
% 1.57/0.57    inference(avatar_split_clause,[],[f167,f142,f87,f83,f173])).
% 1.57/0.57  fof(f87,plain,(
% 1.57/0.57    spl9_4 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.57/0.57  fof(f167,plain,(
% 1.57/0.57    r2_hidden(sK0,k2_relat_1(sK3)) | (~spl9_3 | ~spl9_4 | ~spl9_17)),
% 1.57/0.57    inference(subsumption_resolution,[],[f166,f84])).
% 1.57/0.57  fof(f166,plain,(
% 1.57/0.57    r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl9_4 | ~spl9_17)),
% 1.57/0.57    inference(superposition,[],[f88,f143])).
% 1.57/0.57  fof(f88,plain,(
% 1.57/0.57    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl9_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f87])).
% 1.57/0.57  fof(f171,plain,(
% 1.57/0.57    spl9_23),
% 1.57/0.57    inference(avatar_split_clause,[],[f53,f169])).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(ennf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.57/0.57  fof(f164,plain,(
% 1.57/0.57    spl9_22),
% 1.57/0.57    inference(avatar_split_clause,[],[f71,f162])).
% 1.57/0.57  fof(f71,plain,(
% 1.57/0.57    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.57/0.57    inference(equality_resolution,[],[f44])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.57/0.57    inference(cnf_transformation,[],[f20])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.57/0.57  fof(f156,plain,(
% 1.57/0.57    spl9_20),
% 1.57/0.57    inference(avatar_split_clause,[],[f63,f154])).
% 1.57/0.57  fof(f63,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f31])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(flattening,[],[f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.57/0.57    inference(ennf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.57/0.57  fof(f144,plain,(
% 1.57/0.57    spl9_17),
% 1.57/0.57    inference(avatar_split_clause,[],[f57,f142])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.57/0.57  fof(f140,plain,(
% 1.57/0.57    spl9_16),
% 1.57/0.57    inference(avatar_split_clause,[],[f54,f138])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f25])).
% 1.57/0.57  fof(f131,plain,(
% 1.57/0.57    spl9_14),
% 1.57/0.57    inference(avatar_split_clause,[],[f59,f129])).
% 1.57/0.57  fof(f59,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.57/0.57  fof(f122,plain,(
% 1.57/0.57    spl9_12 | ~spl9_6 | ~spl9_10),
% 1.57/0.57    inference(avatar_split_clause,[],[f114,f111,f95,f120])).
% 1.57/0.57  fof(f95,plain,(
% 1.57/0.57    spl9_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.57/0.57  fof(f111,plain,(
% 1.57/0.57    spl9_10 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.57/0.57  fof(f114,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl9_6 | ~spl9_10)),
% 1.57/0.57    inference(resolution,[],[f112,f96])).
% 1.57/0.57  fof(f96,plain,(
% 1.57/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl9_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f95])).
% 1.57/0.57  fof(f112,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) ) | ~spl9_10),
% 1.57/0.57    inference(avatar_component_clause,[],[f111])).
% 1.57/0.57  fof(f118,plain,(
% 1.57/0.57    spl9_11),
% 1.57/0.57    inference(avatar_split_clause,[],[f56,f116])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.57/0.57  fof(f113,plain,(
% 1.57/0.57    spl9_10),
% 1.57/0.57    inference(avatar_split_clause,[],[f51,f111])).
% 1.57/0.57  fof(f51,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.57/0.57  fof(f109,plain,(
% 1.57/0.57    spl9_9),
% 1.57/0.57    inference(avatar_split_clause,[],[f49,f107])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f21])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.57/0.57  fof(f97,plain,(
% 1.57/0.57    spl9_6),
% 1.57/0.57    inference(avatar_split_clause,[],[f40,f95])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.57/0.57  fof(f93,plain,(
% 1.57/0.57    spl9_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f35,f91])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ( ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f18,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 1.57/0.57    inference(flattening,[],[f17])).
% 1.57/0.57  fof(f17,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 1.57/0.57    inference(ennf_transformation,[],[f16])).
% 1.57/0.57  fof(f16,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.57/0.57    inference(negated_conjecture,[],[f15])).
% 1.57/0.57  fof(f15,conjecture,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 1.57/0.57  fof(f89,plain,(
% 1.57/0.57    spl9_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f39,f87])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f85,plain,(
% 1.57/0.57    spl9_3),
% 1.57/0.57    inference(avatar_split_clause,[],[f38,f83])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f81,plain,(
% 1.57/0.57    spl9_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f37,f79])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    v1_funct_2(sK3,sK1,sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f77,plain,(
% 1.57/0.57    spl9_1),
% 1.57/0.57    inference(avatar_split_clause,[],[f36,f75])).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    v1_funct_1(sK3)),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (9582)------------------------------
% 1.57/0.57  % (9582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (9582)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (9582)Memory used [KB]: 11385
% 1.57/0.57  % (9582)Time elapsed: 0.122 s
% 1.57/0.57  % (9582)------------------------------
% 1.57/0.57  % (9582)------------------------------
% 1.57/0.57  % (9584)Refutation not found, incomplete strategy% (9584)------------------------------
% 1.57/0.57  % (9584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (9584)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (9584)Memory used [KB]: 10746
% 1.57/0.57  % (9584)Time elapsed: 0.134 s
% 1.57/0.57  % (9584)------------------------------
% 1.57/0.57  % (9584)------------------------------
% 1.57/0.57  % (9572)Success in time 0.197 s
%------------------------------------------------------------------------------
