%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:25 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 362 expanded)
%              Number of leaves         :   51 ( 170 expanded)
%              Depth                    :    6
%              Number of atoms          :  635 (1154 expanded)
%              Number of equality atoms :   98 ( 202 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f961,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f93,f97,f101,f109,f113,f117,f137,f158,f208,f213,f217,f244,f248,f256,f260,f264,f278,f285,f292,f296,f304,f319,f329,f352,f360,f368,f383,f422,f429,f457,f459,f512,f530,f674,f695,f783,f808,f819,f859,f875,f948])).

fof(f948,plain,
    ( ~ spl8_36
    | ~ spl8_49
    | ~ spl8_62 ),
    inference(avatar_contradiction_clause,[],[f947])).

fof(f947,plain,
    ( $false
    | ~ spl8_36
    | ~ spl8_49
    | ~ spl8_62 ),
    inference(subsumption_resolution,[],[f910,f255])).

fof(f255,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl8_36
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f910,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0)
    | ~ spl8_49
    | ~ spl8_62 ),
    inference(backward_demodulation,[],[f328,f449])).

fof(f449,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl8_62
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f328,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl8_49
  <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f875,plain,
    ( ~ spl8_45
    | ~ spl8_95 ),
    inference(avatar_contradiction_clause,[],[f871])).

fof(f871,plain,
    ( $false
    | ~ spl8_45
    | ~ spl8_95 ),
    inference(unit_resulting_resolution,[],[f303,f858])).

fof(f858,plain,
    ( ! [X6,X7] : ~ r2_hidden(X6,k9_relat_1(sK3,X7))
    | ~ spl8_95 ),
    inference(avatar_component_clause,[],[f857])).

fof(f857,plain,
    ( spl8_95
  <=> ! [X7,X6] : ~ r2_hidden(X6,k9_relat_1(sK3,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).

fof(f303,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl8_45
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f859,plain,
    ( spl8_95
    | ~ spl8_42
    | ~ spl8_33
    | ~ spl8_36
    | ~ spl8_90 ),
    inference(avatar_split_clause,[],[f831,f817,f254,f242,f283,f857])).

fof(f283,plain,
    ( spl8_42
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f242,plain,
    ( spl8_33
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f817,plain,
    ( spl8_90
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f831,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(X6,k9_relat_1(sK3,X7)) )
    | ~ spl8_33
    | ~ spl8_36
    | ~ spl8_90 ),
    inference(subsumption_resolution,[],[f828,f255])).

fof(f828,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK6(X6,X7,sK3),k1_xboole_0)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X6,k9_relat_1(sK3,X7)) )
    | ~ spl8_33
    | ~ spl8_90 ),
    inference(superposition,[],[f243,f818])).

fof(f818,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl8_90 ),
    inference(avatar_component_clause,[],[f817])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f242])).

fof(f819,plain,
    ( spl8_90
    | ~ spl8_26
    | ~ spl8_84
    | ~ spl8_89 ),
    inference(avatar_split_clause,[],[f814,f806,f781,f211,f817])).

fof(f211,plain,
    ( spl8_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f781,plain,
    ( spl8_84
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f806,plain,
    ( spl8_89
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f814,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl8_26
    | ~ spl8_84
    | ~ spl8_89 ),
    inference(subsumption_resolution,[],[f809,f782])).

fof(f782,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_84 ),
    inference(avatar_component_clause,[],[f781])).

fof(f809,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_26
    | ~ spl8_89 ),
    inference(superposition,[],[f807,f212])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f807,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f806])).

fof(f808,plain,
    ( spl8_89
    | ~ spl8_40
    | ~ spl8_60
    | ~ spl8_63
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f779,f510,f451,f427,f276,f806])).

fof(f276,plain,
    ( spl8_40
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f427,plain,
    ( spl8_60
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f451,plain,
    ( spl8_63
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f510,plain,
    ( spl8_66
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f779,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_40
    | ~ spl8_60
    | ~ spl8_63
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f776,f709])).

fof(f709,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_60
    | ~ spl8_63 ),
    inference(backward_demodulation,[],[f428,f452])).

fof(f452,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f451])).

fof(f428,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f427])).

fof(f776,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_40
    | ~ spl8_66 ),
    inference(resolution,[],[f511,f277])).

fof(f277,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(X2,k1_xboole_0,X1)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f276])).

fof(f511,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f510])).

fof(f783,plain,
    ( spl8_84
    | ~ spl8_60
    | ~ spl8_63 ),
    inference(avatar_split_clause,[],[f709,f451,f427,f781])).

fof(f695,plain,
    ( ~ spl8_49
    | spl8_56
    | ~ spl8_82 ),
    inference(avatar_contradiction_clause,[],[f694])).

fof(f694,plain,
    ( $false
    | ~ spl8_49
    | spl8_56
    | ~ spl8_82 ),
    inference(subsumption_resolution,[],[f692,f382])).

fof(f382,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | spl8_56 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl8_56
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f692,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl8_49
    | ~ spl8_82 ),
    inference(resolution,[],[f673,f328])).

fof(f673,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | r2_hidden(X2,sK0) )
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f672])).

fof(f672,plain,
    ( spl8_82
  <=> ! [X3,X2] :
        ( r2_hidden(X2,sK0)
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f674,plain,
    ( ~ spl8_42
    | spl8_82
    | ~ spl8_1
    | ~ spl8_27
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f463,f455,f215,f87,f672,f283])).

fof(f87,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f215,plain,
    ( spl8_27
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f455,plain,
    ( spl8_64
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f463,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK0)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) )
    | ~ spl8_1
    | ~ spl8_27
    | ~ spl8_64 ),
    inference(subsumption_resolution,[],[f462,f88])).

fof(f88,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f462,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) )
    | ~ spl8_27
    | ~ spl8_64 ),
    inference(superposition,[],[f216,f456])).

fof(f456,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f455])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f215])).

fof(f530,plain,
    ( spl8_57
    | spl8_58
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f469,f358,f95,f91,f403,f400])).

fof(f400,plain,
    ( spl8_57
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f403,plain,
    ( spl8_58
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f91,plain,
    ( spl8_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f95,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f358,plain,
    ( spl8_53
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f469,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_53 ),
    inference(subsumption_resolution,[],[f436,f96])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f436,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2
    | ~ spl8_53 ),
    inference(resolution,[],[f92,f359])).

fof(f359,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f358])).

fof(f92,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f512,plain,
    ( spl8_66
    | ~ spl8_59
    | ~ spl8_63 ),
    inference(avatar_split_clause,[],[f482,f451,f420,f510])).

fof(f420,plain,
    ( spl8_59
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f482,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_59
    | ~ spl8_63 ),
    inference(backward_demodulation,[],[f421,f452])).

fof(f421,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f420])).

fof(f459,plain,
    ( ~ spl8_60
    | spl8_62
    | spl8_63
    | ~ spl8_44
    | ~ spl8_59 ),
    inference(avatar_split_clause,[],[f423,f420,f294,f451,f448,f427])).

fof(f294,plain,
    ( spl8_44
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f423,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_44
    | ~ spl8_59 ),
    inference(resolution,[],[f421,f295])).

fof(f295,plain,
    ( ! [X2,X0] :
        ( ~ v1_funct_2(X2,X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) )
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f294])).

fof(f457,plain,
    ( spl8_64
    | ~ spl8_3
    | ~ spl8_26
    | ~ spl8_57 ),
    inference(avatar_split_clause,[],[f445,f400,f211,f95,f455])).

fof(f445,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_3
    | ~ spl8_26
    | ~ spl8_57 ),
    inference(subsumption_resolution,[],[f441,f96])).

fof(f441,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_26
    | ~ spl8_57 ),
    inference(superposition,[],[f401,f212])).

fof(f401,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f400])).

fof(f429,plain,
    ( spl8_60
    | ~ spl8_3
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f407,f403,f95,f427])).

fof(f407,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_3
    | ~ spl8_58 ),
    inference(backward_demodulation,[],[f96,f404])).

fof(f404,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f403])).

fof(f422,plain,
    ( spl8_59
    | ~ spl8_2
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f406,f403,f91,f420])).

fof(f406,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_58 ),
    inference(backward_demodulation,[],[f92,f404])).

fof(f383,plain,
    ( ~ spl8_56
    | ~ spl8_8
    | spl8_54 ),
    inference(avatar_split_clause,[],[f375,f366,f115,f381])).

fof(f115,plain,
    ( spl8_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f366,plain,
    ( spl8_54
  <=> m1_subset_1(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f375,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl8_8
    | spl8_54 ),
    inference(resolution,[],[f367,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f367,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | spl8_54 ),
    inference(avatar_component_clause,[],[f366])).

fof(f368,plain,
    ( ~ spl8_54
    | ~ spl8_6
    | ~ spl8_48
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f363,f350,f317,f107,f366])).

fof(f107,plain,
    ( spl8_6
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK0)
        | ~ r2_hidden(X5,sK2)
        | sK4 != k1_funct_1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f317,plain,
    ( spl8_48
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f350,plain,
    ( spl8_51
  <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f363,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl8_6
    | ~ spl8_48
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f362,f318])).

fof(f318,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f317])).

fof(f362,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl8_6
    | ~ spl8_51 ),
    inference(trivial_inequality_removal,[],[f361])).

fof(f361,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl8_6
    | ~ spl8_51 ),
    inference(superposition,[],[f108,f351])).

fof(f351,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f350])).

fof(f108,plain,
    ( ! [X5] :
        ( sK4 != k1_funct_1(sK3,X5)
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f360,plain,(
    spl8_53 ),
    inference(avatar_split_clause,[],[f59,f358])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f352,plain,
    ( spl8_51
    | ~ spl8_41
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f344,f327,f280,f350])).

fof(f280,plain,
    ( spl8_41
  <=> ! [X1,X0] :
        ( k1_funct_1(sK3,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f344,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl8_41
    | ~ spl8_49 ),
    inference(resolution,[],[f328,f281])).

fof(f281,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 )
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f280])).

fof(f329,plain,
    ( ~ spl8_42
    | spl8_49
    | ~ spl8_37
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f310,f302,f258,f327,f283])).

fof(f258,plain,
    ( spl8_37
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f310,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_37
    | ~ spl8_45 ),
    inference(resolution,[],[f303,f259])).

fof(f259,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        | ~ v1_relat_1(X2) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f258])).

fof(f319,plain,
    ( ~ spl8_42
    | spl8_48
    | ~ spl8_25
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f311,f302,f206,f317,f283])).

fof(f206,plain,
    ( spl8_25
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK6(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f311,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl8_25
    | ~ spl8_45 ),
    inference(resolution,[],[f303,f207])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | r2_hidden(sK6(X0,X1,X2),X1)
        | ~ v1_relat_1(X2) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f304,plain,
    ( spl8_45
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f300,f262,f99,f95,f302])).

fof(f99,plain,
    ( spl8_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f262,plain,
    ( spl8_38
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f300,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f297,f96])).

fof(f297,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_4
    | ~ spl8_38 ),
    inference(superposition,[],[f100,f263])).

fof(f263,plain,
    ( ! [X2,X0,X3,X1] :
        ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f262])).

fof(f100,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f296,plain,(
    spl8_44 ),
    inference(avatar_split_clause,[],[f79,f294])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f292,plain,
    ( ~ spl8_3
    | ~ spl8_13
    | spl8_42 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_13
    | spl8_42 ),
    inference(unit_resulting_resolution,[],[f96,f284,f136])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_13
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f284,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_42 ),
    inference(avatar_component_clause,[],[f283])).

fof(f285,plain,
    ( spl8_41
    | ~ spl8_42
    | ~ spl8_1
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f273,f246,f87,f283,f280])).

fof(f246,plain,
    ( spl8_34
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_funct_1(X2,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) )
    | ~ spl8_1
    | ~ spl8_34 ),
    inference(resolution,[],[f247,f88])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | k1_funct_1(X2,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f246])).

fof(f278,plain,(
    spl8_40 ),
    inference(avatar_split_clause,[],[f77,f276])).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f264,plain,(
    spl8_38 ),
    inference(avatar_split_clause,[],[f74,f262])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f260,plain,(
    spl8_37 ),
    inference(avatar_split_clause,[],[f49,f258])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f256,plain,
    ( spl8_36
    | ~ spl8_7
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f181,f156,f111,f254])).

fof(f111,plain,
    ( spl8_7
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f156,plain,
    ( spl8_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f181,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_7
    | ~ spl8_18 ),
    inference(condensation,[],[f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl8_7
    | ~ spl8_18 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl8_7
    | ~ spl8_18 ),
    inference(superposition,[],[f157,f112])).

fof(f112,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X2) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f248,plain,(
    spl8_34 ),
    inference(avatar_split_clause,[],[f61,f246])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f244,plain,(
    spl8_33 ),
    inference(avatar_split_clause,[],[f48,f242])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f217,plain,(
    spl8_27 ),
    inference(avatar_split_clause,[],[f60,f215])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f213,plain,(
    spl8_26 ),
    inference(avatar_split_clause,[],[f53,f211])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f208,plain,(
    spl8_25 ),
    inference(avatar_split_clause,[],[f50,f206])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f158,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f70,f156])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f137,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f52,f135])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f117,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f42,f115])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f113,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f40,f111])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f109,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f34,f107])).

fof(f34,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f101,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f35,f99])).

fof(f35,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f38,f95])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f37,f91])).

fof(f37,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f36,f87])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20215)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (20217)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (20216)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (20219)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (20215)Refutation not found, incomplete strategy% (20215)------------------------------
% 0.20/0.48  % (20215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20215)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (20215)Memory used [KB]: 10618
% 0.20/0.48  % (20215)Time elapsed: 0.070 s
% 0.20/0.48  % (20215)------------------------------
% 0.20/0.48  % (20215)------------------------------
% 0.20/0.48  % (20229)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (20224)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (20235)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (20236)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (20220)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (20230)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (20221)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (20226)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (20236)Refutation not found, incomplete strategy% (20236)------------------------------
% 0.20/0.49  % (20236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20236)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (20236)Memory used [KB]: 10618
% 0.20/0.49  % (20236)Time elapsed: 0.088 s
% 0.20/0.49  % (20236)------------------------------
% 0.20/0.49  % (20236)------------------------------
% 0.20/0.50  % (20227)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (20222)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (20214)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (20228)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (20234)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (20223)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.25/0.51  % (20232)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.25/0.52  % (20231)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.25/0.52  % (20225)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.40/0.53  % (20224)Refutation found. Thanks to Tanya!
% 1.40/0.53  % SZS status Theorem for theBenchmark
% 1.40/0.53  % SZS output start Proof for theBenchmark
% 1.40/0.53  fof(f961,plain,(
% 1.40/0.53    $false),
% 1.40/0.53    inference(avatar_sat_refutation,[],[f89,f93,f97,f101,f109,f113,f117,f137,f158,f208,f213,f217,f244,f248,f256,f260,f264,f278,f285,f292,f296,f304,f319,f329,f352,f360,f368,f383,f422,f429,f457,f459,f512,f530,f674,f695,f783,f808,f819,f859,f875,f948])).
% 1.40/0.53  fof(f948,plain,(
% 1.40/0.53    ~spl8_36 | ~spl8_49 | ~spl8_62),
% 1.40/0.53    inference(avatar_contradiction_clause,[],[f947])).
% 1.40/0.53  fof(f947,plain,(
% 1.40/0.53    $false | (~spl8_36 | ~spl8_49 | ~spl8_62)),
% 1.40/0.53    inference(subsumption_resolution,[],[f910,f255])).
% 1.40/0.53  fof(f255,plain,(
% 1.40/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_36),
% 1.40/0.53    inference(avatar_component_clause,[],[f254])).
% 1.40/0.53  fof(f254,plain,(
% 1.40/0.53    spl8_36 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 1.40/0.53  fof(f910,plain,(
% 1.40/0.53    r2_hidden(k4_tarski(sK6(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0) | (~spl8_49 | ~spl8_62)),
% 1.40/0.53    inference(backward_demodulation,[],[f328,f449])).
% 1.40/0.53  fof(f449,plain,(
% 1.40/0.53    k1_xboole_0 = sK3 | ~spl8_62),
% 1.40/0.53    inference(avatar_component_clause,[],[f448])).
% 1.40/0.53  fof(f448,plain,(
% 1.40/0.53    spl8_62 <=> k1_xboole_0 = sK3),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 1.40/0.53  fof(f328,plain,(
% 1.40/0.53    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~spl8_49),
% 1.40/0.53    inference(avatar_component_clause,[],[f327])).
% 1.40/0.53  fof(f327,plain,(
% 1.40/0.53    spl8_49 <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 1.40/0.53  fof(f875,plain,(
% 1.40/0.53    ~spl8_45 | ~spl8_95),
% 1.40/0.53    inference(avatar_contradiction_clause,[],[f871])).
% 1.40/0.53  fof(f871,plain,(
% 1.40/0.53    $false | (~spl8_45 | ~spl8_95)),
% 1.40/0.53    inference(unit_resulting_resolution,[],[f303,f858])).
% 1.40/0.53  fof(f858,plain,(
% 1.40/0.53    ( ! [X6,X7] : (~r2_hidden(X6,k9_relat_1(sK3,X7))) ) | ~spl8_95),
% 1.40/0.53    inference(avatar_component_clause,[],[f857])).
% 1.40/0.53  fof(f857,plain,(
% 1.40/0.53    spl8_95 <=> ! [X7,X6] : ~r2_hidden(X6,k9_relat_1(sK3,X7))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).
% 1.40/0.53  fof(f303,plain,(
% 1.40/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_45),
% 1.40/0.53    inference(avatar_component_clause,[],[f302])).
% 1.40/0.53  fof(f302,plain,(
% 1.40/0.53    spl8_45 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 1.40/0.53  fof(f859,plain,(
% 1.40/0.53    spl8_95 | ~spl8_42 | ~spl8_33 | ~spl8_36 | ~spl8_90),
% 1.40/0.53    inference(avatar_split_clause,[],[f831,f817,f254,f242,f283,f857])).
% 1.40/0.53  fof(f283,plain,(
% 1.40/0.53    spl8_42 <=> v1_relat_1(sK3)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.40/0.53  fof(f242,plain,(
% 1.40/0.53    spl8_33 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.40/0.53  fof(f817,plain,(
% 1.40/0.53    spl8_90 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).
% 1.40/0.53  fof(f831,plain,(
% 1.40/0.53    ( ! [X6,X7] : (~v1_relat_1(sK3) | ~r2_hidden(X6,k9_relat_1(sK3,X7))) ) | (~spl8_33 | ~spl8_36 | ~spl8_90)),
% 1.40/0.53    inference(subsumption_resolution,[],[f828,f255])).
% 1.40/0.53  fof(f828,plain,(
% 1.40/0.53    ( ! [X6,X7] : (r2_hidden(sK6(X6,X7,sK3),k1_xboole_0) | ~v1_relat_1(sK3) | ~r2_hidden(X6,k9_relat_1(sK3,X7))) ) | (~spl8_33 | ~spl8_90)),
% 1.40/0.53    inference(superposition,[],[f243,f818])).
% 1.40/0.53  fof(f818,plain,(
% 1.40/0.53    k1_xboole_0 = k1_relat_1(sK3) | ~spl8_90),
% 1.40/0.53    inference(avatar_component_clause,[],[f817])).
% 1.40/0.53  fof(f243,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) ) | ~spl8_33),
% 1.40/0.53    inference(avatar_component_clause,[],[f242])).
% 1.40/0.53  fof(f819,plain,(
% 1.40/0.53    spl8_90 | ~spl8_26 | ~spl8_84 | ~spl8_89),
% 1.40/0.53    inference(avatar_split_clause,[],[f814,f806,f781,f211,f817])).
% 1.40/0.53  fof(f211,plain,(
% 1.40/0.53    spl8_26 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.40/0.53  fof(f781,plain,(
% 1.40/0.53    spl8_84 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).
% 1.40/0.53  fof(f806,plain,(
% 1.40/0.53    spl8_89 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).
% 1.40/0.53  fof(f814,plain,(
% 1.40/0.53    k1_xboole_0 = k1_relat_1(sK3) | (~spl8_26 | ~spl8_84 | ~spl8_89)),
% 1.40/0.53    inference(subsumption_resolution,[],[f809,f782])).
% 1.40/0.53  fof(f782,plain,(
% 1.40/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl8_84),
% 1.40/0.53    inference(avatar_component_clause,[],[f781])).
% 1.40/0.53  fof(f809,plain,(
% 1.40/0.53    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_26 | ~spl8_89)),
% 1.40/0.53    inference(superposition,[],[f807,f212])).
% 1.40/0.53  fof(f212,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_26),
% 1.40/0.53    inference(avatar_component_clause,[],[f211])).
% 1.40/0.53  fof(f807,plain,(
% 1.40/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl8_89),
% 1.40/0.53    inference(avatar_component_clause,[],[f806])).
% 1.40/0.53  fof(f808,plain,(
% 1.40/0.53    spl8_89 | ~spl8_40 | ~spl8_60 | ~spl8_63 | ~spl8_66),
% 1.40/0.53    inference(avatar_split_clause,[],[f779,f510,f451,f427,f276,f806])).
% 1.40/0.53  fof(f276,plain,(
% 1.40/0.53    spl8_40 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 1.40/0.53  fof(f427,plain,(
% 1.40/0.53    spl8_60 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 1.40/0.53  fof(f451,plain,(
% 1.40/0.53    spl8_63 <=> k1_xboole_0 = sK0),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).
% 1.40/0.53  fof(f510,plain,(
% 1.40/0.53    spl8_66 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).
% 1.40/0.53  fof(f779,plain,(
% 1.40/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl8_40 | ~spl8_60 | ~spl8_63 | ~spl8_66)),
% 1.40/0.53    inference(subsumption_resolution,[],[f776,f709])).
% 1.40/0.53  fof(f709,plain,(
% 1.40/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_60 | ~spl8_63)),
% 1.40/0.53    inference(backward_demodulation,[],[f428,f452])).
% 1.40/0.53  fof(f452,plain,(
% 1.40/0.53    k1_xboole_0 = sK0 | ~spl8_63),
% 1.40/0.53    inference(avatar_component_clause,[],[f451])).
% 1.40/0.53  fof(f428,plain,(
% 1.40/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_60),
% 1.40/0.53    inference(avatar_component_clause,[],[f427])).
% 1.40/0.53  fof(f776,plain,(
% 1.40/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_40 | ~spl8_66)),
% 1.40/0.53    inference(resolution,[],[f511,f277])).
% 1.40/0.53  fof(f277,plain,(
% 1.40/0.53    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl8_40),
% 1.40/0.53    inference(avatar_component_clause,[],[f276])).
% 1.40/0.53  fof(f511,plain,(
% 1.40/0.53    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl8_66),
% 1.40/0.53    inference(avatar_component_clause,[],[f510])).
% 1.40/0.53  fof(f783,plain,(
% 1.40/0.53    spl8_84 | ~spl8_60 | ~spl8_63),
% 1.40/0.53    inference(avatar_split_clause,[],[f709,f451,f427,f781])).
% 1.40/0.53  fof(f695,plain,(
% 1.40/0.53    ~spl8_49 | spl8_56 | ~spl8_82),
% 1.40/0.53    inference(avatar_contradiction_clause,[],[f694])).
% 1.40/0.53  fof(f694,plain,(
% 1.40/0.53    $false | (~spl8_49 | spl8_56 | ~spl8_82)),
% 1.40/0.53    inference(subsumption_resolution,[],[f692,f382])).
% 1.40/0.53  fof(f382,plain,(
% 1.40/0.53    ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | spl8_56),
% 1.40/0.53    inference(avatar_component_clause,[],[f381])).
% 1.40/0.53  fof(f381,plain,(
% 1.40/0.53    spl8_56 <=> r2_hidden(sK6(sK4,sK2,sK3),sK0)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 1.40/0.53  fof(f692,plain,(
% 1.40/0.53    r2_hidden(sK6(sK4,sK2,sK3),sK0) | (~spl8_49 | ~spl8_82)),
% 1.40/0.53    inference(resolution,[],[f673,f328])).
% 1.40/0.53  fof(f673,plain,(
% 1.40/0.53    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | r2_hidden(X2,sK0)) ) | ~spl8_82),
% 1.40/0.53    inference(avatar_component_clause,[],[f672])).
% 1.40/0.53  fof(f672,plain,(
% 1.40/0.53    spl8_82 <=> ! [X3,X2] : (r2_hidden(X2,sK0) | ~r2_hidden(k4_tarski(X2,X3),sK3))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).
% 1.40/0.53  fof(f674,plain,(
% 1.40/0.53    ~spl8_42 | spl8_82 | ~spl8_1 | ~spl8_27 | ~spl8_64),
% 1.40/0.53    inference(avatar_split_clause,[],[f463,f455,f215,f87,f672,f283])).
% 1.40/0.53  fof(f87,plain,(
% 1.40/0.53    spl8_1 <=> v1_funct_1(sK3)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.40/0.53  fof(f215,plain,(
% 1.40/0.53    spl8_27 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.40/0.53  fof(f455,plain,(
% 1.40/0.53    spl8_64 <=> sK0 = k1_relat_1(sK3)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).
% 1.40/0.53  fof(f463,plain,(
% 1.40/0.53    ( ! [X2,X3] : (r2_hidden(X2,sK0) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(X2,X3),sK3)) ) | (~spl8_1 | ~spl8_27 | ~spl8_64)),
% 1.40/0.53    inference(subsumption_resolution,[],[f462,f88])).
% 1.40/0.53  fof(f88,plain,(
% 1.40/0.53    v1_funct_1(sK3) | ~spl8_1),
% 1.40/0.53    inference(avatar_component_clause,[],[f87])).
% 1.40/0.53  fof(f462,plain,(
% 1.40/0.53    ( ! [X2,X3] : (r2_hidden(X2,sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(X2,X3),sK3)) ) | (~spl8_27 | ~spl8_64)),
% 1.40/0.53    inference(superposition,[],[f216,f456])).
% 1.40/0.53  fof(f456,plain,(
% 1.40/0.53    sK0 = k1_relat_1(sK3) | ~spl8_64),
% 1.40/0.53    inference(avatar_component_clause,[],[f455])).
% 1.40/0.53  fof(f216,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2)) ) | ~spl8_27),
% 1.40/0.53    inference(avatar_component_clause,[],[f215])).
% 1.40/0.53  fof(f530,plain,(
% 1.40/0.53    spl8_57 | spl8_58 | ~spl8_2 | ~spl8_3 | ~spl8_53),
% 1.40/0.53    inference(avatar_split_clause,[],[f469,f358,f95,f91,f403,f400])).
% 1.40/0.53  fof(f400,plain,(
% 1.40/0.53    spl8_57 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 1.40/0.53  fof(f403,plain,(
% 1.40/0.53    spl8_58 <=> k1_xboole_0 = sK1),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 1.40/0.53  fof(f91,plain,(
% 1.40/0.53    spl8_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.40/0.53  fof(f95,plain,(
% 1.40/0.53    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.40/0.53  fof(f358,plain,(
% 1.40/0.53    spl8_53 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 1.40/0.53  fof(f469,plain,(
% 1.40/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl8_2 | ~spl8_3 | ~spl8_53)),
% 1.40/0.53    inference(subsumption_resolution,[],[f436,f96])).
% 1.40/0.53  fof(f96,plain,(
% 1.40/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 1.40/0.53    inference(avatar_component_clause,[],[f95])).
% 1.40/0.53  fof(f436,plain,(
% 1.40/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl8_2 | ~spl8_53)),
% 1.40/0.53    inference(resolution,[],[f92,f359])).
% 1.40/0.53  fof(f359,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_53),
% 1.40/0.53    inference(avatar_component_clause,[],[f358])).
% 1.40/0.53  fof(f92,plain,(
% 1.40/0.53    v1_funct_2(sK3,sK0,sK1) | ~spl8_2),
% 1.40/0.53    inference(avatar_component_clause,[],[f91])).
% 1.40/0.53  fof(f512,plain,(
% 1.40/0.53    spl8_66 | ~spl8_59 | ~spl8_63),
% 1.40/0.53    inference(avatar_split_clause,[],[f482,f451,f420,f510])).
% 1.40/0.53  fof(f420,plain,(
% 1.40/0.53    spl8_59 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 1.40/0.53  fof(f482,plain,(
% 1.40/0.53    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl8_59 | ~spl8_63)),
% 1.40/0.53    inference(backward_demodulation,[],[f421,f452])).
% 1.40/0.53  fof(f421,plain,(
% 1.40/0.53    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl8_59),
% 1.40/0.53    inference(avatar_component_clause,[],[f420])).
% 1.40/0.53  fof(f459,plain,(
% 1.40/0.53    ~spl8_60 | spl8_62 | spl8_63 | ~spl8_44 | ~spl8_59),
% 1.40/0.53    inference(avatar_split_clause,[],[f423,f420,f294,f451,f448,f427])).
% 1.40/0.53  fof(f294,plain,(
% 1.40/0.53    spl8_44 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 1.40/0.53  fof(f423,plain,(
% 1.40/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_44 | ~spl8_59)),
% 1.40/0.53    inference(resolution,[],[f421,f295])).
% 1.40/0.53  fof(f295,plain,(
% 1.40/0.53    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | ~spl8_44),
% 1.40/0.53    inference(avatar_component_clause,[],[f294])).
% 1.40/0.53  fof(f457,plain,(
% 1.40/0.53    spl8_64 | ~spl8_3 | ~spl8_26 | ~spl8_57),
% 1.40/0.53    inference(avatar_split_clause,[],[f445,f400,f211,f95,f455])).
% 1.40/0.53  fof(f445,plain,(
% 1.40/0.53    sK0 = k1_relat_1(sK3) | (~spl8_3 | ~spl8_26 | ~spl8_57)),
% 1.40/0.53    inference(subsumption_resolution,[],[f441,f96])).
% 1.40/0.53  fof(f441,plain,(
% 1.40/0.53    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl8_26 | ~spl8_57)),
% 1.40/0.53    inference(superposition,[],[f401,f212])).
% 1.40/0.53  fof(f401,plain,(
% 1.40/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_57),
% 1.40/0.53    inference(avatar_component_clause,[],[f400])).
% 1.40/0.53  fof(f429,plain,(
% 1.40/0.53    spl8_60 | ~spl8_3 | ~spl8_58),
% 1.40/0.53    inference(avatar_split_clause,[],[f407,f403,f95,f427])).
% 1.40/0.53  fof(f407,plain,(
% 1.40/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_3 | ~spl8_58)),
% 1.40/0.53    inference(backward_demodulation,[],[f96,f404])).
% 1.40/0.53  fof(f404,plain,(
% 1.40/0.53    k1_xboole_0 = sK1 | ~spl8_58),
% 1.40/0.53    inference(avatar_component_clause,[],[f403])).
% 1.40/0.53  fof(f422,plain,(
% 1.40/0.53    spl8_59 | ~spl8_2 | ~spl8_58),
% 1.40/0.53    inference(avatar_split_clause,[],[f406,f403,f91,f420])).
% 1.40/0.53  fof(f406,plain,(
% 1.40/0.53    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl8_2 | ~spl8_58)),
% 1.40/0.53    inference(backward_demodulation,[],[f92,f404])).
% 1.40/0.53  fof(f383,plain,(
% 1.40/0.53    ~spl8_56 | ~spl8_8 | spl8_54),
% 1.40/0.53    inference(avatar_split_clause,[],[f375,f366,f115,f381])).
% 1.40/0.53  fof(f115,plain,(
% 1.40/0.53    spl8_8 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.40/0.53  fof(f366,plain,(
% 1.40/0.53    spl8_54 <=> m1_subset_1(sK6(sK4,sK2,sK3),sK0)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 1.40/0.53  fof(f375,plain,(
% 1.40/0.53    ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | (~spl8_8 | spl8_54)),
% 1.40/0.53    inference(resolution,[],[f367,f116])).
% 1.40/0.53  fof(f116,plain,(
% 1.40/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl8_8),
% 1.40/0.53    inference(avatar_component_clause,[],[f115])).
% 1.40/0.53  fof(f367,plain,(
% 1.40/0.53    ~m1_subset_1(sK6(sK4,sK2,sK3),sK0) | spl8_54),
% 1.40/0.53    inference(avatar_component_clause,[],[f366])).
% 1.40/0.53  fof(f368,plain,(
% 1.40/0.53    ~spl8_54 | ~spl8_6 | ~spl8_48 | ~spl8_51),
% 1.40/0.53    inference(avatar_split_clause,[],[f363,f350,f317,f107,f366])).
% 1.40/0.53  fof(f107,plain,(
% 1.40/0.53    spl8_6 <=> ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.40/0.53  fof(f317,plain,(
% 1.40/0.53    spl8_48 <=> r2_hidden(sK6(sK4,sK2,sK3),sK2)),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.40/0.53  fof(f350,plain,(
% 1.40/0.53    spl8_51 <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 1.40/0.53  fof(f363,plain,(
% 1.40/0.53    ~m1_subset_1(sK6(sK4,sK2,sK3),sK0) | (~spl8_6 | ~spl8_48 | ~spl8_51)),
% 1.40/0.53    inference(subsumption_resolution,[],[f362,f318])).
% 1.40/0.53  fof(f318,plain,(
% 1.40/0.53    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~spl8_48),
% 1.40/0.53    inference(avatar_component_clause,[],[f317])).
% 1.40/0.53  fof(f362,plain,(
% 1.40/0.53    ~r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK4,sK2,sK3),sK0) | (~spl8_6 | ~spl8_51)),
% 1.40/0.53    inference(trivial_inequality_removal,[],[f361])).
% 1.40/0.53  fof(f361,plain,(
% 1.40/0.53    sK4 != sK4 | ~r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK4,sK2,sK3),sK0) | (~spl8_6 | ~spl8_51)),
% 1.40/0.53    inference(superposition,[],[f108,f351])).
% 1.40/0.53  fof(f351,plain,(
% 1.40/0.53    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~spl8_51),
% 1.40/0.53    inference(avatar_component_clause,[],[f350])).
% 1.40/0.53  fof(f108,plain,(
% 1.40/0.53    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) ) | ~spl8_6),
% 1.40/0.53    inference(avatar_component_clause,[],[f107])).
% 1.40/0.53  fof(f360,plain,(
% 1.40/0.53    spl8_53),
% 1.40/0.53    inference(avatar_split_clause,[],[f59,f358])).
% 1.40/0.53  fof(f59,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f28])).
% 1.40/0.53  fof(f28,plain,(
% 1.40/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.53    inference(flattening,[],[f27])).
% 1.40/0.53  fof(f27,plain,(
% 1.40/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.53    inference(ennf_transformation,[],[f15])).
% 1.40/0.53  fof(f15,axiom,(
% 1.40/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.40/0.53  fof(f352,plain,(
% 1.40/0.53    spl8_51 | ~spl8_41 | ~spl8_49),
% 1.40/0.53    inference(avatar_split_clause,[],[f344,f327,f280,f350])).
% 1.40/0.53  fof(f280,plain,(
% 1.40/0.53    spl8_41 <=> ! [X1,X0] : (k1_funct_1(sK3,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK3))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 1.40/0.53  fof(f344,plain,(
% 1.40/0.53    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | (~spl8_41 | ~spl8_49)),
% 1.40/0.53    inference(resolution,[],[f328,f281])).
% 1.40/0.53  fof(f281,plain,(
% 1.40/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1) ) | ~spl8_41),
% 1.40/0.53    inference(avatar_component_clause,[],[f280])).
% 1.40/0.53  fof(f329,plain,(
% 1.40/0.53    ~spl8_42 | spl8_49 | ~spl8_37 | ~spl8_45),
% 1.40/0.53    inference(avatar_split_clause,[],[f310,f302,f258,f327,f283])).
% 1.40/0.53  fof(f258,plain,(
% 1.40/0.53    spl8_37 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 1.40/0.53  fof(f310,plain,(
% 1.40/0.53    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | (~spl8_37 | ~spl8_45)),
% 1.40/0.53    inference(resolution,[],[f303,f259])).
% 1.40/0.53  fof(f259,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) ) | ~spl8_37),
% 1.40/0.53    inference(avatar_component_clause,[],[f258])).
% 1.40/0.53  fof(f319,plain,(
% 1.40/0.53    ~spl8_42 | spl8_48 | ~spl8_25 | ~spl8_45),
% 1.40/0.53    inference(avatar_split_clause,[],[f311,f302,f206,f317,f283])).
% 1.40/0.53  fof(f206,plain,(
% 1.40/0.53    spl8_25 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.40/0.53  fof(f311,plain,(
% 1.40/0.53    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | (~spl8_25 | ~spl8_45)),
% 1.40/0.53    inference(resolution,[],[f303,f207])).
% 1.40/0.53  fof(f207,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) ) | ~spl8_25),
% 1.40/0.53    inference(avatar_component_clause,[],[f206])).
% 1.40/0.53  fof(f304,plain,(
% 1.40/0.53    spl8_45 | ~spl8_3 | ~spl8_4 | ~spl8_38),
% 1.40/0.53    inference(avatar_split_clause,[],[f300,f262,f99,f95,f302])).
% 1.40/0.53  fof(f99,plain,(
% 1.40/0.53    spl8_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.40/0.53  fof(f262,plain,(
% 1.40/0.53    spl8_38 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.40/0.53  fof(f300,plain,(
% 1.40/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_3 | ~spl8_4 | ~spl8_38)),
% 1.40/0.53    inference(subsumption_resolution,[],[f297,f96])).
% 1.40/0.53  fof(f297,plain,(
% 1.40/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl8_4 | ~spl8_38)),
% 1.40/0.53    inference(superposition,[],[f100,f263])).
% 1.40/0.53  fof(f263,plain,(
% 1.40/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_38),
% 1.40/0.53    inference(avatar_component_clause,[],[f262])).
% 1.40/0.53  fof(f100,plain,(
% 1.40/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_4),
% 1.40/0.53    inference(avatar_component_clause,[],[f99])).
% 1.40/0.53  fof(f296,plain,(
% 1.40/0.53    spl8_44),
% 1.40/0.53    inference(avatar_split_clause,[],[f79,f294])).
% 1.40/0.53  fof(f79,plain,(
% 1.40/0.53    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.40/0.53    inference(equality_resolution,[],[f55])).
% 1.40/0.53  fof(f55,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f28])).
% 1.40/0.53  fof(f292,plain,(
% 1.40/0.53    ~spl8_3 | ~spl8_13 | spl8_42),
% 1.40/0.53    inference(avatar_contradiction_clause,[],[f290])).
% 1.40/0.53  fof(f290,plain,(
% 1.40/0.53    $false | (~spl8_3 | ~spl8_13 | spl8_42)),
% 1.40/0.53    inference(unit_resulting_resolution,[],[f96,f284,f136])).
% 1.40/0.53  fof(f136,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_13),
% 1.40/0.53    inference(avatar_component_clause,[],[f135])).
% 1.40/0.53  fof(f135,plain,(
% 1.40/0.53    spl8_13 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.40/0.53  fof(f284,plain,(
% 1.40/0.53    ~v1_relat_1(sK3) | spl8_42),
% 1.40/0.53    inference(avatar_component_clause,[],[f283])).
% 1.40/0.53  fof(f285,plain,(
% 1.40/0.53    spl8_41 | ~spl8_42 | ~spl8_1 | ~spl8_34),
% 1.40/0.53    inference(avatar_split_clause,[],[f273,f246,f87,f283,f280])).
% 1.40/0.53  fof(f246,plain,(
% 1.40/0.53    spl8_34 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 1.40/0.53  fof(f273,plain,(
% 1.40/0.53    ( ! [X0,X1] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK3)) ) | (~spl8_1 | ~spl8_34)),
% 1.40/0.53    inference(resolution,[],[f247,f88])).
% 1.40/0.53  fof(f247,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) ) | ~spl8_34),
% 1.40/0.53    inference(avatar_component_clause,[],[f246])).
% 1.40/0.53  fof(f278,plain,(
% 1.40/0.53    spl8_40),
% 1.40/0.53    inference(avatar_split_clause,[],[f77,f276])).
% 1.40/0.53  fof(f77,plain,(
% 1.40/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.40/0.53    inference(equality_resolution,[],[f57])).
% 1.40/0.53  fof(f57,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f28])).
% 1.40/0.53  fof(f264,plain,(
% 1.40/0.53    spl8_38),
% 1.40/0.53    inference(avatar_split_clause,[],[f74,f262])).
% 1.40/0.53  fof(f74,plain,(
% 1.40/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f33])).
% 1.40/0.53  fof(f33,plain,(
% 1.40/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.53    inference(ennf_transformation,[],[f14])).
% 1.40/0.53  fof(f14,axiom,(
% 1.40/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.40/0.53  fof(f260,plain,(
% 1.40/0.53    spl8_37),
% 1.40/0.53    inference(avatar_split_clause,[],[f49,f258])).
% 1.40/0.53  fof(f49,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.40/0.53    inference(cnf_transformation,[],[f24])).
% 1.40/0.53  fof(f24,plain,(
% 1.40/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.40/0.53    inference(ennf_transformation,[],[f9])).
% 1.40/0.53  fof(f9,axiom,(
% 1.40/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.40/0.53  fof(f256,plain,(
% 1.40/0.53    spl8_36 | ~spl8_7 | ~spl8_18),
% 1.40/0.53    inference(avatar_split_clause,[],[f181,f156,f111,f254])).
% 1.40/0.53  fof(f111,plain,(
% 1.40/0.53    spl8_7 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.40/0.53  fof(f156,plain,(
% 1.40/0.53    spl8_18 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2)))),
% 1.40/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.40/0.53  fof(f181,plain,(
% 1.40/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl8_7 | ~spl8_18)),
% 1.40/0.53    inference(condensation,[],[f180])).
% 1.40/0.53  fof(f180,plain,(
% 1.40/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) ) | (~spl8_7 | ~spl8_18)),
% 1.40/0.53    inference(duplicate_literal_removal,[],[f179])).
% 1.40/0.53  fof(f179,plain,(
% 1.40/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) ) | (~spl8_7 | ~spl8_18)),
% 1.40/0.53    inference(superposition,[],[f157,f112])).
% 1.40/0.53  fof(f112,plain,(
% 1.40/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl8_7),
% 1.40/0.53    inference(avatar_component_clause,[],[f111])).
% 1.40/0.53  fof(f157,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) ) | ~spl8_18),
% 1.40/0.53    inference(avatar_component_clause,[],[f156])).
% 1.40/0.53  fof(f248,plain,(
% 1.40/0.53    spl8_34),
% 1.40/0.53    inference(avatar_split_clause,[],[f61,f246])).
% 1.40/0.53  fof(f61,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f30])).
% 1.40/0.53  fof(f30,plain,(
% 1.40/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.40/0.53    inference(flattening,[],[f29])).
% 1.40/0.53  fof(f29,plain,(
% 1.40/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.40/0.53    inference(ennf_transformation,[],[f10])).
% 1.40/0.53  fof(f10,axiom,(
% 1.40/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.40/0.53  fof(f244,plain,(
% 1.40/0.53    spl8_33),
% 1.40/0.53    inference(avatar_split_clause,[],[f48,f242])).
% 1.40/0.53  fof(f48,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.40/0.53    inference(cnf_transformation,[],[f24])).
% 1.40/0.53  fof(f217,plain,(
% 1.40/0.53    spl8_27),
% 1.40/0.53    inference(avatar_split_clause,[],[f60,f215])).
% 1.40/0.53  fof(f60,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f30])).
% 1.40/0.53  fof(f213,plain,(
% 1.40/0.53    spl8_26),
% 1.40/0.53    inference(avatar_split_clause,[],[f53,f211])).
% 1.40/0.53  fof(f53,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f26])).
% 1.40/0.53  fof(f26,plain,(
% 1.40/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.53    inference(ennf_transformation,[],[f13])).
% 1.40/0.53  fof(f13,axiom,(
% 1.40/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.40/0.53  fof(f208,plain,(
% 1.40/0.53    spl8_25),
% 1.40/0.53    inference(avatar_split_clause,[],[f50,f206])).
% 1.40/0.53  fof(f50,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.40/0.53    inference(cnf_transformation,[],[f24])).
% 1.40/0.53  fof(f158,plain,(
% 1.40/0.53    spl8_18),
% 1.40/0.53    inference(avatar_split_clause,[],[f70,f156])).
% 1.40/0.53  fof(f70,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.40/0.53    inference(cnf_transformation,[],[f31])).
% 1.40/0.53  fof(f31,plain,(
% 1.40/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.40/0.53    inference(ennf_transformation,[],[f2])).
% 1.40/0.53  fof(f2,axiom,(
% 1.40/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.40/0.53  fof(f137,plain,(
% 1.40/0.53    spl8_13),
% 1.40/0.53    inference(avatar_split_clause,[],[f52,f135])).
% 1.40/0.53  fof(f52,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f25])).
% 1.40/0.53  fof(f25,plain,(
% 1.40/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.53    inference(ennf_transformation,[],[f11])).
% 1.40/0.53  fof(f11,axiom,(
% 1.40/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.40/0.53  fof(f117,plain,(
% 1.40/0.53    spl8_8),
% 1.40/0.53    inference(avatar_split_clause,[],[f42,f115])).
% 1.40/0.53  fof(f42,plain,(
% 1.40/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f21])).
% 1.40/0.53  fof(f21,plain,(
% 1.40/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.40/0.53    inference(ennf_transformation,[],[f7])).
% 1.40/0.53  fof(f7,axiom,(
% 1.40/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.40/0.53  fof(f113,plain,(
% 1.40/0.53    spl8_7),
% 1.40/0.53    inference(avatar_split_clause,[],[f40,f111])).
% 1.40/0.53  fof(f40,plain,(
% 1.40/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.40/0.53    inference(cnf_transformation,[],[f4])).
% 1.40/0.53  fof(f4,axiom,(
% 1.40/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.40/0.53  fof(f109,plain,(
% 1.40/0.53    spl8_6),
% 1.40/0.53    inference(avatar_split_clause,[],[f34,f107])).
% 1.40/0.53  fof(f34,plain,(
% 1.40/0.53    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f19])).
% 1.40/0.53  fof(f19,plain,(
% 1.40/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.40/0.53    inference(flattening,[],[f18])).
% 1.40/0.53  fof(f18,plain,(
% 1.40/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.40/0.53    inference(ennf_transformation,[],[f17])).
% 1.40/0.53  fof(f17,negated_conjecture,(
% 1.40/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.40/0.53    inference(negated_conjecture,[],[f16])).
% 1.40/0.53  fof(f16,conjecture,(
% 1.40/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 1.40/0.53  fof(f101,plain,(
% 1.40/0.53    spl8_4),
% 1.40/0.53    inference(avatar_split_clause,[],[f35,f99])).
% 1.40/0.53  fof(f35,plain,(
% 1.40/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.40/0.53    inference(cnf_transformation,[],[f19])).
% 1.40/0.53  fof(f97,plain,(
% 1.40/0.53    spl8_3),
% 1.40/0.53    inference(avatar_split_clause,[],[f38,f95])).
% 1.40/0.53  fof(f38,plain,(
% 1.40/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.40/0.53    inference(cnf_transformation,[],[f19])).
% 1.40/0.53  fof(f93,plain,(
% 1.40/0.53    spl8_2),
% 1.40/0.53    inference(avatar_split_clause,[],[f37,f91])).
% 1.40/0.53  fof(f37,plain,(
% 1.40/0.53    v1_funct_2(sK3,sK0,sK1)),
% 1.40/0.53    inference(cnf_transformation,[],[f19])).
% 1.40/0.53  fof(f89,plain,(
% 1.40/0.53    spl8_1),
% 1.40/0.53    inference(avatar_split_clause,[],[f36,f87])).
% 1.40/0.53  fof(f36,plain,(
% 1.40/0.53    v1_funct_1(sK3)),
% 1.40/0.53    inference(cnf_transformation,[],[f19])).
% 1.40/0.53  % SZS output end Proof for theBenchmark
% 1.40/0.53  % (20224)------------------------------
% 1.40/0.53  % (20224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.53  % (20224)Termination reason: Refutation
% 1.40/0.53  
% 1.40/0.53  % (20224)Memory used [KB]: 11129
% 1.40/0.53  % (20224)Time elapsed: 0.121 s
% 1.40/0.53  % (20224)------------------------------
% 1.40/0.53  % (20224)------------------------------
% 1.40/0.54  % (20212)Success in time 0.18 s
%------------------------------------------------------------------------------
