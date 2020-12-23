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
% DateTime   : Thu Dec  3 13:02:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 470 expanded)
%              Number of leaves         :   59 ( 217 expanded)
%              Depth                    :    9
%              Number of atoms          :  866 (1565 expanded)
%              Number of equality atoms :  152 ( 318 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f111,f119,f123,f127,f137,f141,f145,f153,f159,f163,f167,f170,f196,f200,f204,f208,f212,f216,f224,f245,f264,f298,f302,f307,f329,f355,f576,f638,f650,f654,f655,f913,f974,f999,f1004,f1021,f1028,f1041,f1107,f1136])).

fof(f1136,plain,
    ( ~ spl3_13
    | spl3_14
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_64 ),
    inference(avatar_contradiction_clause,[],[f1135])).

fof(f1135,plain,
    ( $false
    | ~ spl3_13
    | spl3_14
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f1134,f126])).

fof(f126,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_13
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1134,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_14
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_64 ),
    inference(forward_demodulation,[],[f1133,f1017])).

fof(f1017,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f1016])).

fof(f1016,plain,
    ( spl3_64
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f1133,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_14
    | ~ spl3_40
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f1132,f280])).

fof(f280,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl3_40
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f1132,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_14
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f130,f636])).

fof(f636,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl3_41
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f130,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_14
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1107,plain,
    ( spl3_15
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_64 ),
    inference(avatar_contradiction_clause,[],[f1106])).

fof(f1106,plain,
    ( $false
    | spl3_15
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f1105,f328])).

fof(f328,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl3_47
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f1105,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_15
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_64 ),
    inference(forward_demodulation,[],[f1079,f1017])).

fof(f1079,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_15
    | ~ spl3_40
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f1049,f280])).

fof(f1049,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_15
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f133,f636])).

fof(f133,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_15
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1041,plain,
    ( ~ spl3_14
    | ~ spl3_32
    | ~ spl3_37
    | spl3_63 ),
    inference(avatar_split_clause,[],[f1003,f997,f262,f214,f129])).

fof(f214,plain,
    ( spl3_32
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f262,plain,
    ( spl3_37
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f997,plain,
    ( spl3_63
  <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f1003,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_32
    | ~ spl3_37
    | spl3_63 ),
    inference(subsumption_resolution,[],[f1001,f263])).

fof(f263,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1001,plain,
    ( sK1 != k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_32
    | spl3_63 ),
    inference(superposition,[],[f998,f215])).

fof(f215,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f214])).

fof(f998,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | spl3_63 ),
    inference(avatar_component_clause,[],[f997])).

fof(f1028,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_17
    | spl3_65 ),
    inference(avatar_contradiction_clause,[],[f1027])).

fof(f1027,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_17
    | spl3_65 ),
    inference(subsumption_resolution,[],[f1026,f98])).

fof(f98,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1026,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_17
    | spl3_65 ),
    inference(subsumption_resolution,[],[f1023,f102])).

fof(f102,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1023,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_17
    | spl3_65 ),
    inference(resolution,[],[f1020,f140])).

fof(f140,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1020,plain,
    ( ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | spl3_65 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f1019,plain,
    ( spl3_65
  <=> v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f1021,plain,
    ( spl3_64
    | ~ spl3_65
    | ~ spl3_22
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f979,f972,f161,f1019,f1016])).

fof(f161,plain,
    ( spl3_22
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f972,plain,
    ( spl3_61
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f979,plain,
    ( ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_22
    | ~ spl3_61 ),
    inference(trivial_inequality_removal,[],[f978])).

fof(f978,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_22
    | ~ spl3_61 ),
    inference(superposition,[],[f162,f973])).

fof(f973,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f972])).

fof(f162,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1004,plain,
    ( spl3_54
    | ~ spl3_3
    | ~ spl3_4
    | spl3_41
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f923,f353,f282,f89,f85,f487])).

fof(f487,plain,
    ( spl3_54
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f85,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f89,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f353,plain,
    ( spl3_52
  <=> ! [X3,X5,X4] :
        ( k1_relat_1(X5) = X3
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(X5,X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f923,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_4
    | spl3_41
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f657,f283])).

fof(f283,plain,
    ( k1_xboole_0 != sK1
    | spl3_41 ),
    inference(avatar_component_clause,[],[f282])).

fof(f657,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f598,f86])).

fof(f86,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f598,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_4
    | ~ spl3_52 ),
    inference(resolution,[],[f90,f354])).

fof(f354,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_xboole_0 = X4
        | k1_relat_1(X5) = X3
        | ~ v1_funct_2(X5,X3,X4) )
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f353])).

fof(f90,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f999,plain,
    ( ~ spl3_14
    | ~ spl3_63
    | spl3_15
    | ~ spl3_43
    | spl3_57 ),
    inference(avatar_split_clause,[],[f943,f640,f296,f132,f997,f129])).

fof(f296,plain,
    ( spl3_43
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) != X0
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f640,plain,
    ( spl3_57
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f943,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_15
    | ~ spl3_43
    | spl3_57 ),
    inference(subsumption_resolution,[],[f303,f641])).

fof(f641,plain,
    ( k1_xboole_0 != sK0
    | spl3_57 ),
    inference(avatar_component_clause,[],[f640])).

fof(f303,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_15
    | ~ spl3_43 ),
    inference(resolution,[],[f297,f133])).

fof(f297,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) != X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f296])).

fof(f974,plain,
    ( spl3_61
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f757,f574,f198,f121,f101,f97,f972])).

fof(f121,plain,
    ( spl3_12
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f198,plain,
    ( spl3_28
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f574,plain,
    ( spl3_55
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f757,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f742,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f742,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f741,f98])).

fof(f741,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_7
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f737,f102])).

fof(f737,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(resolution,[],[f575,f199])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f198])).

fof(f575,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f574])).

fof(f913,plain,
    ( ~ spl3_11
    | ~ spl3_37
    | spl3_41
    | ~ spl3_58 ),
    inference(avatar_contradiction_clause,[],[f912])).

fof(f912,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_37
    | spl3_41
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f911,f283])).

fof(f911,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_11
    | ~ spl3_37
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f910,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_11
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f910,plain,
    ( k1_relat_1(k1_xboole_0) = sK1
    | ~ spl3_37
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f263,f646])).

fof(f646,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f645])).

fof(f645,plain,
    ( spl3_58
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f655,plain,
    ( ~ spl3_59
    | ~ spl3_16
    | ~ spl3_4
    | ~ spl3_5
    | spl3_14
    | ~ spl3_27
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_45
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f590,f487,f305,f222,f210,f194,f129,f93,f89,f135,f648])).

fof(f648,plain,
    ( spl3_59
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f135,plain,
    ( spl3_16
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f93,plain,
    ( spl3_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f194,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f210,plain,
    ( spl3_31
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f222,plain,
    ( spl3_33
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f305,plain,
    ( spl3_45
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f590,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | spl3_14
    | ~ spl3_27
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_45
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f580,f130])).

fof(f580,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_27
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_45
    | ~ spl3_54 ),
    inference(backward_demodulation,[],[f309,f488])).

fof(f488,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f487])).

fof(f309,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_27
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(backward_demodulation,[],[f240,f306])).

fof(f306,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f305])).

fof(f240,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_27
    | ~ spl3_31
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f232,f237])).

fof(f237,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f235,f90])).

fof(f235,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(superposition,[],[f211,f94])).

fof(f94,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f210])).

fof(f232,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_27
    | ~ spl3_33 ),
    inference(superposition,[],[f195,f223])).

fof(f223,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f222])).

fof(f195,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f194])).

fof(f654,plain,
    ( ~ spl3_21
    | ~ spl3_1
    | ~ spl3_17
    | spl3_59 ),
    inference(avatar_split_clause,[],[f653,f648,f139,f77,f157])).

fof(f157,plain,
    ( spl3_21
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f77,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f653,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_17
    | spl3_59 ),
    inference(subsumption_resolution,[],[f651,f78])).

fof(f78,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f651,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_17
    | spl3_59 ),
    inference(resolution,[],[f649,f140])).

fof(f649,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_59 ),
    inference(avatar_component_clause,[],[f648])).

fof(f650,plain,
    ( spl3_58
    | ~ spl3_59
    | ~ spl3_57
    | ~ spl3_23
    | ~ spl3_45
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f582,f487,f305,f165,f640,f648,f645])).

fof(f165,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f582,plain,
    ( k1_xboole_0 != sK0
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_23
    | ~ spl3_45
    | ~ spl3_54 ),
    inference(backward_demodulation,[],[f318,f488])).

fof(f318,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_23
    | ~ spl3_45 ),
    inference(superposition,[],[f166,f306])).

fof(f166,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f165])).

fof(f638,plain,
    ( spl3_40
    | ~ spl3_21
    | ~ spl3_41
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f468,f243,f165,f282,f157,f279])).

fof(f243,plain,
    ( spl3_34
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f468,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(superposition,[],[f166,f244])).

fof(f244,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f243])).

fof(f576,plain,
    ( spl3_55
    | ~ spl3_2
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f495,f279,f81,f574])).

fof(f81,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f495,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_40 ),
    inference(backward_demodulation,[],[f82,f280])).

fof(f82,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f355,plain,
    ( spl3_52
    | ~ spl3_32
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f314,f300,f214,f353])).

fof(f300,plain,
    ( spl3_44
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f314,plain,
    ( ! [X4,X5,X3] :
        ( k1_relat_1(X5) = X3
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(X5,X3,X4) )
    | ~ spl3_32
    | ~ spl3_44 ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( ! [X4,X5,X3] :
        ( k1_relat_1(X5) = X3
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(X5,X3,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl3_32
    | ~ spl3_44 ),
    inference(superposition,[],[f301,f215])).

fof(f301,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f300])).

fof(f329,plain,
    ( spl3_47
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f231,f206,f121,f117,f109,f101,f97,f327])).

fof(f109,plain,
    ( spl3_9
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f206,plain,
    ( spl3_30
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f231,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f230,f118])).

fof(f230,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f229,f98])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) )
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f228,f102])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) )
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f227,f110])).

fof(f110,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) )
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(superposition,[],[f207,f122])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v1_funct_2(X1,k1_relat_1(X1),X0) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f206])).

fof(f307,plain,
    ( spl3_45
    | ~ spl3_21
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f226,f202,f81,f77,f157,f305])).

fof(f202,plain,
    ( spl3_29
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f226,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f225,f78])).

fof(f225,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(resolution,[],[f203,f82])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f202])).

fof(f302,plain,(
    spl3_44 ),
    inference(avatar_split_clause,[],[f68,f300])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f298,plain,(
    spl3_43 ),
    inference(avatar_split_clause,[],[f67,f296])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f264,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_31
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f241,f222,f210,f93,f89,f262])).

fof(f241,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_31
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f223,f237])).

fof(f245,plain,
    ( spl3_34
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f237,f210,f93,f89,f243])).

fof(f224,plain,
    ( spl3_33
    | ~ spl3_21
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f220,f198,f81,f77,f157,f222])).

fof(f220,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f219,f78])).

fof(f219,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(resolution,[],[f199,f82])).

fof(f216,plain,(
    spl3_32 ),
    inference(avatar_split_clause,[],[f62,f214])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f212,plain,(
    spl3_31 ),
    inference(avatar_split_clause,[],[f61,f210])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f208,plain,(
    spl3_30 ),
    inference(avatar_split_clause,[],[f58,f206])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f204,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f57,f202])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f200,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f56,f198])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f196,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f53,f194])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f170,plain,
    ( ~ spl3_4
    | ~ spl3_20
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_20
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f158,f90,f152])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f158,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f167,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f51,f165])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f163,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f50,f161])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f159,plain,
    ( ~ spl3_21
    | ~ spl3_1
    | spl3_16
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f155,f143,f135,f77,f157])).

fof(f143,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f155,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_16
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f154,f78])).

fof(f154,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_16
    | ~ spl3_18 ),
    inference(resolution,[],[f144,f136])).

fof(f136,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f144,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f153,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f60,f151])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f145,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f55,f143])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f141,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f54,f139])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f137,plain,
    ( ~ spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f36,f135,f132,f129])).

fof(f36,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f127,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f45,f125])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f123,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f43,f121])).

fof(f43,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f119,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f42,f117])).

fof(f42,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f111,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f44,f109])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f103,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f99,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f97])).

fof(f46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f95,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:34:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (8343)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (8339)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (8343)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f1137,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f111,f119,f123,f127,f137,f141,f145,f153,f159,f163,f167,f170,f196,f200,f204,f208,f212,f216,f224,f245,f264,f298,f302,f307,f329,f355,f576,f638,f650,f654,f655,f913,f974,f999,f1004,f1021,f1028,f1041,f1107,f1136])).
% 0.21/0.46  fof(f1136,plain,(
% 0.21/0.46    ~spl3_13 | spl3_14 | ~spl3_40 | ~spl3_41 | ~spl3_64),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f1135])).
% 0.21/0.46  fof(f1135,plain,(
% 0.21/0.46    $false | (~spl3_13 | spl3_14 | ~spl3_40 | ~spl3_41 | ~spl3_64)),
% 0.21/0.46    inference(subsumption_resolution,[],[f1134,f126])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    spl3_13 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.46  fof(f1134,plain,(
% 0.21/0.46    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_14 | ~spl3_40 | ~spl3_41 | ~spl3_64)),
% 0.21/0.46    inference(forward_demodulation,[],[f1133,f1017])).
% 0.21/0.46  fof(f1017,plain,(
% 0.21/0.46    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl3_64),
% 0.21/0.46    inference(avatar_component_clause,[],[f1016])).
% 0.21/0.46  fof(f1016,plain,(
% 0.21/0.46    spl3_64 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.46  fof(f1133,plain,(
% 0.21/0.46    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_14 | ~spl3_40 | ~spl3_41)),
% 0.21/0.46    inference(forward_demodulation,[],[f1132,f280])).
% 0.21/0.46  fof(f280,plain,(
% 0.21/0.46    k1_xboole_0 = sK2 | ~spl3_40),
% 0.21/0.46    inference(avatar_component_clause,[],[f279])).
% 0.21/0.46  fof(f279,plain,(
% 0.21/0.46    spl3_40 <=> k1_xboole_0 = sK2),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.46  fof(f1132,plain,(
% 0.21/0.46    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_14 | ~spl3_41)),
% 0.21/0.46    inference(forward_demodulation,[],[f130,f636])).
% 0.21/0.46  fof(f636,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | ~spl3_41),
% 0.21/0.46    inference(avatar_component_clause,[],[f282])).
% 0.21/0.46  fof(f282,plain,(
% 0.21/0.46    spl3_41 <=> k1_xboole_0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f129])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    spl3_14 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f1107,plain,(
% 0.21/0.46    spl3_15 | ~spl3_40 | ~spl3_41 | ~spl3_47 | ~spl3_64),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f1106])).
% 0.21/0.46  fof(f1106,plain,(
% 0.21/0.46    $false | (spl3_15 | ~spl3_40 | ~spl3_41 | ~spl3_47 | ~spl3_64)),
% 0.21/0.46    inference(subsumption_resolution,[],[f1105,f328])).
% 0.21/0.46  fof(f328,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_47),
% 0.21/0.46    inference(avatar_component_clause,[],[f327])).
% 0.21/0.46  fof(f327,plain,(
% 0.21/0.46    spl3_47 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.46  fof(f1105,plain,(
% 0.21/0.46    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl3_15 | ~spl3_40 | ~spl3_41 | ~spl3_64)),
% 0.21/0.46    inference(forward_demodulation,[],[f1079,f1017])).
% 0.21/0.46  fof(f1079,plain,(
% 0.21/0.46    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_15 | ~spl3_40 | ~spl3_41)),
% 0.21/0.46    inference(backward_demodulation,[],[f1049,f280])).
% 0.21/0.46  fof(f1049,plain,(
% 0.21/0.46    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_15 | ~spl3_41)),
% 0.21/0.46    inference(backward_demodulation,[],[f133,f636])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f132])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    spl3_15 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f1041,plain,(
% 0.21/0.46    ~spl3_14 | ~spl3_32 | ~spl3_37 | spl3_63),
% 0.21/0.46    inference(avatar_split_clause,[],[f1003,f997,f262,f214,f129])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    spl3_32 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    spl3_37 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.46  fof(f997,plain,(
% 0.21/0.46    spl3_63 <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.21/0.46  fof(f1003,plain,(
% 0.21/0.46    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_32 | ~spl3_37 | spl3_63)),
% 0.21/0.46    inference(subsumption_resolution,[],[f1001,f263])).
% 0.21/0.46  fof(f263,plain,(
% 0.21/0.46    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_37),
% 0.21/0.46    inference(avatar_component_clause,[],[f262])).
% 0.21/0.46  fof(f1001,plain,(
% 0.21/0.46    sK1 != k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_32 | spl3_63)),
% 0.21/0.46    inference(superposition,[],[f998,f215])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_32),
% 0.21/0.46    inference(avatar_component_clause,[],[f214])).
% 0.21/0.46  fof(f998,plain,(
% 0.21/0.46    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | spl3_63),
% 0.21/0.46    inference(avatar_component_clause,[],[f997])).
% 0.21/0.46  fof(f1028,plain,(
% 0.21/0.46    ~spl3_6 | ~spl3_7 | ~spl3_17 | spl3_65),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f1027])).
% 0.21/0.46  fof(f1027,plain,(
% 0.21/0.46    $false | (~spl3_6 | ~spl3_7 | ~spl3_17 | spl3_65)),
% 0.21/0.46    inference(subsumption_resolution,[],[f1026,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    v1_relat_1(k1_xboole_0) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl3_6 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f1026,plain,(
% 0.21/0.46    ~v1_relat_1(k1_xboole_0) | (~spl3_7 | ~spl3_17 | spl3_65)),
% 0.21/0.46    inference(subsumption_resolution,[],[f1023,f102])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    v1_funct_1(k1_xboole_0) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl3_7 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f1023,plain,(
% 0.21/0.46    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl3_17 | spl3_65)),
% 0.21/0.46    inference(resolution,[],[f1020,f140])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f139])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    spl3_17 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f1020,plain,(
% 0.21/0.46    ~v1_relat_1(k2_funct_1(k1_xboole_0)) | spl3_65),
% 0.21/0.46    inference(avatar_component_clause,[],[f1019])).
% 0.21/0.46  fof(f1019,plain,(
% 0.21/0.46    spl3_65 <=> v1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.21/0.46  fof(f1021,plain,(
% 0.21/0.46    spl3_64 | ~spl3_65 | ~spl3_22 | ~spl3_61),
% 0.21/0.46    inference(avatar_split_clause,[],[f979,f972,f161,f1019,f1016])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    spl3_22 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.46  fof(f972,plain,(
% 0.21/0.46    spl3_61 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.21/0.46  fof(f979,plain,(
% 0.21/0.46    ~v1_relat_1(k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_22 | ~spl3_61)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f978])).
% 0.21/0.46  fof(f978,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_22 | ~spl3_61)),
% 0.21/0.46    inference(superposition,[],[f162,f973])).
% 0.21/0.46  fof(f973,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_61),
% 0.21/0.46    inference(avatar_component_clause,[],[f972])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl3_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f161])).
% 0.21/0.46  fof(f1004,plain,(
% 0.21/0.46    spl3_54 | ~spl3_3 | ~spl3_4 | spl3_41 | ~spl3_52),
% 0.21/0.46    inference(avatar_split_clause,[],[f923,f353,f282,f89,f85,f487])).
% 0.21/0.46  fof(f487,plain,(
% 0.21/0.46    spl3_54 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl3_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f353,plain,(
% 0.21/0.46    spl3_52 <=> ! [X3,X5,X4] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.46  fof(f923,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK2) | (~spl3_3 | ~spl3_4 | spl3_41 | ~spl3_52)),
% 0.21/0.46    inference(subsumption_resolution,[],[f657,f283])).
% 0.21/0.46  fof(f283,plain,(
% 0.21/0.46    k1_xboole_0 != sK1 | spl3_41),
% 0.21/0.46    inference(avatar_component_clause,[],[f282])).
% 0.21/0.46  fof(f657,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK2) | (~spl3_3 | ~spl3_4 | ~spl3_52)),
% 0.21/0.46    inference(subsumption_resolution,[],[f598,f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    v1_funct_2(sK2,sK0,sK1) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f85])).
% 0.21/0.46  fof(f598,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | (~spl3_4 | ~spl3_52)),
% 0.21/0.46    inference(resolution,[],[f90,f354])).
% 0.21/0.46  fof(f354,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4)) ) | ~spl3_52),
% 0.21/0.46    inference(avatar_component_clause,[],[f353])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f89])).
% 0.21/0.46  fof(f999,plain,(
% 0.21/0.46    ~spl3_14 | ~spl3_63 | spl3_15 | ~spl3_43 | spl3_57),
% 0.21/0.46    inference(avatar_split_clause,[],[f943,f640,f296,f132,f997,f129])).
% 0.21/0.46  fof(f296,plain,(
% 0.21/0.46    spl3_43 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.46  fof(f640,plain,(
% 0.21/0.46    spl3_57 <=> k1_xboole_0 = sK0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.46  fof(f943,plain,(
% 0.21/0.46    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl3_15 | ~spl3_43 | spl3_57)),
% 0.21/0.46    inference(subsumption_resolution,[],[f303,f641])).
% 0.21/0.46  fof(f641,plain,(
% 0.21/0.46    k1_xboole_0 != sK0 | spl3_57),
% 0.21/0.46    inference(avatar_component_clause,[],[f640])).
% 0.21/0.46  fof(f303,plain,(
% 0.21/0.46    k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl3_15 | ~spl3_43)),
% 0.21/0.46    inference(resolution,[],[f297,f133])).
% 0.21/0.46  fof(f297,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_43),
% 0.21/0.46    inference(avatar_component_clause,[],[f296])).
% 0.21/0.46  fof(f974,plain,(
% 0.21/0.46    spl3_61 | ~spl3_6 | ~spl3_7 | ~spl3_12 | ~spl3_28 | ~spl3_55),
% 0.21/0.46    inference(avatar_split_clause,[],[f757,f574,f198,f121,f101,f97,f972])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    spl3_12 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    spl3_28 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.46  fof(f574,plain,(
% 0.21/0.46    spl3_55 <=> v2_funct_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.21/0.46  fof(f757,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_7 | ~spl3_12 | ~spl3_28 | ~spl3_55)),
% 0.21/0.46    inference(forward_demodulation,[],[f742,f122])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f121])).
% 0.21/0.46  fof(f742,plain,(
% 0.21/0.46    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_7 | ~spl3_28 | ~spl3_55)),
% 0.21/0.46    inference(subsumption_resolution,[],[f741,f98])).
% 0.21/0.46  fof(f741,plain,(
% 0.21/0.46    ~v1_relat_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_7 | ~spl3_28 | ~spl3_55)),
% 0.21/0.46    inference(subsumption_resolution,[],[f737,f102])).
% 0.21/0.46  fof(f737,plain,(
% 0.21/0.46    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_28 | ~spl3_55)),
% 0.21/0.46    inference(resolution,[],[f575,f199])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) ) | ~spl3_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f198])).
% 0.21/0.46  fof(f575,plain,(
% 0.21/0.46    v2_funct_1(k1_xboole_0) | ~spl3_55),
% 0.21/0.46    inference(avatar_component_clause,[],[f574])).
% 0.21/0.46  fof(f913,plain,(
% 0.21/0.46    ~spl3_11 | ~spl3_37 | spl3_41 | ~spl3_58),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f912])).
% 0.21/0.46  fof(f912,plain,(
% 0.21/0.46    $false | (~spl3_11 | ~spl3_37 | spl3_41 | ~spl3_58)),
% 0.21/0.46    inference(subsumption_resolution,[],[f911,f283])).
% 0.21/0.46  fof(f911,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | (~spl3_11 | ~spl3_37 | ~spl3_58)),
% 0.21/0.46    inference(forward_demodulation,[],[f910,f118])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f117])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl3_11 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f910,plain,(
% 0.21/0.46    k1_relat_1(k1_xboole_0) = sK1 | (~spl3_37 | ~spl3_58)),
% 0.21/0.46    inference(forward_demodulation,[],[f263,f646])).
% 0.21/0.46  fof(f646,plain,(
% 0.21/0.46    k1_xboole_0 = k2_funct_1(sK2) | ~spl3_58),
% 0.21/0.46    inference(avatar_component_clause,[],[f645])).
% 0.21/0.46  fof(f645,plain,(
% 0.21/0.46    spl3_58 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.21/0.46  fof(f655,plain,(
% 0.21/0.46    ~spl3_59 | ~spl3_16 | ~spl3_4 | ~spl3_5 | spl3_14 | ~spl3_27 | ~spl3_31 | ~spl3_33 | ~spl3_45 | ~spl3_54),
% 0.21/0.46    inference(avatar_split_clause,[],[f590,f487,f305,f222,f210,f194,f129,f93,f89,f135,f648])).
% 0.21/0.46  fof(f648,plain,(
% 0.21/0.46    spl3_59 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    spl3_16 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl3_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    spl3_27 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.46  fof(f210,plain,(
% 0.21/0.46    spl3_31 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    spl3_33 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.46  fof(f305,plain,(
% 0.21/0.46    spl3_45 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.46  fof(f590,plain,(
% 0.21/0.46    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | spl3_14 | ~spl3_27 | ~spl3_31 | ~spl3_33 | ~spl3_45 | ~spl3_54)),
% 0.21/0.46    inference(subsumption_resolution,[],[f580,f130])).
% 0.21/0.46  fof(f580,plain,(
% 0.21/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_27 | ~spl3_31 | ~spl3_33 | ~spl3_45 | ~spl3_54)),
% 0.21/0.46    inference(backward_demodulation,[],[f309,f488])).
% 0.21/0.46  fof(f488,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK2) | ~spl3_54),
% 0.21/0.46    inference(avatar_component_clause,[],[f487])).
% 0.21/0.46  fof(f309,plain,(
% 0.21/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_27 | ~spl3_31 | ~spl3_33 | ~spl3_45)),
% 0.21/0.46    inference(backward_demodulation,[],[f240,f306])).
% 0.21/0.46  fof(f306,plain,(
% 0.21/0.46    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_45),
% 0.21/0.46    inference(avatar_component_clause,[],[f305])).
% 0.21/0.46  fof(f240,plain,(
% 0.21/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_27 | ~spl3_31 | ~spl3_33)),
% 0.21/0.46    inference(backward_demodulation,[],[f232,f237])).
% 0.21/0.46  fof(f237,plain,(
% 0.21/0.46    sK1 = k2_relat_1(sK2) | (~spl3_4 | ~spl3_5 | ~spl3_31)),
% 0.21/0.46    inference(subsumption_resolution,[],[f235,f90])).
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl3_5 | ~spl3_31)),
% 0.21/0.46    inference(superposition,[],[f211,f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f211,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_31),
% 0.21/0.46    inference(avatar_component_clause,[],[f210])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_27 | ~spl3_33)),
% 0.21/0.46    inference(superposition,[],[f195,f223])).
% 0.21/0.46  fof(f223,plain,(
% 0.21/0.46    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_33),
% 0.21/0.46    inference(avatar_component_clause,[],[f222])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f194])).
% 0.21/0.46  fof(f654,plain,(
% 0.21/0.46    ~spl3_21 | ~spl3_1 | ~spl3_17 | spl3_59),
% 0.21/0.46    inference(avatar_split_clause,[],[f653,f648,f139,f77,f157])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    spl3_21 <=> v1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f653,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_17 | spl3_59)),
% 0.21/0.46    inference(subsumption_resolution,[],[f651,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f651,plain,(
% 0.21/0.46    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_17 | spl3_59)),
% 0.21/0.46    inference(resolution,[],[f649,f140])).
% 0.21/0.46  fof(f649,plain,(
% 0.21/0.46    ~v1_relat_1(k2_funct_1(sK2)) | spl3_59),
% 0.21/0.46    inference(avatar_component_clause,[],[f648])).
% 0.21/0.46  fof(f650,plain,(
% 0.21/0.46    spl3_58 | ~spl3_59 | ~spl3_57 | ~spl3_23 | ~spl3_45 | ~spl3_54),
% 0.21/0.46    inference(avatar_split_clause,[],[f582,f487,f305,f165,f640,f648,f645])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    spl3_23 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.46  fof(f582,plain,(
% 0.21/0.46    k1_xboole_0 != sK0 | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | (~spl3_23 | ~spl3_45 | ~spl3_54)),
% 0.21/0.46    inference(backward_demodulation,[],[f318,f488])).
% 0.21/0.46  fof(f318,plain,(
% 0.21/0.46    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | (~spl3_23 | ~spl3_45)),
% 0.21/0.46    inference(superposition,[],[f166,f306])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl3_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f165])).
% 0.21/0.46  fof(f638,plain,(
% 0.21/0.46    spl3_40 | ~spl3_21 | ~spl3_41 | ~spl3_23 | ~spl3_34),
% 0.21/0.46    inference(avatar_split_clause,[],[f468,f243,f165,f282,f157,f279])).
% 0.21/0.46  fof(f243,plain,(
% 0.21/0.46    spl3_34 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.46  fof(f468,plain,(
% 0.21/0.46    k1_xboole_0 != sK1 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | (~spl3_23 | ~spl3_34)),
% 0.21/0.46    inference(superposition,[],[f166,f244])).
% 0.21/0.46  fof(f244,plain,(
% 0.21/0.46    sK1 = k2_relat_1(sK2) | ~spl3_34),
% 0.21/0.46    inference(avatar_component_clause,[],[f243])).
% 0.21/0.46  fof(f576,plain,(
% 0.21/0.46    spl3_55 | ~spl3_2 | ~spl3_40),
% 0.21/0.46    inference(avatar_split_clause,[],[f495,f279,f81,f574])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f495,plain,(
% 0.21/0.46    v2_funct_1(k1_xboole_0) | (~spl3_2 | ~spl3_40)),
% 0.21/0.46    inference(backward_demodulation,[],[f82,f280])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f355,plain,(
% 0.21/0.46    spl3_52 | ~spl3_32 | ~spl3_44),
% 0.21/0.46    inference(avatar_split_clause,[],[f314,f300,f214,f353])).
% 0.21/0.46  fof(f300,plain,(
% 0.21/0.46    spl3_44 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.46  fof(f314,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4)) ) | (~spl3_32 | ~spl3_44)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f311])).
% 0.21/0.46  fof(f311,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | (~spl3_32 | ~spl3_44)),
% 0.21/0.46    inference(superposition,[],[f301,f215])).
% 0.21/0.46  fof(f301,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) ) | ~spl3_44),
% 0.21/0.46    inference(avatar_component_clause,[],[f300])).
% 0.21/0.46  fof(f329,plain,(
% 0.21/0.46    spl3_47 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_11 | ~spl3_12 | ~spl3_30),
% 0.21/0.46    inference(avatar_split_clause,[],[f231,f206,f121,f117,f109,f101,f97,f327])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl3_9 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    spl3_30 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_11 | ~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(forward_demodulation,[],[f230,f118])).
% 0.21/0.46  fof(f230,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) ) | (~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(subsumption_resolution,[],[f229,f98])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) ) | (~spl3_7 | ~spl3_9 | ~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(subsumption_resolution,[],[f228,f102])).
% 0.21/0.46  fof(f228,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) ) | (~spl3_9 | ~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(subsumption_resolution,[],[f227,f110])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f109])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) ) | (~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(superposition,[],[f207,f122])).
% 0.21/0.46  fof(f207,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) ) | ~spl3_30),
% 0.21/0.46    inference(avatar_component_clause,[],[f206])).
% 0.21/0.46  fof(f307,plain,(
% 0.21/0.46    spl3_45 | ~spl3_21 | ~spl3_1 | ~spl3_2 | ~spl3_29),
% 0.21/0.46    inference(avatar_split_clause,[],[f226,f202,f81,f77,f157,f305])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    spl3_29 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f225,f78])).
% 0.21/0.47  fof(f225,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_2 | ~spl3_29)),
% 0.21/0.47    inference(resolution,[],[f203,f82])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) ) | ~spl3_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f202])).
% 0.21/0.47  fof(f302,plain,(
% 0.21/0.47    spl3_44),
% 0.21/0.47    inference(avatar_split_clause,[],[f68,f300])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.47  fof(f298,plain,(
% 0.21/0.47    spl3_43),
% 0.21/0.47    inference(avatar_split_clause,[],[f67,f296])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    spl3_37 | ~spl3_4 | ~spl3_5 | ~spl3_31 | ~spl3_33),
% 0.21/0.47    inference(avatar_split_clause,[],[f241,f222,f210,f93,f89,f262])).
% 0.21/0.47  fof(f241,plain,(
% 0.21/0.47    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_31 | ~spl3_33)),
% 0.21/0.47    inference(backward_demodulation,[],[f223,f237])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    spl3_34 | ~spl3_4 | ~spl3_5 | ~spl3_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f237,f210,f93,f89,f243])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    spl3_33 | ~spl3_21 | ~spl3_1 | ~spl3_2 | ~spl3_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f220,f198,f81,f77,f157,f222])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f219,f78])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_2 | ~spl3_28)),
% 0.21/0.47    inference(resolution,[],[f199,f82])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    spl3_32),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f214])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    spl3_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f210])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    spl3_30),
% 0.21/0.47    inference(avatar_split_clause,[],[f58,f206])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    spl3_29),
% 0.21/0.47    inference(avatar_split_clause,[],[f57,f202])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    spl3_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f56,f198])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    spl3_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f53,f194])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ~spl3_4 | ~spl3_20 | spl3_21),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    $false | (~spl3_4 | ~spl3_20 | spl3_21)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f158,f90,f152])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    spl3_20 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl3_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f157])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    spl3_23),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f165])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    spl3_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f161])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    ~spl3_21 | ~spl3_1 | spl3_16 | ~spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f155,f143,f135,f77,f157])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    spl3_18 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | (~spl3_1 | spl3_16 | ~spl3_18)),
% 0.21/0.47    inference(subsumption_resolution,[],[f154,f78])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl3_16 | ~spl3_18)),
% 0.21/0.47    inference(resolution,[],[f144,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~v1_funct_1(k2_funct_1(sK2)) | spl3_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f135])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f143])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    spl3_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f151])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f55,f143])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl3_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f54,f139])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ~spl3_14 | ~spl3_15 | ~spl3_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f135,f132,f129])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f15])).
% 0.21/0.47  fof(f15,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl3_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f125])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f43,f121])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f117])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f44,f109])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f48,f101])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    v1_funct_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f46,f97])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f93])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f89])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f85])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f81])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    v2_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f77])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (8343)------------------------------
% 0.21/0.47  % (8343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8343)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (8343)Memory used [KB]: 11001
% 0.21/0.47  % (8343)Time elapsed: 0.059 s
% 0.21/0.47  % (8343)------------------------------
% 0.21/0.47  % (8343)------------------------------
% 0.21/0.47  % (8333)Success in time 0.116 s
%------------------------------------------------------------------------------
