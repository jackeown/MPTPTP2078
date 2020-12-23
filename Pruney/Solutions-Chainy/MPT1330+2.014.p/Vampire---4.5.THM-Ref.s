%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 379 expanded)
%              Number of leaves         :   53 ( 178 expanded)
%              Depth                    :    6
%              Number of atoms          :  598 (1181 expanded)
%              Number of equality atoms :  105 ( 256 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f72,f76,f80,f84,f88,f92,f108,f112,f116,f120,f124,f132,f136,f140,f149,f154,f158,f165,f168,f173,f179,f183,f189,f193,f198,f202,f207,f212,f216,f222,f229,f232,f252,f303,f307,f319,f323,f330,f340])).

fof(f340,plain,
    ( ~ spl3_1
    | ~ spl3_29
    | spl3_49
    | ~ spl3_50
    | ~ spl3_51 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_29
    | spl3_49
    | ~ spl3_50
    | ~ spl3_51 ),
    inference(unit_resulting_resolution,[],[f52,f318,f322,f329,f178])).

fof(f178,plain,
    ( ! [X2,X1] :
        ( v1_partfun1(X2,k1_xboole_0)
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl3_29
  <=> ! [X1,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_partfun1(X2,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f329,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl3_51
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f322,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl3_50
  <=> v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f318,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_49 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl3_49
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f52,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f330,plain,
    ( spl3_51
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f309,f110,f67,f328])).

fof(f67,plain,
    ( spl3_5
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f110,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

% (7245)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f309,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f111,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f323,plain,
    ( spl3_50
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f308,f106,f67,f321])).

fof(f106,plain,
    ( spl3_13
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f308,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f107,f68])).

fof(f107,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f319,plain,
    ( ~ spl3_49
    | ~ spl3_5
    | spl3_39 ),
    inference(avatar_split_clause,[],[f315,f224,f67,f317])).

fof(f224,plain,
    ( spl3_39
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f315,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_5
    | spl3_39 ),
    inference(backward_demodulation,[],[f225,f68])).

fof(f225,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f224])).

fof(f307,plain,
    ( ~ spl3_26
    | ~ spl3_17
    | spl3_48 ),
    inference(avatar_split_clause,[],[f306,f301,f122,f160])).

fof(f160,plain,
    ( spl3_26
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f122,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f301,plain,
    ( spl3_48
  <=> k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f306,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_17
    | spl3_48 ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_17
    | spl3_48 ),
    inference(superposition,[],[f302,f123])).

fof(f123,plain,
    ( ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f302,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | spl3_48 ),
    inference(avatar_component_clause,[],[f301])).

fof(f303,plain,
    ( ~ spl3_48
    | ~ spl3_15
    | spl3_38
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f273,f250,f220,f114,f301])).

fof(f114,plain,
    ( spl3_15
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f220,plain,
    ( spl3_38
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f250,plain,
    ( spl3_43
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f273,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ spl3_15
    | spl3_38
    | ~ spl3_43 ),
    inference(backward_demodulation,[],[f221,f269])).

fof(f269,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_15
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f115,f251])).

fof(f251,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f250])).

fof(f115,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f221,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_relat_1(sK2))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f220])).

fof(f252,plain,
    ( spl3_43
    | ~ spl3_15
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f236,f227,f114,f250])).

fof(f227,plain,
    ( spl3_40
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f236,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_15
    | ~ spl3_40 ),
    inference(backward_demodulation,[],[f115,f228])).

fof(f228,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f227])).

fof(f232,plain,
    ( ~ spl3_1
    | spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_31
    | spl3_39 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl3_1
    | spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_31
    | spl3_39 ),
    inference(unit_resulting_resolution,[],[f52,f71,f107,f111,f225,f188])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( v1_partfun1(X2,X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X2) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_31
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f71,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_6
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f229,plain,
    ( ~ spl3_39
    | spl3_40
    | ~ spl3_14
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f217,f210,f110,f227,f224])).

fof(f210,plain,
    ( spl3_36
  <=> ! [X1,X0] :
        ( ~ v1_partfun1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f217,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_14
    | ~ spl3_36 ),
    inference(resolution,[],[f211,f111])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(sK2) = X0
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f210])).

fof(f222,plain,
    ( ~ spl3_38
    | spl3_33
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f218,f214,f196,f220])).

fof(f196,plain,
    ( spl3_33
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f214,plain,
    ( spl3_37
  <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f218,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_relat_1(sK2))
    | spl3_33
    | ~ spl3_37 ),
    inference(superposition,[],[f197,f215])).

fof(f215,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f214])).

fof(f197,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f196])).

fof(f216,plain,
    ( ~ spl3_26
    | spl3_37
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f185,f181,f152,f214,f160])).

fof(f152,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f181,plain,
    ( spl3_30
  <=> k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f185,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(superposition,[],[f153,f182])).

fof(f182,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f181])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f152])).

fof(f212,plain,
    ( spl3_36
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f208,f205,f134,f210])).

fof(f134,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f205,plain,
    ( spl3_35
  <=> ! [X0] :
        ( k1_relat_1(sK2) = X0
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(resolution,[],[f206,f135])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f134])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | ~ v1_partfun1(sK2,X0)
        | k1_relat_1(sK2) = X0 )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( spl3_35
    | ~ spl3_14
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f203,f200,f110,f205])).

fof(f200,plain,
    ( spl3_34
  <=> ! [X1,X3,X0,X2] :
        ( ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f203,plain,
    ( ! [X0] :
        ( k1_relat_1(sK2) = X0
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl3_14
    | ~ spl3_34 ),
    inference(resolution,[],[f201,f111])).

fof(f201,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ v4_relat_1(X0,X1) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl3_34
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f169,f156,f90,f200])).

fof(f90,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f156,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f169,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(resolution,[],[f157,f91])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f156])).

fof(f198,plain,
    ( ~ spl3_33
    | spl3_16
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f194,f191,f118,f196])).

fof(f118,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f191,plain,
    ( spl3_32
  <=> ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f194,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl3_16
    | ~ spl3_32 ),
    inference(superposition,[],[f119,f192])).

fof(f192,plain,
    ( ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f191])).

fof(f119,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f193,plain,
    ( spl3_32
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f184,f171,f110,f191])).

fof(f171,plain,
    ( spl3_28
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f184,plain,
    ( ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(resolution,[],[f172,f111])).

fof(f172,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f171])).

fof(f189,plain,(
    spl3_31 ),
    inference(avatar_split_clause,[],[f45,f187])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f183,plain,
    ( spl3_30
    | ~ spl3_10
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f175,f163,f86,f181])).

fof(f86,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f163,plain,
    ( spl3_27
  <=> r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f175,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_10
    | ~ spl3_27 ),
    inference(resolution,[],[f164,f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f164,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f163])).

fof(f179,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f49,f177])).

fof(f49,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f173,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f47,f171])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f168,plain,
    ( ~ spl3_11
    | ~ spl3_14
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_14
    | spl3_26 ),
    inference(unit_resulting_resolution,[],[f111,f161,f91])).

fof(f161,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f160])).

fof(f165,plain,
    ( ~ spl3_26
    | spl3_27
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f150,f147,f130,f163,f160])).

fof(f130,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f147,plain,
    ( spl3_23
  <=> v5_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f150,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(resolution,[],[f148,f131])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(X1,X0)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f148,plain,
    ( v5_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f158,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f41,f156])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f154,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f36,f152])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f149,plain,
    ( spl3_23
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f145,f138,f110,f147])).

fof(f138,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f145,plain,
    ( v5_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(resolution,[],[f139,f111])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f44,f138])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f136,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f43,f134])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f38,f130])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f124,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f34,f122])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f120,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f100,f82,f78,f59,f55,f118])).

fof(f55,plain,
    ( spl3_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( spl3_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f78,plain,
    ( spl3_8
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f100,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f95,f94])).

fof(f94,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f83,f60])).

fof(f60,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f95,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_2
    | spl3_8
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f79,f93])).

fof(f93,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f83,f56])).

fof(f56,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f79,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f116,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f94,f82,f59,f114])).

fof(f112,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f99,f82,f74,f59,f55,f110])).

fof(f74,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f96,f94])).

fof(f96,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f75,f93])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f74])).

% (7250)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f108,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f82,f63,f59,f55,f106])).

fof(f63,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f98,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f97,f94])).

fof(f97,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f64,f93])).

fof(f64,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f92,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f42,f90])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f88,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f84,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f80,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f76,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f27,f70,f67])).

fof(f27,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:50:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (7243)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (7243)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (7237)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (7235)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (7235)Refutation not found, incomplete strategy% (7235)------------------------------
% 0.22/0.48  % (7235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7235)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7235)Memory used [KB]: 10618
% 0.22/0.48  % (7235)Time elapsed: 0.070 s
% 0.22/0.48  % (7235)------------------------------
% 0.22/0.48  % (7235)------------------------------
% 0.22/0.48  % (7234)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f341,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f72,f76,f80,f84,f88,f92,f108,f112,f116,f120,f124,f132,f136,f140,f149,f154,f158,f165,f168,f173,f179,f183,f189,f193,f198,f202,f207,f212,f216,f222,f229,f232,f252,f303,f307,f319,f323,f330,f340])).
% 0.22/0.48  fof(f340,plain,(
% 0.22/0.48    ~spl3_1 | ~spl3_29 | spl3_49 | ~spl3_50 | ~spl3_51),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f335])).
% 0.22/0.48  fof(f335,plain,(
% 0.22/0.48    $false | (~spl3_1 | ~spl3_29 | spl3_49 | ~spl3_50 | ~spl3_51)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f52,f318,f322,f329,f178])).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f177])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    spl3_29 <=> ! [X1,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.48  fof(f329,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | ~spl3_51),
% 0.22/0.48    inference(avatar_component_clause,[],[f328])).
% 0.22/0.48  fof(f328,plain,(
% 0.22/0.48    spl3_51 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.22/0.48  fof(f322,plain,(
% 0.22/0.48    v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) | ~spl3_50),
% 0.22/0.48    inference(avatar_component_clause,[],[f321])).
% 0.22/0.48  fof(f321,plain,(
% 0.22/0.48    spl3_50 <=> v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.48  fof(f318,plain,(
% 0.22/0.48    ~v1_partfun1(sK2,k1_xboole_0) | spl3_49),
% 0.22/0.48    inference(avatar_component_clause,[],[f317])).
% 0.22/0.48  fof(f317,plain,(
% 0.22/0.48    spl3_49 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f330,plain,(
% 0.22/0.48    spl3_51 | ~spl3_5 | ~spl3_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f309,f110,f67,f328])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl3_5 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.48  % (7245)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  fof(f309,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_14)),
% 0.22/0.48    inference(backward_demodulation,[],[f111,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f110])).
% 0.22/0.48  fof(f323,plain,(
% 0.22/0.48    spl3_50 | ~spl3_5 | ~spl3_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f308,f106,f67,f321])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    spl3_13 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.48  fof(f308,plain,(
% 0.22/0.48    v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) | (~spl3_5 | ~spl3_13)),
% 0.22/0.48    inference(backward_demodulation,[],[f107,f68])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f106])).
% 0.22/0.48  fof(f319,plain,(
% 0.22/0.48    ~spl3_49 | ~spl3_5 | spl3_39),
% 0.22/0.48    inference(avatar_split_clause,[],[f315,f224,f67,f317])).
% 0.22/0.48  fof(f224,plain,(
% 0.22/0.48    spl3_39 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.48  fof(f315,plain,(
% 0.22/0.48    ~v1_partfun1(sK2,k1_xboole_0) | (~spl3_5 | spl3_39)),
% 0.22/0.48    inference(backward_demodulation,[],[f225,f68])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_39),
% 0.22/0.48    inference(avatar_component_clause,[],[f224])).
% 0.22/0.48  fof(f307,plain,(
% 0.22/0.48    ~spl3_26 | ~spl3_17 | spl3_48),
% 0.22/0.48    inference(avatar_split_clause,[],[f306,f301,f122,f160])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    spl3_26 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    spl3_17 <=> ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.48  fof(f301,plain,(
% 0.22/0.48    spl3_48 <=> k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.48  fof(f306,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | (~spl3_17 | spl3_48)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f305])).
% 0.22/0.48  fof(f305,plain,(
% 0.22/0.48    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_17 | spl3_48)),
% 0.22/0.48    inference(superposition,[],[f302,f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f122])).
% 0.22/0.48  fof(f302,plain,(
% 0.22/0.48    k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2) | spl3_48),
% 0.22/0.48    inference(avatar_component_clause,[],[f301])).
% 0.22/0.48  fof(f303,plain,(
% 0.22/0.48    ~spl3_48 | ~spl3_15 | spl3_38 | ~spl3_43),
% 0.22/0.48    inference(avatar_split_clause,[],[f273,f250,f220,f114,f301])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    spl3_15 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    spl3_38 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.48  fof(f250,plain,(
% 0.22/0.48    spl3_43 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.22/0.48  fof(f273,plain,(
% 0.22/0.48    k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2) | (~spl3_15 | spl3_38 | ~spl3_43)),
% 0.22/0.48    inference(backward_demodulation,[],[f221,f269])).
% 0.22/0.48  fof(f269,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_15 | ~spl3_43)),
% 0.22/0.48    inference(forward_demodulation,[],[f115,f251])).
% 0.22/0.48  fof(f251,plain,(
% 0.22/0.48    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_43),
% 0.22/0.48    inference(avatar_component_clause,[],[f250])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f114])).
% 0.22/0.48  fof(f221,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k10_relat_1(sK2,k2_relat_1(sK2)) | spl3_38),
% 0.22/0.48    inference(avatar_component_clause,[],[f220])).
% 0.22/0.48  fof(f252,plain,(
% 0.22/0.48    spl3_43 | ~spl3_15 | ~spl3_40),
% 0.22/0.48    inference(avatar_split_clause,[],[f236,f227,f114,f250])).
% 0.22/0.48  fof(f227,plain,(
% 0.22/0.48    spl3_40 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.48  fof(f236,plain,(
% 0.22/0.48    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_15 | ~spl3_40)),
% 0.22/0.48    inference(backward_demodulation,[],[f115,f228])).
% 0.22/0.48  fof(f228,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_40),
% 0.22/0.48    inference(avatar_component_clause,[],[f227])).
% 0.22/0.48  fof(f232,plain,(
% 0.22/0.48    ~spl3_1 | spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_31 | spl3_39),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f230])).
% 0.22/0.48  fof(f230,plain,(
% 0.22/0.48    $false | (~spl3_1 | spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_31 | spl3_39)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f52,f71,f107,f111,f225,f188])).
% 0.22/0.48  fof(f188,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_1(X2)) ) | ~spl3_31),
% 0.22/0.48    inference(avatar_component_clause,[],[f187])).
% 0.22/0.48  fof(f187,plain,(
% 0.22/0.48    spl3_31 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    k1_xboole_0 != k2_struct_0(sK1) | spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl3_6 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f229,plain,(
% 0.22/0.48    ~spl3_39 | spl3_40 | ~spl3_14 | ~spl3_36),
% 0.22/0.48    inference(avatar_split_clause,[],[f217,f210,f110,f227,f224])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    spl3_36 <=> ! [X1,X0] : (~v1_partfun1(sK2,X0) | k1_relat_1(sK2) = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.48  fof(f217,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_14 | ~spl3_36)),
% 0.22/0.48    inference(resolution,[],[f211,f111])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0 | ~v1_partfun1(sK2,X0)) ) | ~spl3_36),
% 0.22/0.48    inference(avatar_component_clause,[],[f210])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    ~spl3_38 | spl3_33 | ~spl3_37),
% 0.22/0.48    inference(avatar_split_clause,[],[f218,f214,f196,f220])).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    spl3_33 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.48  fof(f214,plain,(
% 0.22/0.48    spl3_37 <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k10_relat_1(sK2,k2_relat_1(sK2)) | (spl3_33 | ~spl3_37)),
% 0.22/0.48    inference(superposition,[],[f197,f215])).
% 0.22/0.48  fof(f215,plain,(
% 0.22/0.48    k10_relat_1(sK2,k2_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_37),
% 0.22/0.48    inference(avatar_component_clause,[],[f214])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | spl3_33),
% 0.22/0.48    inference(avatar_component_clause,[],[f196])).
% 0.22/0.48  fof(f216,plain,(
% 0.22/0.48    ~spl3_26 | spl3_37 | ~spl3_24 | ~spl3_30),
% 0.22/0.48    inference(avatar_split_clause,[],[f185,f181,f152,f214,f160])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    spl3_24 <=> ! [X1,X0] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    spl3_30 <=> k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.48  fof(f185,plain,(
% 0.22/0.48    k10_relat_1(sK2,k2_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_24 | ~spl3_30)),
% 0.22/0.48    inference(superposition,[],[f153,f182])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1)) | ~spl3_30),
% 0.22/0.48    inference(avatar_component_clause,[],[f181])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) ) | ~spl3_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f152])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    spl3_36 | ~spl3_20 | ~spl3_35),
% 0.22/0.48    inference(avatar_split_clause,[],[f208,f205,f134,f210])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    spl3_20 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    spl3_35 <=> ! [X0] : (k1_relat_1(sK2) = X0 | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.48  fof(f208,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_partfun1(sK2,X0) | k1_relat_1(sK2) = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl3_20 | ~spl3_35)),
% 0.22/0.48    inference(resolution,[],[f206,f135])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f134])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ( ! [X0] : (~v4_relat_1(sK2,X0) | ~v1_partfun1(sK2,X0) | k1_relat_1(sK2) = X0) ) | ~spl3_35),
% 0.22/0.48    inference(avatar_component_clause,[],[f205])).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    spl3_35 | ~spl3_14 | ~spl3_34),
% 0.22/0.48    inference(avatar_split_clause,[],[f203,f200,f110,f205])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    spl3_34 <=> ! [X1,X3,X0,X2] : (~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK2) = X0 | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (~spl3_14 | ~spl3_34)),
% 0.22/0.48    inference(resolution,[],[f201,f111])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1)) ) | ~spl3_34),
% 0.22/0.48    inference(avatar_component_clause,[],[f200])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    spl3_34 | ~spl3_11 | ~spl3_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f169,f156,f90,f200])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl3_11 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl3_25 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | (~spl3_11 | ~spl3_25)),
% 0.22/0.48    inference(resolution,[],[f157,f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f90])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) ) | ~spl3_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f156])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    ~spl3_33 | spl3_16 | ~spl3_32),
% 0.22/0.48    inference(avatar_split_clause,[],[f194,f191,f118,f196])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl3_16 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    spl3_32 <=> ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | (spl3_16 | ~spl3_32)),
% 0.22/0.48    inference(superposition,[],[f119,f192])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl3_32),
% 0.22/0.48    inference(avatar_component_clause,[],[f191])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f118])).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    spl3_32 | ~spl3_14 | ~spl3_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f184,f171,f110,f191])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    spl3_28 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | (~spl3_14 | ~spl3_28)),
% 0.22/0.48    inference(resolution,[],[f172,f111])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl3_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f171])).
% 0.22/0.48  fof(f189,plain,(
% 0.22/0.48    spl3_31),
% 0.22/0.48    inference(avatar_split_clause,[],[f45,f187])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    spl3_30 | ~spl3_10 | ~spl3_27),
% 0.22/0.48    inference(avatar_split_clause,[],[f175,f163,f86,f181])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl3_10 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    spl3_27 <=> r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1)) | (~spl3_10 | ~spl3_27)),
% 0.22/0.48    inference(resolution,[],[f164,f87])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f86])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | ~spl3_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f163])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    spl3_29),
% 0.22/0.48    inference(avatar_split_clause,[],[f49,f177])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | v1_partfun1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    spl3_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f47,f171])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    ~spl3_11 | ~spl3_14 | spl3_26),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f166])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    $false | (~spl3_11 | ~spl3_14 | spl3_26)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f111,f161,f91])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | spl3_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f160])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    ~spl3_26 | spl3_27 | ~spl3_19 | ~spl3_23),
% 0.22/0.48    inference(avatar_split_clause,[],[f150,f147,f130,f163,f160])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    spl3_19 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl3_23 <=> v5_relat_1(sK2,k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | ~v1_relat_1(sK2) | (~spl3_19 | ~spl3_23)),
% 0.22/0.48    inference(resolution,[],[f148,f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl3_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f130])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    v5_relat_1(sK2,k2_struct_0(sK1)) | ~spl3_23),
% 0.22/0.48    inference(avatar_component_clause,[],[f147])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    spl3_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f41,f156])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    spl3_24),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f152])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    spl3_23 | ~spl3_14 | ~spl3_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f145,f138,f110,f147])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    spl3_21 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    v5_relat_1(sK2,k2_struct_0(sK1)) | (~spl3_14 | ~spl3_21)),
% 0.22/0.48    inference(resolution,[],[f139,f111])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) ) | ~spl3_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f138])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    spl3_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f44,f138])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl3_20),
% 0.22/0.48    inference(avatar_split_clause,[],[f43,f134])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    spl3_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f130])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl3_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f122])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ~spl3_16 | ~spl3_2 | ~spl3_3 | spl3_8 | ~spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f100,f82,f78,f59,f55,f118])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl3_2 <=> l1_struct_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl3_3 <=> l1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl3_8 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl3_9 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_2 | ~spl3_3 | spl3_8 | ~spl3_9)),
% 0.22/0.48    inference(backward_demodulation,[],[f95,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl3_3 | ~spl3_9)),
% 0.22/0.48    inference(resolution,[],[f83,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    l1_struct_0(sK0) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f59])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f82])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_2 | spl3_8 | ~spl3_9)),
% 0.22/0.48    inference(backward_demodulation,[],[f79,f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    k2_struct_0(sK1) = u1_struct_0(sK1) | (~spl3_2 | ~spl3_9)),
% 0.22/0.48    inference(resolution,[],[f83,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    l1_struct_0(sK1) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f55])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl3_15 | ~spl3_3 | ~spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f94,f82,f59,f114])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    spl3_14 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f99,f82,f74,f59,f55,f110])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_9)),
% 0.22/0.48    inference(backward_demodulation,[],[f96,f94])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_2 | ~spl3_7 | ~spl3_9)),
% 0.22/0.48    inference(backward_demodulation,[],[f75,f93])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f74])).
% 0.22/0.49  % (7250)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl3_13 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f98,f82,f63,f59,f55,f106])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl3_4 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9)),
% 0.22/0.49    inference(backward_demodulation,[],[f97,f94])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.22/0.49    inference(backward_demodulation,[],[f64,f93])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f63])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f90])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f86])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f82])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ~spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f78])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f74])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl3_5 | ~spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f70,f67])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f63])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f59])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f55])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    l1_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f51])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (7243)------------------------------
% 0.22/0.49  % (7243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7243)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (7243)Memory used [KB]: 10746
% 0.22/0.49  % (7243)Time elapsed: 0.074 s
% 0.22/0.49  % (7243)------------------------------
% 0.22/0.49  % (7243)------------------------------
% 0.22/0.49  % (7231)Success in time 0.131 s
%------------------------------------------------------------------------------
