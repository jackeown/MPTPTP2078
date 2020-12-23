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
% DateTime   : Thu Dec  3 13:08:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 307 expanded)
%              Number of leaves         :   43 ( 130 expanded)
%              Depth                    :    9
%              Number of atoms          :  682 (1314 expanded)
%              Number of equality atoms :   57 ( 119 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f65,f69,f73,f77,f81,f85,f89,f93,f97,f101,f105,f113,f118,f122,f126,f132,f145,f151,f156,f160,f170,f183,f186,f189,f197,f201,f214,f226,f235,f241,f246])).

fof(f246,plain,
    ( spl6_4
    | ~ spl6_32
    | ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl6_4
    | ~ spl6_32
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f244,f60])).

fof(f60,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f244,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_32
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f196,f210])).

fof(f210,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl6_35
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f196,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_32
  <=> v1_xboole_0(k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f241,plain,
    ( ~ spl6_8
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f76,f213])).

fof(f213,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl6_36
  <=> ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f76,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f235,plain,
    ( ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_20
    | spl6_38 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_20
    | spl6_38 ),
    inference(subsumption_resolution,[],[f233,f56])).

fof(f56,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f233,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_20
    | spl6_38 ),
    inference(subsumption_resolution,[],[f232,f64])).

fof(f64,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f232,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_20
    | spl6_38 ),
    inference(subsumption_resolution,[],[f231,f80])).

fof(f80,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f231,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_20
    | spl6_38 ),
    inference(subsumption_resolution,[],[f230,f72])).

fof(f72,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f230,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_20
    | spl6_38 ),
    inference(subsumption_resolution,[],[f228,f52])).

fof(f52,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f228,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_20
    | spl6_38 ),
    inference(resolution,[],[f225,f125])).

fof(f125,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_20
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f225,plain,
    ( ~ m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0)
    | spl6_38 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl6_38
  <=> m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f226,plain,
    ( ~ spl6_38
    | spl6_31
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f215,f209,f192,f224])).

fof(f192,plain,
    ( spl6_31
  <=> m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f215,plain,
    ( ~ m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0)
    | spl6_31
    | ~ spl6_35 ),
    inference(backward_demodulation,[],[f193,f210])).

fof(f193,plain,
    ( ~ m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f192])).

fof(f214,plain,
    ( spl6_35
    | spl6_36
    | ~ spl6_6
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f206,f199,f67,f212,f209])).

fof(f67,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f199,plain,
    ( spl6_33
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_partfun1(X0,X1)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | sK0 = k1_relat_1(sK4) )
    | ~ spl6_6
    | ~ spl6_33 ),
    inference(resolution,[],[f200,f68])).

fof(f68,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_relat_1(X0) = X1 )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( spl6_33
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f163,f158,f83,f199])).

fof(f83,plain,
    ( spl6_10
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f158,plain,
    ( spl6_26
  <=> ! [X5,X7,X4,X6] :
        ( k1_relat_1(X4) = X5
        | ~ v1_partfun1(X4,X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
        | ~ v1_relat_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_partfun1(X0,X1)
        | k1_relat_1(X0) = X1 )
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(condensation,[],[f161])).

fof(f161,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_relat_1(X0) = X1 )
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(resolution,[],[f159,f84])).

fof(f84,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f159,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_relat_1(X7)
        | ~ v1_partfun1(X4,X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
        | k1_relat_1(X4) = X5 )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f158])).

fof(f197,plain,
    ( ~ spl6_31
    | spl6_32
    | ~ spl6_13
    | spl6_29 ),
    inference(avatar_split_clause,[],[f190,f178,f95,f195,f192])).

fof(f95,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f178,plain,
    ( spl6_29
  <=> r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f190,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | ~ spl6_13
    | spl6_29 ),
    inference(resolution,[],[f179,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f179,plain,
    ( ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f178])).

fof(f189,plain,
    ( ~ spl6_8
    | ~ spl6_15
    | spl6_30 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_15
    | spl6_30 ),
    inference(unit_resulting_resolution,[],[f76,f182,f104])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f182,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_30
  <=> v5_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f186,plain,
    ( ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | spl6_28 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | spl6_28 ),
    inference(unit_resulting_resolution,[],[f84,f76,f176,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f176,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_28
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f183,plain,
    ( ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_1
    | ~ spl6_18
    | spl6_27 ),
    inference(avatar_split_clause,[],[f173,f168,f116,f47,f181,f178,f175])).

fof(f47,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f116,plain,
    ( spl6_18
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f168,plain,
    ( spl6_27
  <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f173,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl6_1
    | ~ spl6_18
    | spl6_27 ),
    inference(subsumption_resolution,[],[f172,f48])).

fof(f48,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f172,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl6_18
    | spl6_27 ),
    inference(trivial_inequality_removal,[],[f171])).

fof(f171,plain,
    ( k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl6_18
    | spl6_27 ),
    inference(superposition,[],[f169,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f116])).

fof(f169,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( ~ spl6_27
    | ~ spl6_5
    | spl6_11
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f166,f154,f87,f63,f168])).

fof(f87,plain,
    ( spl6_11
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f154,plain,
    ( spl6_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f166,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_5
    | spl6_11
    | ~ spl6_25 ),
    inference(backward_demodulation,[],[f88,f165])).

fof(f165,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_5
    | ~ spl6_25 ),
    inference(resolution,[],[f155,f64])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f154])).

fof(f88,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f160,plain,
    ( spl6_26
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f128,f120,f91,f158])).

fof(f120,plain,
    ( spl6_19
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f128,plain,
    ( ! [X6,X4,X7,X5] :
        ( k1_relat_1(X4) = X5
        | ~ v1_partfun1(X4,X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
        | ~ v1_relat_1(X7) )
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(resolution,[],[f121,f92])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f156,plain,
    ( spl6_25
    | ~ spl6_8
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f152,f149,f75,f154])).

fof(f149,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_8
    | ~ spl6_24 ),
    inference(resolution,[],[f150,f76])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1)) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl6_24
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f147,f143,f67,f47,f149])).

fof(f143,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1)) )
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(X1,sK1)
        | ~ v1_funct_1(sK4)
        | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1)) )
    | ~ spl6_6
    | ~ spl6_23 ),
    inference(resolution,[],[f144,f68])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_funct_1(X0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl6_23
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f141,f130,f79,f71,f59,f55,f51,f143])).

fof(f130,plain,
    ( spl6_21
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(X5,X1)
        | ~ v1_partfun1(X4,X0)
        | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f140,f80])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_7
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f139,f60])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f138,f52])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(sK3)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | spl6_3
    | ~ spl6_7
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK1)
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_7
    | ~ spl6_21 ),
    inference(resolution,[],[f131,f72])).

fof(f131,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_2(X3,X1,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_1(X3)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(X5,X1)
        | ~ v1_partfun1(X4,X0)
        | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f35,f130])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X1)
      | ~ v1_partfun1(X4,X0)
      | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

fof(f126,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f44,f124])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f122,plain,
    ( spl6_19
    | ~ spl6_14
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f114,f111,f99,f120])).

fof(f99,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f111,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl6_14
    | ~ spl6_17 ),
    inference(resolution,[],[f112,f100])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f39,f116])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
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
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f113,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f41,f111])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f105,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f43,f103])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f101,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f38,f95])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f93,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f89,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f27,f87])).

fof(f27,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f85,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f81,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f28,f47])).

fof(f28,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (3665)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.45  % (3656)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.45  % (3663)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.45  % (3665)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (3661)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f247,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f65,f69,f73,f77,f81,f85,f89,f93,f97,f101,f105,f113,f118,f122,f126,f132,f145,f151,f156,f160,f170,f183,f186,f189,f197,f201,f214,f226,f235,f241,f246])).
% 0.20/0.46  fof(f246,plain,(
% 0.20/0.46    spl6_4 | ~spl6_32 | ~spl6_35),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f245])).
% 0.20/0.46  fof(f245,plain,(
% 0.20/0.46    $false | (spl6_4 | ~spl6_32 | ~spl6_35)),
% 0.20/0.46    inference(subsumption_resolution,[],[f244,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ~v1_xboole_0(sK0) | spl6_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl6_4 <=> v1_xboole_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.46  fof(f244,plain,(
% 0.20/0.46    v1_xboole_0(sK0) | (~spl6_32 | ~spl6_35)),
% 0.20/0.46    inference(forward_demodulation,[],[f196,f210])).
% 0.20/0.46  fof(f210,plain,(
% 0.20/0.46    sK0 = k1_relat_1(sK4) | ~spl6_35),
% 0.20/0.46    inference(avatar_component_clause,[],[f209])).
% 0.20/0.46  fof(f209,plain,(
% 0.20/0.46    spl6_35 <=> sK0 = k1_relat_1(sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.46  fof(f196,plain,(
% 0.20/0.46    v1_xboole_0(k1_relat_1(sK4)) | ~spl6_32),
% 0.20/0.46    inference(avatar_component_clause,[],[f195])).
% 0.20/0.46  fof(f195,plain,(
% 0.20/0.46    spl6_32 <=> v1_xboole_0(k1_relat_1(sK4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.46  fof(f241,plain,(
% 0.20/0.46    ~spl6_8 | ~spl6_36),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.46  fof(f238,plain,(
% 0.20/0.46    $false | (~spl6_8 | ~spl6_36)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f76,f213])).
% 0.20/0.46  fof(f213,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl6_36),
% 0.20/0.46    inference(avatar_component_clause,[],[f212])).
% 0.20/0.46  fof(f212,plain,(
% 0.20/0.46    spl6_36 <=> ! [X0] : ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.46  fof(f235,plain,(
% 0.20/0.46    ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_20 | spl6_38),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.46  fof(f234,plain,(
% 0.20/0.46    $false | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_20 | spl6_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f233,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ~v1_xboole_0(sK1) | spl6_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl6_3 <=> v1_xboole_0(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.46  fof(f233,plain,(
% 0.20/0.46    v1_xboole_0(sK1) | (~spl6_2 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_20 | spl6_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f232,f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.46  fof(f232,plain,(
% 0.20/0.46    ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_7 | ~spl6_9 | ~spl6_20 | spl6_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f231,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.46  fof(f231,plain,(
% 0.20/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_7 | ~spl6_20 | spl6_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f230,f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    v1_funct_2(sK3,sK1,sK0) | ~spl6_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.46  fof(f230,plain,(
% 0.20/0.46    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_20 | spl6_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f228,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    v1_funct_1(sK3) | ~spl6_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    spl6_2 <=> v1_funct_1(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.46  fof(f228,plain,(
% 0.20/0.46    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_20 | spl6_38)),
% 0.20/0.46    inference(resolution,[],[f225,f125])).
% 0.20/0.46  fof(f125,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) ) | ~spl6_20),
% 0.20/0.46    inference(avatar_component_clause,[],[f124])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    spl6_20 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.46  fof(f225,plain,(
% 0.20/0.46    ~m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0) | spl6_38),
% 0.20/0.46    inference(avatar_component_clause,[],[f224])).
% 0.20/0.46  fof(f224,plain,(
% 0.20/0.46    spl6_38 <=> m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.20/0.46  fof(f226,plain,(
% 0.20/0.46    ~spl6_38 | spl6_31 | ~spl6_35),
% 0.20/0.46    inference(avatar_split_clause,[],[f215,f209,f192,f224])).
% 0.20/0.46  fof(f192,plain,(
% 0.20/0.46    spl6_31 <=> m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.46  fof(f215,plain,(
% 0.20/0.46    ~m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0) | (spl6_31 | ~spl6_35)),
% 0.20/0.46    inference(backward_demodulation,[],[f193,f210])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    ~m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | spl6_31),
% 0.20/0.46    inference(avatar_component_clause,[],[f192])).
% 0.20/0.46  fof(f214,plain,(
% 0.20/0.46    spl6_35 | spl6_36 | ~spl6_6 | ~spl6_33),
% 0.20/0.46    inference(avatar_split_clause,[],[f206,f199,f67,f212,f209])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    spl6_33 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.46  fof(f206,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK0 = k1_relat_1(sK4)) ) | (~spl6_6 | ~spl6_33)),
% 0.20/0.46    inference(resolution,[],[f200,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    v1_partfun1(sK4,sK0) | ~spl6_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f200,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(X0) = X1) ) | ~spl6_33),
% 0.20/0.46    inference(avatar_component_clause,[],[f199])).
% 0.20/0.46  fof(f201,plain,(
% 0.20/0.46    spl6_33 | ~spl6_10 | ~spl6_26),
% 0.20/0.46    inference(avatar_split_clause,[],[f163,f158,f83,f199])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    spl6_10 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.46  fof(f158,plain,(
% 0.20/0.46    spl6_26 <=> ! [X5,X7,X4,X6] : (k1_relat_1(X4) = X5 | ~v1_partfun1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | ~v1_relat_1(X7))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.46  fof(f163,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1) ) | (~spl6_10 | ~spl6_26)),
% 0.20/0.46    inference(condensation,[],[f161])).
% 0.20/0.46  fof(f161,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_relat_1(X0) = X1) ) | (~spl6_10 | ~spl6_26)),
% 0.20/0.46    inference(resolution,[],[f159,f84])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl6_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f83])).
% 0.20/0.46  fof(f159,plain,(
% 0.20/0.46    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X7) | ~v1_partfun1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | k1_relat_1(X4) = X5) ) | ~spl6_26),
% 0.20/0.46    inference(avatar_component_clause,[],[f158])).
% 0.20/0.46  fof(f197,plain,(
% 0.20/0.46    ~spl6_31 | spl6_32 | ~spl6_13 | spl6_29),
% 0.20/0.46    inference(avatar_split_clause,[],[f190,f178,f95,f195,f192])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    spl6_13 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    spl6_29 <=> r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.46  fof(f190,plain,(
% 0.20/0.46    v1_xboole_0(k1_relat_1(sK4)) | ~m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | (~spl6_13 | spl6_29)),
% 0.20/0.46    inference(resolution,[],[f179,f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl6_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f95])).
% 0.20/0.46  fof(f179,plain,(
% 0.20/0.46    ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | spl6_29),
% 0.20/0.46    inference(avatar_component_clause,[],[f178])).
% 0.20/0.46  fof(f189,plain,(
% 0.20/0.46    ~spl6_8 | ~spl6_15 | spl6_30),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.46  fof(f187,plain,(
% 0.20/0.46    $false | (~spl6_8 | ~spl6_15 | spl6_30)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f76,f182,f104])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f103])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    spl6_15 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.46  fof(f182,plain,(
% 0.20/0.46    ~v5_relat_1(sK4,sK2) | spl6_30),
% 0.20/0.46    inference(avatar_component_clause,[],[f181])).
% 0.20/0.46  fof(f181,plain,(
% 0.20/0.46    spl6_30 <=> v5_relat_1(sK4,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.46  fof(f186,plain,(
% 0.20/0.46    ~spl6_8 | ~spl6_10 | ~spl6_12 | spl6_28),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f184])).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    $false | (~spl6_8 | ~spl6_10 | ~spl6_12 | spl6_28)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f84,f76,f176,f92])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl6_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f91])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    spl6_12 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.46  fof(f176,plain,(
% 0.20/0.46    ~v1_relat_1(sK4) | spl6_28),
% 0.20/0.46    inference(avatar_component_clause,[],[f175])).
% 0.20/0.46  fof(f175,plain,(
% 0.20/0.46    spl6_28 <=> v1_relat_1(sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.46  fof(f183,plain,(
% 0.20/0.46    ~spl6_28 | ~spl6_29 | ~spl6_30 | ~spl6_1 | ~spl6_18 | spl6_27),
% 0.20/0.46    inference(avatar_split_clause,[],[f173,f168,f116,f47,f181,f178,f175])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl6_1 <=> v1_funct_1(sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    spl6_18 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.46  fof(f168,plain,(
% 0.20/0.46    spl6_27 <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    ~v5_relat_1(sK4,sK2) | ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl6_1 | ~spl6_18 | spl6_27)),
% 0.20/0.46    inference(subsumption_resolution,[],[f172,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    v1_funct_1(sK4) | ~spl6_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f47])).
% 0.20/0.46  fof(f172,plain,(
% 0.20/0.46    ~v5_relat_1(sK4,sK2) | ~v1_funct_1(sK4) | ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl6_18 | spl6_27)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f171])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v5_relat_1(sK4,sK2) | ~v1_funct_1(sK4) | ~r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl6_18 | spl6_27)),
% 0.20/0.46    inference(superposition,[],[f169,f117])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl6_18),
% 0.20/0.46    inference(avatar_component_clause,[],[f116])).
% 0.20/0.46  fof(f169,plain,(
% 0.20/0.46    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | spl6_27),
% 0.20/0.46    inference(avatar_component_clause,[],[f168])).
% 0.20/0.46  fof(f170,plain,(
% 0.20/0.46    ~spl6_27 | ~spl6_5 | spl6_11 | ~spl6_25),
% 0.20/0.46    inference(avatar_split_clause,[],[f166,f154,f87,f63,f168])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    spl6_11 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.46  fof(f154,plain,(
% 0.20/0.46    spl6_25 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.46  fof(f166,plain,(
% 0.20/0.46    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_5 | spl6_11 | ~spl6_25)),
% 0.20/0.46    inference(backward_demodulation,[],[f88,f165])).
% 0.20/0.46  fof(f165,plain,(
% 0.20/0.46    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_5 | ~spl6_25)),
% 0.20/0.46    inference(resolution,[],[f155,f64])).
% 0.20/0.46  fof(f155,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | ~spl6_25),
% 0.20/0.46    inference(avatar_component_clause,[],[f154])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | spl6_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f87])).
% 0.20/0.46  fof(f160,plain,(
% 0.20/0.46    spl6_26 | ~spl6_12 | ~spl6_19),
% 0.20/0.46    inference(avatar_split_clause,[],[f128,f120,f91,f158])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    spl6_19 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.46  fof(f128,plain,(
% 0.20/0.46    ( ! [X6,X4,X7,X5] : (k1_relat_1(X4) = X5 | ~v1_partfun1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | ~v1_relat_1(X7)) ) | (~spl6_12 | ~spl6_19)),
% 0.20/0.46    inference(resolution,[],[f121,f92])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl6_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f120])).
% 0.20/0.46  fof(f156,plain,(
% 0.20/0.46    spl6_25 | ~spl6_8 | ~spl6_24),
% 0.20/0.46    inference(avatar_split_clause,[],[f152,f149,f75,f154])).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    spl6_24 <=> ! [X1,X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_8 | ~spl6_24)),
% 0.20/0.46    inference(resolution,[],[f150,f76])).
% 0.20/0.46  fof(f150,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1))) ) | ~spl6_24),
% 0.20/0.46    inference(avatar_component_clause,[],[f149])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    spl6_24 | ~spl6_1 | ~spl6_6 | ~spl6_23),
% 0.20/0.46    inference(avatar_split_clause,[],[f147,f143,f67,f47,f149])).
% 0.20/0.46  fof(f143,plain,(
% 0.20/0.46    spl6_23 <=> ! [X1,X0,X2] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.46  fof(f147,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1))) ) | (~spl6_1 | ~spl6_6 | ~spl6_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f146,f48])).
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(X1,sK1) | ~v1_funct_1(sK4) | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1))) ) | (~spl6_6 | ~spl6_23)),
% 0.20/0.46    inference(resolution,[],[f144,f68])).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_partfun1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_funct_1(X0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | ~spl6_23),
% 0.20/0.46    inference(avatar_component_clause,[],[f143])).
% 0.20/0.46  fof(f145,plain,(
% 0.20/0.46    spl6_23 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_21),
% 0.20/0.46    inference(avatar_split_clause,[],[f141,f130,f79,f71,f59,f55,f51,f143])).
% 0.20/0.46  fof(f130,plain,(
% 0.20/0.46    spl6_21 <=> ! [X1,X3,X5,X0,X2,X4] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X1) | ~v1_partfun1(X4,X0) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.46  fof(f141,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (~spl6_2 | spl6_3 | spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_21)),
% 0.20/0.46    inference(subsumption_resolution,[],[f140,f80])).
% 0.20/0.46  fof(f140,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (~spl6_2 | spl6_3 | spl6_4 | ~spl6_7 | ~spl6_21)),
% 0.20/0.46    inference(subsumption_resolution,[],[f139,f60])).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_21)),
% 0.20/0.46    inference(subsumption_resolution,[],[f138,f52])).
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(sK3) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (spl6_3 | ~spl6_7 | ~spl6_21)),
% 0.20/0.46    inference(subsumption_resolution,[],[f137,f56])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v1_xboole_0(sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (~spl6_7 | ~spl6_21)),
% 0.20/0.46    inference(resolution,[],[f131,f72])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X3,X1,X0) | v1_xboole_0(X1) | ~v1_funct_1(X3) | v1_xboole_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X1) | ~v1_partfun1(X4,X0) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))) ) | ~spl6_21),
% 0.20/0.46    inference(avatar_component_clause,[],[f130])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    spl6_21),
% 0.20/0.46    inference(avatar_split_clause,[],[f35,f130])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X1) | ~v1_partfun1(X4,X0) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    spl6_20),
% 0.20/0.46    inference(avatar_split_clause,[],[f44,f124])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    spl6_19 | ~spl6_14 | ~spl6_17),
% 0.20/0.46    inference(avatar_split_clause,[],[f114,f111,f99,f120])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    spl6_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    spl6_17 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | (~spl6_14 | ~spl6_17)),
% 0.20/0.46    inference(resolution,[],[f112,f100])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f99])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) ) | ~spl6_17),
% 0.20/0.46    inference(avatar_component_clause,[],[f111])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    spl6_18),
% 0.20/0.46    inference(avatar_split_clause,[],[f39,f116])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    spl6_17),
% 0.20/0.46    inference(avatar_split_clause,[],[f41,f111])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    spl6_15),
% 0.20/0.46    inference(avatar_split_clause,[],[f43,f103])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    spl6_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f42,f99])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    spl6_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f38,f95])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    spl6_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f36,f91])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    ~spl6_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f87])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    spl6_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f37,f83])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl6_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f32,f79])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    spl6_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f29,f75])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    spl6_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f31,f71])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl6_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f67])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    v1_partfun1(sK4,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl6_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f63])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    m1_subset_1(sK5,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ~spl6_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f34,f59])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ~v1_xboole_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ~spl6_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f33,f55])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ~v1_xboole_0(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl6_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f30,f51])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    v1_funct_1(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl6_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f47])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    v1_funct_1(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (3665)------------------------------
% 0.20/0.46  % (3665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (3665)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (3665)Memory used [KB]: 10746
% 0.20/0.46  % (3665)Time elapsed: 0.044 s
% 0.20/0.46  % (3665)------------------------------
% 0.20/0.46  % (3665)------------------------------
% 0.20/0.46  % (3655)Success in time 0.113 s
%------------------------------------------------------------------------------
