%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 266 expanded)
%              Number of leaves         :   49 ( 127 expanded)
%              Depth                    :    8
%              Number of atoms          :  439 ( 682 expanded)
%              Number of equality atoms :   94 ( 160 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f79,f83,f87,f91,f107,f111,f115,f119,f123,f131,f139,f150,f155,f159,f163,f171,f182,f186,f197,f215,f221,f231,f252,f268,f276,f309,f316,f342,f352])).

fof(f352,plain,
    ( ~ spl2_3
    | ~ spl2_34
    | spl2_43
    | ~ spl2_47 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_34
    | spl2_43
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f315,f344])).

fof(f344,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_34
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f251,f78,f341])).

fof(f341,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v4_relat_1(k6_relat_1(X2),X3) )
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl2_47
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v4_relat_1(k6_relat_1(X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f78,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f251,plain,
    ( v4_relat_1(k6_relat_1(sK1),sK0)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl2_34
  <=> v4_relat_1(k6_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f315,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_43 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl2_43
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f342,plain,
    ( spl2_47
    | ~ spl2_11
    | ~ spl2_37
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f279,f274,f266,f109,f340])).

fof(f109,plain,
    ( spl2_11
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f266,plain,
    ( spl2_37
  <=> ! [X1,X0] :
        ( k9_relat_1(X0,X1) = k2_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f274,plain,
    ( spl2_38
  <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f279,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v4_relat_1(k6_relat_1(X2),X3) )
    | ~ spl2_11
    | ~ spl2_37
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f277,f110])).

fof(f110,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f277,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = k2_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v4_relat_1(k6_relat_1(X2),X3) )
    | ~ spl2_37
    | ~ spl2_38 ),
    inference(superposition,[],[f275,f267])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X0,X1) = k2_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) )
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f266])).

fof(f275,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f274])).

fof(f316,plain,
    ( ~ spl2_43
    | spl2_29
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f310,f307,f212,f313])).

fof(f212,plain,
    ( spl2_29
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f307,plain,
    ( spl2_42
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f310,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_29
    | ~ spl2_42 ),
    inference(superposition,[],[f214,f308])).

fof(f308,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f307])).

fof(f214,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | spl2_29 ),
    inference(avatar_component_clause,[],[f212])).

fof(f309,plain,
    ( spl2_42
    | ~ spl2_18
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f234,f229,f137,f307])).

fof(f137,plain,
    ( spl2_18
  <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f229,plain,
    ( spl2_31
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f234,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_18
    | ~ spl2_31 ),
    inference(superposition,[],[f230,f138])).

fof(f138,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f230,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f229])).

fof(f276,plain,
    ( spl2_38
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f201,f184,f180,f148,f113,f105,f85,f81,f77,f274])).

fof(f81,plain,
    ( spl2_4
  <=> ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f85,plain,
    ( spl2_5
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f105,plain,
    ( spl2_10
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f113,plain,
    ( spl2_12
  <=> ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f148,plain,
    ( spl2_19
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f180,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f184,plain,
    ( spl2_26
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
        | ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f201,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f200,f191])).

% (9898)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f191,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f190,f106])).

fof(f106,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f190,plain,
    ( ! [X0,X1] : k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f189,f149])).

fof(f149,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f189,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f187,f106])).

fof(f187,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f78,f78,f181])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f180])).

fof(f200,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f198,f114])).

fof(f114,plain,
    ( ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f198,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f78,f86,f82,f185])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
        | ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f184])).

fof(f82,plain,
    ( ! [X0] : v2_funct_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f86,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f268,plain,
    ( spl2_37
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f175,f161,f157,f266])).

fof(f157,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f161,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X0,X1) = k2_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1) )
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X0,X1) = k2_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v4_relat_1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(superposition,[],[f158,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f161])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f252,plain,
    ( spl2_34
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_20
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f177,f169,f152,f89,f77,f249])).

fof(f89,plain,
    ( spl2_6
  <=> ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f152,plain,
    ( spl2_20
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f169,plain,
    ( spl2_24
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X1)
        | ~ v4_relat_1(X2,X0)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f177,plain,
    ( v4_relat_1(k6_relat_1(sK1),sK0)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_20
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f154,f78,f90,f170])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_relat_1(X2,X0)
        | v4_relat_1(X2,X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f169])).

fof(f90,plain,
    ( ! [X0] : v4_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f154,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f231,plain,
    ( spl2_31
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f145,f137,f117,f229])).

fof(f117,plain,
    ( spl2_13
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f145,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(superposition,[],[f138,f118])).

fof(f118,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f221,plain,
    ( ~ spl2_16
    | spl2_28 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl2_16
    | spl2_28 ),
    inference(unit_resulting_resolution,[],[f130,f210])).

fof(f210,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_28 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl2_28
  <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f130,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl2_16
  <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f215,plain,
    ( ~ spl2_28
    | ~ spl2_29
    | spl2_2
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f206,f195,f180,f148,f105,f77,f72,f212,f208])).

fof(f72,plain,
    ( spl2_2
  <=> sK1 = k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f195,plain,
    ( spl2_27
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f206,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f204,f191])).

fof(f204,plain,
    ( sK1 != k10_relat_1(k6_relat_1(sK0),sK1)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_2
    | ~ spl2_27 ),
    inference(superposition,[],[f74,f196])).

fof(f196,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f195])).

fof(f74,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f197,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f62,f195])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f186,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f57,f184])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f182,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f50,f180])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f171,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f56,f169])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f163,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f58,f161])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f159,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f55,f157])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f155,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f140,f121,f67,f152])).

fof(f67,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f121,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f140,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f69,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f150,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f54,f148])).

fof(f54,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f139,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f53,f137])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f131,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f64,f129])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f47,f37])).

fof(f37,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f123,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f59,f121])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f119,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f51,f117])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f115,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f38,f113])).

fof(f38,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(f111,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f49,f109])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f107,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f48,f105])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f91,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f44,f89])).

fof(f44,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f87,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f42,f85])).

fof(f42,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f83,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f79,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f63,f72])).

fof(f63,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f36,f37])).

fof(f36,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f70,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (9879)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (9883)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (9894)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (9886)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (9889)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (9880)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (9891)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (9886)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (9887)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (9888)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (9893)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f354,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f70,f75,f79,f83,f87,f91,f107,f111,f115,f119,f123,f131,f139,f150,f155,f159,f163,f171,f182,f186,f197,f215,f221,f231,f252,f268,f276,f309,f316,f342,f352])).
% 0.20/0.49  fof(f352,plain,(
% 0.20/0.49    ~spl2_3 | ~spl2_34 | spl2_43 | ~spl2_47),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f351])).
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    $false | (~spl2_3 | ~spl2_34 | spl2_43 | ~spl2_47)),
% 0.20/0.49    inference(subsumption_resolution,[],[f315,f344])).
% 0.20/0.49  fof(f344,plain,(
% 0.20/0.49    sK1 = k3_xboole_0(sK0,sK1) | (~spl2_3 | ~spl2_34 | ~spl2_47)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f251,f78,f341])).
% 0.20/0.49  fof(f341,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~v1_relat_1(k6_relat_1(X2)) | ~v4_relat_1(k6_relat_1(X2),X3)) ) | ~spl2_47),
% 0.20/0.49    inference(avatar_component_clause,[],[f340])).
% 0.20/0.49  fof(f340,plain,(
% 0.20/0.49    spl2_47 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~v1_relat_1(k6_relat_1(X2)) | ~v4_relat_1(k6_relat_1(X2),X3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    v4_relat_1(k6_relat_1(sK1),sK0) | ~spl2_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f249])).
% 0.20/0.49  fof(f249,plain,(
% 0.20/0.49    spl2_34 <=> v4_relat_1(k6_relat_1(sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    sK1 != k3_xboole_0(sK0,sK1) | spl2_43),
% 0.20/0.49    inference(avatar_component_clause,[],[f313])).
% 0.20/0.49  fof(f313,plain,(
% 0.20/0.49    spl2_43 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.49  fof(f342,plain,(
% 0.20/0.49    spl2_47 | ~spl2_11 | ~spl2_37 | ~spl2_38),
% 0.20/0.49    inference(avatar_split_clause,[],[f279,f274,f266,f109,f340])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl2_11 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    spl2_37 <=> ! [X1,X0] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    spl2_38 <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~v1_relat_1(k6_relat_1(X2)) | ~v4_relat_1(k6_relat_1(X2),X3)) ) | (~spl2_11 | ~spl2_37 | ~spl2_38)),
% 0.20/0.49    inference(forward_demodulation,[],[f277,f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f109])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k2_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2)) | ~v4_relat_1(k6_relat_1(X2),X3)) ) | (~spl2_37 | ~spl2_38)),
% 0.20/0.49    inference(superposition,[],[f275,f267])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) ) | ~spl2_37),
% 0.20/0.49    inference(avatar_component_clause,[],[f266])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f274])).
% 0.20/0.49  fof(f316,plain,(
% 0.20/0.49    ~spl2_43 | spl2_29 | ~spl2_42),
% 0.20/0.49    inference(avatar_split_clause,[],[f310,f307,f212,f313])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    spl2_29 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    spl2_42 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.20/0.49  fof(f310,plain,(
% 0.20/0.49    sK1 != k3_xboole_0(sK0,sK1) | (spl2_29 | ~spl2_42)),
% 0.20/0.49    inference(superposition,[],[f214,f308])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl2_42),
% 0.20/0.49    inference(avatar_component_clause,[],[f307])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    sK1 != k3_xboole_0(sK1,sK0) | spl2_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f212])).
% 0.20/0.49  fof(f309,plain,(
% 0.20/0.49    spl2_42 | ~spl2_18 | ~spl2_31),
% 0.20/0.49    inference(avatar_split_clause,[],[f234,f229,f137,f307])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl2_18 <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.49  fof(f229,plain,(
% 0.20/0.49    spl2_31 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_18 | ~spl2_31)),
% 0.20/0.49    inference(superposition,[],[f230,f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl2_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f137])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f229])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    spl2_38 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_10 | ~spl2_12 | ~spl2_19 | ~spl2_25 | ~spl2_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f201,f184,f180,f148,f113,f105,f85,f81,f77,f274])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl2_4 <=> ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl2_5 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl2_10 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl2_12 <=> ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    spl2_19 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl2_25 <=> ! [X1,X0] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    spl2_26 <=> ! [X1,X0] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_10 | ~spl2_12 | ~spl2_19 | ~spl2_25 | ~spl2_26)),
% 0.20/0.49    inference(forward_demodulation,[],[f200,f191])).
% 0.20/0.49  % (9898)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_10 | ~spl2_19 | ~spl2_25)),
% 0.20/0.49    inference(forward_demodulation,[],[f190,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_10 | ~spl2_19 | ~spl2_25)),
% 0.20/0.49    inference(forward_demodulation,[],[f189,f149])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f148])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_10 | ~spl2_25)),
% 0.20/0.49    inference(forward_demodulation,[],[f187,f106])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) ) | (~spl2_3 | ~spl2_25)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f78,f78,f181])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f180])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_12 | ~spl2_26)),
% 0.20/0.49    inference(forward_demodulation,[],[f198,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) ) | ~spl2_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f113])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)) ) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_26)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f78,f86,f82,f185])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl2_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f184])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl2_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    spl2_37 | ~spl2_21 | ~spl2_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f175,f161,f157,f266])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl2_21 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    spl2_22 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) ) | (~spl2_21 | ~spl2_22)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f174])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) ) | (~spl2_21 | ~spl2_22)),
% 0.20/0.49    inference(superposition,[],[f158,f162])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl2_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f161])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl2_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f157])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    spl2_34 | ~spl2_3 | ~spl2_6 | ~spl2_20 | ~spl2_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f177,f169,f152,f89,f77,f249])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl2_6 <=> ! [X0] : v4_relat_1(k6_relat_1(X0),X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl2_20 <=> r1_tarski(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    spl2_24 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    v4_relat_1(k6_relat_1(sK1),sK0) | (~spl2_3 | ~spl2_6 | ~spl2_20 | ~spl2_24)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f154,f78,f90,f170])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) ) | ~spl2_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f169])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f89])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    r1_tarski(sK1,sK0) | ~spl2_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f152])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    spl2_31 | ~spl2_13 | ~spl2_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f145,f137,f117,f229])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl2_13 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_13 | ~spl2_18)),
% 0.20/0.49    inference(superposition,[],[f138,f118])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f117])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    ~spl2_16 | spl2_28),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f216])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    $false | (~spl2_16 | spl2_28)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f130,f210])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl2_28),
% 0.20/0.49    inference(avatar_component_clause,[],[f208])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    spl2_28 <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl2_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f129])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl2_16 <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    ~spl2_28 | ~spl2_29 | spl2_2 | ~spl2_3 | ~spl2_10 | ~spl2_19 | ~spl2_25 | ~spl2_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f206,f195,f180,f148,f105,f77,f72,f212,f208])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl2_2 <=> sK1 = k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl2_27 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    sK1 != k3_xboole_0(sK1,sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_3 | ~spl2_10 | ~spl2_19 | ~spl2_25 | ~spl2_27)),
% 0.20/0.49    inference(forward_demodulation,[],[f204,f191])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    sK1 != k10_relat_1(k6_relat_1(sK0),sK1) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl2_2 | ~spl2_27)),
% 0.20/0.49    inference(superposition,[],[f74,f196])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl2_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f195])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) | spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    spl2_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f62,f195])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    spl2_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f57,f184])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    spl2_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f50,f180])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    spl2_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f56,f169])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    spl2_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f58,f161])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    spl2_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f55,f157])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    spl2_20 | ~spl2_1 | ~spl2_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f140,f121,f67,f152])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl2_14 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    r1_tarski(sK1,sK0) | (~spl2_1 | ~spl2_14)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f69,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f121])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f67])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl2_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f54,f148])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl2_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f53,f137])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl2_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f64,f129])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f47,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,axiom,(
% 0.20/0.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl2_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f59,f121])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl2_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f117])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl2_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f113])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl2_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f49,f109])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl2_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f48,f105])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl2_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f89])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl2_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f85])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl2_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f81])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl2_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f77])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f63,f72])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 0.20/0.49    inference(forward_demodulation,[],[f36,f37])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.20/0.49    inference(negated_conjecture,[],[f20])).
% 0.20/0.49  fof(f20,conjecture,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl2_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f67])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (9886)------------------------------
% 0.20/0.49  % (9886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (9886)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (9886)Memory used [KB]: 6268
% 0.20/0.49  % (9886)Time elapsed: 0.058 s
% 0.20/0.49  % (9886)------------------------------
% 0.20/0.49  % (9886)------------------------------
% 0.20/0.49  % (9876)Success in time 0.13 s
%------------------------------------------------------------------------------
