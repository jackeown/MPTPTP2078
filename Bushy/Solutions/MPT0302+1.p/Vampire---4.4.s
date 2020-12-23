%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t114_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:58 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 309 expanded)
%              Number of leaves         :   34 ( 122 expanded)
%              Depth                    :    7
%              Number of atoms          :  379 ( 782 expanded)
%              Number of equality atoms :   52 ( 199 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f47,f54,f61,f68,f93,f98,f112,f116,f130,f135,f137,f150,f154,f168,f173,f187,f191,f196,f198,f199,f212,f217,f226,f233,f243,f245,f250,f256,f258])).

fof(f258,plain,
    ( spl4_3
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f252,f46])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f252,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_34 ),
    inference(resolution,[],[f208,f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t114_zfmisc_1.p',t7_xboole_0)).

fof(f208,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl4_34
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f256,plain,
    ( ~ spl4_22
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(resolution,[],[f208,f140])).

fof(f140,plain,
    ( r2_hidden(sK3(sK1,k1_xboole_0),sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_22
  <=> r2_hidden(sK3(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f250,plain,
    ( spl4_1
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f246,f39])).

fof(f39,plain,
    ( k1_xboole_0 != sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f246,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_38 ),
    inference(resolution,[],[f222,f25])).

fof(f222,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_38
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f245,plain,
    ( ~ spl4_30
    | spl4_33
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl4_30
    | ~ spl4_33
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f240,f186])).

fof(f186,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl4_33
  <=> ~ r2_hidden(sK3(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f240,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | ~ spl4_30
    | ~ spl4_40 ),
    inference(resolution,[],[f225,f177])).

fof(f177,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_30
  <=> r2_hidden(sK3(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl4_40
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f243,plain,
    ( spl4_27
    | ~ spl4_28
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl4_27
    | ~ spl4_28
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f238,f161])).

fof(f161,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_27
  <=> ~ r2_hidden(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f238,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl4_28
    | ~ spl4_40 ),
    inference(resolution,[],[f225,f164])).

fof(f164,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl4_28
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f233,plain,
    ( ~ spl4_43
    | spl4_21
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f213,f210,f128,f231])).

fof(f231,plain,
    ( spl4_43
  <=> ~ r2_hidden(sK3(k1_xboole_0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f128,plain,
    ( spl4_21
  <=> ~ r2_hidden(sK3(k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f210,plain,
    ( spl4_36
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f213,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK1),sK0)
    | ~ spl4_21
    | ~ spl4_36 ),
    inference(resolution,[],[f211,f129])).

fof(f129,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK1),sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f128])).

fof(f211,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f210])).

fof(f226,plain,
    ( spl4_38
    | spl4_40
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f201,f59,f224,f221])).

fof(f59,plain,
    ( spl4_6
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t114_zfmisc_1.p',l54_zfmisc_1)).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X1,sK0) )
    | ~ spl4_6 ),
    inference(superposition,[],[f32,f60])).

fof(f60,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f217,plain,
    ( ~ spl4_26
    | spl4_29
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl4_26
    | ~ spl4_29
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f214,f158])).

fof(f158,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_26
  <=> r2_hidden(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f214,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl4_29
    | ~ spl4_36 ),
    inference(resolution,[],[f211,f167])).

fof(f167,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl4_29
  <=> ~ r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f212,plain,
    ( spl4_34
    | spl4_36
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f200,f59,f210,f207])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f69,f33])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl4_6 ),
    inference(superposition,[],[f31,f60])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f199,plain,
    ( spl4_26
    | spl4_5
    | spl4_29 ),
    inference(avatar_split_clause,[],[f174,f166,f52,f157])).

fof(f52,plain,
    ( spl4_5
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f174,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl4_5
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f170,f53])).

fof(f53,plain,
    ( sK0 != sK1
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f170,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | sK0 = sK1
    | ~ spl4_29 ),
    inference(resolution,[],[f167,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t114_zfmisc_1.p',t2_tarski)).

fof(f198,plain,
    ( spl4_18
    | spl4_3
    | spl4_21 ),
    inference(avatar_split_clause,[],[f136,f128,f45,f119])).

fof(f119,plain,
    ( spl4_18
  <=> r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f136,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f132,f46])).

fof(f132,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl4_21 ),
    inference(resolution,[],[f129,f29])).

fof(f196,plain,
    ( spl4_16
    | spl4_1
    | spl4_15 ),
    inference(avatar_split_clause,[],[f117,f104,f38,f107])).

fof(f107,plain,
    ( spl4_16
  <=> r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f104,plain,
    ( spl4_15
  <=> ~ r2_hidden(sK3(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f117,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f113,f39])).

fof(f113,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl4_15 ),
    inference(resolution,[],[f105,f29])).

fof(f105,plain,
    ( ~ r2_hidden(sK3(sK0,k1_xboole_0),sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f191,plain,
    ( spl4_5
    | spl4_31
    | spl4_33 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f189,f53])).

fof(f189,plain,
    ( sK0 = sK1
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f188,f186])).

fof(f188,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | sK0 = sK1
    | ~ spl4_31 ),
    inference(resolution,[],[f180,f29])).

fof(f180,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK1)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_31
  <=> ~ r2_hidden(sK3(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f187,plain,
    ( ~ spl4_31
    | ~ spl4_33
    | spl4_5 ),
    inference(avatar_split_clause,[],[f77,f52,f185,f179])).

fof(f77,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | ~ r2_hidden(sK3(sK1,sK0),sK1)
    | ~ spl4_5 ),
    inference(extensionality_resolution,[],[f30,f53])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f173,plain,
    ( spl4_5
    | spl4_27
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_27
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f171,f53])).

fof(f171,plain,
    ( sK0 = sK1
    | ~ spl4_27
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f170,f161])).

fof(f168,plain,
    ( ~ spl4_27
    | ~ spl4_29
    | spl4_5 ),
    inference(avatar_split_clause,[],[f76,f52,f166,f160])).

fof(f76,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl4_5 ),
    inference(extensionality_resolution,[],[f30,f53])).

fof(f154,plain,
    ( spl4_3
    | spl4_23
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f152,f46])).

fof(f152,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f151,f149])).

fof(f149,plain,
    ( ~ r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_25
  <=> ~ r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f151,plain,
    ( r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl4_23 ),
    inference(resolution,[],[f143,f29])).

fof(f143,plain,
    ( ~ r2_hidden(sK3(sK1,k1_xboole_0),sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_23
  <=> ~ r2_hidden(sK3(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f150,plain,
    ( ~ spl4_23
    | ~ spl4_25
    | spl4_3 ),
    inference(avatar_split_clause,[],[f75,f45,f148,f142])).

fof(f75,plain,
    ( ~ r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK3(sK1,k1_xboole_0),sK1)
    | ~ spl4_3 ),
    inference(extensionality_resolution,[],[f30,f46])).

fof(f137,plain,
    ( spl4_10
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f99,f91,f38,f82])).

fof(f82,plain,
    ( spl4_10
  <=> r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f91,plain,
    ( spl4_13
  <=> ~ r2_hidden(sK3(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f99,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f95,f39])).

fof(f95,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl4_13 ),
    inference(resolution,[],[f92,f29])).

fof(f92,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK0),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f135,plain,
    ( spl4_3
    | spl4_19
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f133,f46])).

fof(f133,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f132,f123])).

fof(f123,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_19
  <=> ~ r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f130,plain,
    ( ~ spl4_19
    | ~ spl4_21
    | spl4_3 ),
    inference(avatar_split_clause,[],[f74,f45,f128,f122])).

fof(f74,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK1),sK1)
    | ~ r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl4_3 ),
    inference(extensionality_resolution,[],[f30,f46])).

fof(f116,plain,
    ( spl4_1
    | spl4_15
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f114,f39])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f113,f111])).

fof(f111,plain,
    ( ~ r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_17
  <=> ~ r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f112,plain,
    ( ~ spl4_15
    | ~ spl4_17
    | spl4_1 ),
    inference(avatar_split_clause,[],[f73,f38,f110,f104])).

fof(f73,plain,
    ( ~ r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK3(sK0,k1_xboole_0),sK0)
    | ~ spl4_1 ),
    inference(extensionality_resolution,[],[f30,f39])).

fof(f98,plain,
    ( spl4_1
    | spl4_11
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f96,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f95,f86])).

fof(f86,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_11
  <=> ~ r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f93,plain,
    ( ~ spl4_11
    | ~ spl4_13
    | spl4_1 ),
    inference(avatar_split_clause,[],[f72,f38,f91,f85])).

fof(f72,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK0),sK0)
    | ~ r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl4_1 ),
    inference(extensionality_resolution,[],[f30,f39])).

fof(f68,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f66,plain,
    ( spl4_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f27,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t114_zfmisc_1.p',d2_xboole_0)).

fof(f61,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t114_zfmisc_1.p',t114_zfmisc_1)).

fof(f54,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
