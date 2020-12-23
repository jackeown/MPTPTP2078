%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 355 expanded)
%              Number of leaves         :   47 ( 174 expanded)
%              Depth                    :    7
%              Number of atoms          :  630 (1447 expanded)
%              Number of equality atoms :   77 ( 147 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f513,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f73,f86,f90,f113,f117,f121,f125,f130,f146,f150,f154,f160,f168,f175,f211,f232,f237,f258,f286,f295,f373,f401,f414,f426,f451,f474,f485,f489,f510,f512])).

fof(f512,plain,
    ( ~ spl8_5
    | ~ spl8_38
    | ~ spl8_52 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_38
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f287,f450])).

fof(f450,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,X0))
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl8_52
  <=> ! [X0] : ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f287,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl8_5
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f68,f285])).

fof(f285,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
        | r2_hidden(k1_mcart_1(X7),k2_zfmisc_1(X4,X5)) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl8_38
  <=> ! [X5,X7,X4,X6] :
        ( ~ r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
        | r2_hidden(k1_mcart_1(X7),k2_zfmisc_1(X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f68,plain,
    ( r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl8_5
  <=> r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f510,plain,
    ( ~ spl8_6
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_33
    | ~ spl8_47 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_33
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f417,f507])).

fof(f507,plain,
    ( ~ r1_xboole_0(sK3,sK3)
    | ~ spl8_14
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f230,f230,f112])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f230,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl8_33
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f417,plain,
    ( r1_xboole_0(sK3,sK3)
    | ~ spl8_6
    | ~ spl8_19
    | ~ spl8_47 ),
    inference(unit_resulting_resolution,[],[f400,f72,f400,f145])).

fof(f145,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X2,X3)
        | ~ r1_xboole_0(X1,X3)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f144])).

% (6963)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f144,plain,
    ( spl8_19
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X3)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f72,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_6
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f400,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl8_47
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f489,plain,
    ( ~ spl8_5
    | ~ spl8_38
    | ~ spl8_45 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_38
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f287,f372])).

fof(f372,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,sK4))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl8_45
  <=> ! [X0] : ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f485,plain,
    ( ~ spl8_6
    | ~ spl8_19
    | ~ spl8_24
    | ~ spl8_30
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_19
    | ~ spl8_24
    | ~ spl8_30
    | spl8_39 ),
    inference(subsumption_resolution,[],[f352,f481])).

fof(f481,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(superposition,[],[f174,f206])).

fof(f206,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl8_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f174,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl8_24
  <=> r1_tarski(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f352,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ spl8_6
    | ~ spl8_19
    | ~ spl8_24
    | spl8_39 ),
    inference(unit_resulting_resolution,[],[f72,f174,f294,f145])).

fof(f294,plain,
    ( ~ r1_xboole_0(sK5,sK5)
    | spl8_39 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl8_39
  <=> r1_xboole_0(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f474,plain,
    ( ~ spl8_6
    | ~ spl8_19
    | ~ spl8_23
    | ~ spl8_29
    | spl8_50 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_19
    | ~ spl8_23
    | ~ spl8_29
    | spl8_50 ),
    inference(subsumption_resolution,[],[f427,f470])).

fof(f470,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl8_23
    | ~ spl8_29 ),
    inference(superposition,[],[f167,f202])).

fof(f202,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_29
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f167,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_23
  <=> r1_tarski(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f427,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ spl8_6
    | ~ spl8_19
    | ~ spl8_23
    | spl8_50 ),
    inference(unit_resulting_resolution,[],[f72,f167,f425,f145])).

fof(f425,plain,
    ( ~ r1_xboole_0(sK4,sK4)
    | spl8_50 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl8_50
  <=> r1_xboole_0(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f451,plain,
    ( spl8_52
    | ~ spl8_15
    | spl8_33 ),
    inference(avatar_split_clause,[],[f233,f229,f115,f449])).

fof(f115,plain,
    ( spl8_15
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k1_mcart_1(X0),X1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f233,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,X0))
    | ~ spl8_15
    | spl8_33 ),
    inference(unit_resulting_resolution,[],[f231,f116])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(k1_mcart_1(X0),X1) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f115])).

fof(f231,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl8_33 ),
    inference(avatar_component_clause,[],[f229])).

fof(f426,plain,
    ( ~ spl8_50
    | ~ spl8_14
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f390,f223,f111,f423])).

fof(f223,plain,
    ( spl8_32
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f390,plain,
    ( ~ r1_xboole_0(sK4,sK4)
    | ~ spl8_14
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f224,f224,f112])).

fof(f224,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f223])).

fof(f414,plain,
    ( spl8_28
    | ~ spl8_4
    | spl8_8
    | ~ spl8_22
    | spl8_29
    | spl8_30
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f374,f223,f204,f200,f158,f79,f61,f196])).

fof(f196,plain,
    ( spl8_28
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f61,plain,
    ( spl8_4
  <=> m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f79,plain,
    ( spl8_8
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f158,plain,
    ( spl8_22
  <=> ! [X1,X3,X0,X2] :
        ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f374,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl8_8
    | ~ spl8_22
    | spl8_29
    | spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f214,f224])).

fof(f214,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl8_8
    | ~ spl8_22
    | spl8_29
    | spl8_30 ),
    inference(subsumption_resolution,[],[f212,f201])).

fof(f201,plain,
    ( k1_xboole_0 != sK1
    | spl8_29 ),
    inference(avatar_component_clause,[],[f200])).

fof(f212,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_8
    | ~ spl8_22
    | spl8_30 ),
    inference(subsumption_resolution,[],[f163,f205])).

fof(f205,plain,
    ( k1_xboole_0 != sK2
    | spl8_30 ),
    inference(avatar_component_clause,[],[f204])).

fof(f163,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_8
    | ~ spl8_22 ),
    inference(superposition,[],[f81,f159])).

fof(f159,plain,
    ( ! [X2,X0,X3,X1] :
        ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f158])).

fof(f81,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f401,plain,
    ( spl8_47
    | ~ spl8_18
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f387,f196,f127,f398])).

fof(f127,plain,
    ( spl8_18
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f387,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_18
    | ~ spl8_28 ),
    inference(superposition,[],[f129,f198])).

fof(f198,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f196])).

fof(f129,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f373,plain,
    ( spl8_45
    | ~ spl8_16
    | spl8_32 ),
    inference(avatar_split_clause,[],[f227,f223,f119,f371])).

fof(f119,plain,
    ( spl8_16
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k2_mcart_1(X0),X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f227,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,sK4))
    | ~ spl8_16
    | spl8_32 ),
    inference(unit_resulting_resolution,[],[f225,f120])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(k2_mcart_1(X0),X2) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f119])).

fof(f225,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl8_32 ),
    inference(avatar_component_clause,[],[f223])).

fof(f295,plain,
    ( ~ spl8_39
    | ~ spl8_14
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f261,f208,f111,f292])).

fof(f208,plain,
    ( spl8_31
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f261,plain,
    ( ~ r1_xboole_0(sK5,sK5)
    | ~ spl8_14
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f209,f209,f112])).

fof(f209,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f208])).

fof(f286,plain,
    ( spl8_38
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f142,f123,f115,f284])).

fof(f123,plain,
    ( spl8_17
  <=> ! [X1,X0,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f142,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
        | r2_hidden(k1_mcart_1(X7),k2_zfmisc_1(X4,X5)) )
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(superposition,[],[f116,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f258,plain,
    ( spl8_31
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f240,f235,f66,f208])).

fof(f235,plain,
    ( spl8_34
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(X3,k3_zfmisc_1(X0,X1,X2))
        | r2_hidden(k2_mcart_1(X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f240,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f68,f236])).

fof(f236,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X3,k3_zfmisc_1(X0,X1,X2))
        | r2_hidden(k2_mcart_1(X3),X2) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f235])).

fof(f237,plain,
    ( spl8_34
    | ~ spl8_16
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f141,f123,f119,f235])).

fof(f141,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X3,k3_zfmisc_1(X0,X1,X2))
        | r2_hidden(k2_mcart_1(X3),X2) )
    | ~ spl8_16
    | ~ spl8_17 ),
    inference(superposition,[],[f120,f124])).

fof(f232,plain,
    ( ~ spl8_4
    | ~ spl8_33
    | spl8_7
    | ~ spl8_21
    | spl8_28
    | spl8_29
    | spl8_30 ),
    inference(avatar_split_clause,[],[f217,f204,f200,f196,f152,f75,f229,f61])).

fof(f75,plain,
    ( spl8_7
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f152,plain,
    ( spl8_21
  <=> ! [X1,X3,X0,X2] :
        ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
        | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f217,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | spl8_7
    | ~ spl8_21
    | spl8_28
    | spl8_29
    | spl8_30 ),
    inference(subsumption_resolution,[],[f215,f197])).

fof(f197,plain,
    ( k1_xboole_0 != sK0
    | spl8_28 ),
    inference(avatar_component_clause,[],[f196])).

fof(f215,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK0
    | spl8_7
    | ~ spl8_21
    | spl8_29
    | spl8_30 ),
    inference(subsumption_resolution,[],[f213,f201])).

fof(f213,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_7
    | ~ spl8_21
    | spl8_30 ),
    inference(subsumption_resolution,[],[f162,f205])).

fof(f162,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_7
    | ~ spl8_21 ),
    inference(superposition,[],[f77,f153])).

fof(f153,plain,
    ( ! [X2,X0,X3,X1] :
        ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
        | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f152])).

fof(f77,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f211,plain,
    ( spl8_28
    | spl8_29
    | spl8_30
    | ~ spl8_4
    | ~ spl8_31
    | spl8_9
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f161,f148,f83,f208,f61,f204,f200,f196])).

fof(f83,plain,
    ( spl8_9
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f148,plain,
    ( spl8_20
  <=> ! [X1,X3,X0,X2] :
        ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f161,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_9
    | ~ spl8_20 ),
    inference(superposition,[],[f85,f149])).

fof(f149,plain,
    ( ! [X2,X0,X3,X1] :
        ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f85,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f175,plain,
    ( spl8_24
    | ~ spl8_3
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f105,f88,f56,f172])).

fof(f56,plain,
    ( spl8_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f88,plain,
    ( spl8_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f105,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl8_3
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f58,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f58,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f168,plain,
    ( spl8_23
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f104,f88,f51,f165])).

fof(f51,plain,
    ( spl8_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f104,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f53,f89])).

fof(f53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f160,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f42,f158])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f154,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f41,f152])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f150,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f43,f148])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f146,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f44,f144])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f130,plain,
    ( spl8_18
    | ~ spl8_1
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f103,f88,f46,f127])).

fof(f46,plain,
    ( spl8_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f103,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl8_1
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f48,f89])).

fof(f48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f125,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f38,f123])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f121,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f40,f119])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f117,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f39,f115])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f35,f111])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f90,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f36,f88])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f86,plain,
    ( ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f31,f83,f79,f75])).

fof(f31,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f21,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                  & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
                | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
              & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
              | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
            & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
            | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
            | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
          & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
          | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
          | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
        & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
        | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
        | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
      & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f73,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f69,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (6971)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (6966)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (6977)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (6975)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (6965)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (6968)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (6967)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (6966)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f513,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f73,f86,f90,f113,f117,f121,f125,f130,f146,f150,f154,f160,f168,f175,f211,f232,f237,f258,f286,f295,f373,f401,f414,f426,f451,f474,f485,f489,f510,f512])).
% 0.20/0.47  fof(f512,plain,(
% 0.20/0.47    ~spl8_5 | ~spl8_38 | ~spl8_52),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f511])).
% 0.20/0.47  fof(f511,plain,(
% 0.20/0.47    $false | (~spl8_5 | ~spl8_38 | ~spl8_52)),
% 0.20/0.47    inference(subsumption_resolution,[],[f287,f450])).
% 0.20/0.47  fof(f450,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,X0))) ) | ~spl8_52),
% 0.20/0.47    inference(avatar_component_clause,[],[f449])).
% 0.20/0.47  fof(f449,plain,(
% 0.20/0.47    spl8_52 <=> ! [X0] : ~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 0.20/0.47  fof(f287,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | (~spl8_5 | ~spl8_38)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f68,f285])).
% 0.20/0.47  fof(f285,plain,(
% 0.20/0.47    ( ! [X6,X4,X7,X5] : (~r2_hidden(X7,k3_zfmisc_1(X4,X5,X6)) | r2_hidden(k1_mcart_1(X7),k2_zfmisc_1(X4,X5))) ) | ~spl8_38),
% 0.20/0.47    inference(avatar_component_clause,[],[f284])).
% 0.20/0.47  fof(f284,plain,(
% 0.20/0.47    spl8_38 <=> ! [X5,X7,X4,X6] : (~r2_hidden(X7,k3_zfmisc_1(X4,X5,X6)) | r2_hidden(k1_mcart_1(X7),k2_zfmisc_1(X4,X5)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) | ~spl8_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl8_5 <=> r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.47  fof(f510,plain,(
% 0.20/0.47    ~spl8_6 | ~spl8_14 | ~spl8_19 | ~spl8_33 | ~spl8_47),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f509])).
% 0.20/0.47  fof(f509,plain,(
% 0.20/0.47    $false | (~spl8_6 | ~spl8_14 | ~spl8_19 | ~spl8_33 | ~spl8_47)),
% 0.20/0.47    inference(subsumption_resolution,[],[f417,f507])).
% 0.20/0.47  fof(f507,plain,(
% 0.20/0.47    ~r1_xboole_0(sK3,sK3) | (~spl8_14 | ~spl8_33)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f230,f230,f112])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) ) | ~spl8_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl8_14 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.47  fof(f230,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl8_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f229])).
% 0.20/0.47  fof(f229,plain,(
% 0.20/0.47    spl8_33 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.20/0.47  fof(f417,plain,(
% 0.20/0.47    r1_xboole_0(sK3,sK3) | (~spl8_6 | ~spl8_19 | ~spl8_47)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f400,f72,f400,f145])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl8_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f144])).
% 0.20/0.47  % (6963)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl8_19 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl8_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl8_6 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.47  fof(f400,plain,(
% 0.20/0.47    r1_tarski(sK3,k1_xboole_0) | ~spl8_47),
% 0.20/0.47    inference(avatar_component_clause,[],[f398])).
% 0.20/0.47  fof(f398,plain,(
% 0.20/0.47    spl8_47 <=> r1_tarski(sK3,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.20/0.47  fof(f489,plain,(
% 0.20/0.47    ~spl8_5 | ~spl8_38 | ~spl8_45),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f488])).
% 0.20/0.47  fof(f488,plain,(
% 0.20/0.47    $false | (~spl8_5 | ~spl8_38 | ~spl8_45)),
% 0.20/0.47    inference(subsumption_resolution,[],[f287,f372])).
% 0.20/0.47  fof(f372,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,sK4))) ) | ~spl8_45),
% 0.20/0.47    inference(avatar_component_clause,[],[f371])).
% 0.20/0.47  fof(f371,plain,(
% 0.20/0.47    spl8_45 <=> ! [X0] : ~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,sK4))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.20/0.47  fof(f485,plain,(
% 0.20/0.47    ~spl8_6 | ~spl8_19 | ~spl8_24 | ~spl8_30 | spl8_39),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f484])).
% 0.20/0.47  fof(f484,plain,(
% 0.20/0.47    $false | (~spl8_6 | ~spl8_19 | ~spl8_24 | ~spl8_30 | spl8_39)),
% 0.20/0.47    inference(subsumption_resolution,[],[f352,f481])).
% 0.20/0.47  fof(f481,plain,(
% 0.20/0.47    r1_tarski(sK5,k1_xboole_0) | (~spl8_24 | ~spl8_30)),
% 0.20/0.47    inference(superposition,[],[f174,f206])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | ~spl8_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f204])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    spl8_30 <=> k1_xboole_0 = sK2),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    r1_tarski(sK5,sK2) | ~spl8_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f172])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    spl8_24 <=> r1_tarski(sK5,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.20/0.47  fof(f352,plain,(
% 0.20/0.47    ~r1_tarski(sK5,k1_xboole_0) | (~spl8_6 | ~spl8_19 | ~spl8_24 | spl8_39)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f72,f174,f294,f145])).
% 0.20/0.47  fof(f294,plain,(
% 0.20/0.47    ~r1_xboole_0(sK5,sK5) | spl8_39),
% 0.20/0.47    inference(avatar_component_clause,[],[f292])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    spl8_39 <=> r1_xboole_0(sK5,sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.20/0.47  fof(f474,plain,(
% 0.20/0.47    ~spl8_6 | ~spl8_19 | ~spl8_23 | ~spl8_29 | spl8_50),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f473])).
% 0.20/0.47  fof(f473,plain,(
% 0.20/0.47    $false | (~spl8_6 | ~spl8_19 | ~spl8_23 | ~spl8_29 | spl8_50)),
% 0.20/0.47    inference(subsumption_resolution,[],[f427,f470])).
% 0.20/0.47  fof(f470,plain,(
% 0.20/0.47    r1_tarski(sK4,k1_xboole_0) | (~spl8_23 | ~spl8_29)),
% 0.20/0.47    inference(superposition,[],[f167,f202])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~spl8_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f200])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    spl8_29 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    r1_tarski(sK4,sK1) | ~spl8_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f165])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl8_23 <=> r1_tarski(sK4,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.47  fof(f427,plain,(
% 0.20/0.47    ~r1_tarski(sK4,k1_xboole_0) | (~spl8_6 | ~spl8_19 | ~spl8_23 | spl8_50)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f72,f167,f425,f145])).
% 0.20/0.47  fof(f425,plain,(
% 0.20/0.47    ~r1_xboole_0(sK4,sK4) | spl8_50),
% 0.20/0.47    inference(avatar_component_clause,[],[f423])).
% 0.20/0.47  fof(f423,plain,(
% 0.20/0.47    spl8_50 <=> r1_xboole_0(sK4,sK4)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.20/0.47  fof(f451,plain,(
% 0.20/0.47    spl8_52 | ~spl8_15 | spl8_33),
% 0.20/0.47    inference(avatar_split_clause,[],[f233,f229,f115,f449])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl8_15 <=> ! [X1,X0,X2] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.47  fof(f233,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,X0))) ) | (~spl8_15 | spl8_33)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f231,f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) ) | ~spl8_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f115])).
% 0.20/0.47  fof(f231,plain,(
% 0.20/0.47    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | spl8_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f229])).
% 0.20/0.47  fof(f426,plain,(
% 0.20/0.47    ~spl8_50 | ~spl8_14 | ~spl8_32),
% 0.20/0.47    inference(avatar_split_clause,[],[f390,f223,f111,f423])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    spl8_32 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.20/0.47  fof(f390,plain,(
% 0.20/0.47    ~r1_xboole_0(sK4,sK4) | (~spl8_14 | ~spl8_32)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f224,f224,f112])).
% 0.20/0.47  fof(f224,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl8_32),
% 0.20/0.47    inference(avatar_component_clause,[],[f223])).
% 0.20/0.47  fof(f414,plain,(
% 0.20/0.47    spl8_28 | ~spl8_4 | spl8_8 | ~spl8_22 | spl8_29 | spl8_30 | ~spl8_32),
% 0.20/0.47    inference(avatar_split_clause,[],[f374,f223,f204,f200,f158,f79,f61,f196])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    spl8_28 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl8_4 <=> m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl8_8 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl8_22 <=> ! [X1,X3,X0,X2] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.20/0.47  fof(f374,plain,(
% 0.20/0.47    ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl8_8 | ~spl8_22 | spl8_29 | spl8_30 | ~spl8_32)),
% 0.20/0.47    inference(subsumption_resolution,[],[f214,f224])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl8_8 | ~spl8_22 | spl8_29 | spl8_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f212,f201])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | spl8_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f200])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_8 | ~spl8_22 | spl8_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f163,f205])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    k1_xboole_0 != sK2 | spl8_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f204])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_8 | ~spl8_22)),
% 0.20/0.47    inference(superposition,[],[f81,f159])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl8_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f158])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl8_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f79])).
% 0.20/0.47  fof(f401,plain,(
% 0.20/0.47    spl8_47 | ~spl8_18 | ~spl8_28),
% 0.20/0.47    inference(avatar_split_clause,[],[f387,f196,f127,f398])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    spl8_18 <=> r1_tarski(sK3,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.47  fof(f387,plain,(
% 0.20/0.47    r1_tarski(sK3,k1_xboole_0) | (~spl8_18 | ~spl8_28)),
% 0.20/0.47    inference(superposition,[],[f129,f198])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl8_28),
% 0.20/0.47    inference(avatar_component_clause,[],[f196])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    r1_tarski(sK3,sK0) | ~spl8_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f127])).
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    spl8_45 | ~spl8_16 | spl8_32),
% 0.20/0.47    inference(avatar_split_clause,[],[f227,f223,f119,f371])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl8_16 <=> ! [X1,X0,X2] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,sK4))) ) | (~spl8_16 | spl8_32)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f225,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) ) | ~spl8_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f119])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | spl8_32),
% 0.20/0.47    inference(avatar_component_clause,[],[f223])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    ~spl8_39 | ~spl8_14 | ~spl8_31),
% 0.20/0.47    inference(avatar_split_clause,[],[f261,f208,f111,f292])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    spl8_31 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.20/0.47  fof(f261,plain,(
% 0.20/0.47    ~r1_xboole_0(sK5,sK5) | (~spl8_14 | ~spl8_31)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f209,f209,f112])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl8_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f208])).
% 0.20/0.47  fof(f286,plain,(
% 0.20/0.47    spl8_38 | ~spl8_15 | ~spl8_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f142,f123,f115,f284])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl8_17 <=> ! [X1,X0,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ( ! [X6,X4,X7,X5] : (~r2_hidden(X7,k3_zfmisc_1(X4,X5,X6)) | r2_hidden(k1_mcart_1(X7),k2_zfmisc_1(X4,X5))) ) | (~spl8_15 | ~spl8_17)),
% 0.20/0.47    inference(superposition,[],[f116,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) | ~spl8_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f258,plain,(
% 0.20/0.47    spl8_31 | ~spl8_5 | ~spl8_34),
% 0.20/0.47    inference(avatar_split_clause,[],[f240,f235,f66,f208])).
% 0.20/0.47  fof(f235,plain,(
% 0.20/0.47    spl8_34 <=> ! [X1,X3,X0,X2] : (~r2_hidden(X3,k3_zfmisc_1(X0,X1,X2)) | r2_hidden(k2_mcart_1(X3),X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(sK6),sK5) | (~spl8_5 | ~spl8_34)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f68,f236])).
% 0.20/0.47  fof(f236,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k3_zfmisc_1(X0,X1,X2)) | r2_hidden(k2_mcart_1(X3),X2)) ) | ~spl8_34),
% 0.20/0.47    inference(avatar_component_clause,[],[f235])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    spl8_34 | ~spl8_16 | ~spl8_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f141,f123,f119,f235])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k3_zfmisc_1(X0,X1,X2)) | r2_hidden(k2_mcart_1(X3),X2)) ) | (~spl8_16 | ~spl8_17)),
% 0.20/0.47    inference(superposition,[],[f120,f124])).
% 0.20/0.47  fof(f232,plain,(
% 0.20/0.47    ~spl8_4 | ~spl8_33 | spl8_7 | ~spl8_21 | spl8_28 | spl8_29 | spl8_30),
% 0.20/0.47    inference(avatar_split_clause,[],[f217,f204,f200,f196,f152,f75,f229,f61])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl8_7 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    spl8_21 <=> ! [X1,X3,X0,X2] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | (spl8_7 | ~spl8_21 | spl8_28 | spl8_29 | spl8_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f215,f197])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    k1_xboole_0 != sK0 | spl8_28),
% 0.20/0.47    inference(avatar_component_clause,[],[f196])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | (spl8_7 | ~spl8_21 | spl8_29 | spl8_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f213,f201])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_7 | ~spl8_21 | spl8_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f162,f205])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_7 | ~spl8_21)),
% 0.20/0.47    inference(superposition,[],[f77,f153])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl8_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f152])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl8_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f75])).
% 0.20/0.47  fof(f211,plain,(
% 0.20/0.47    spl8_28 | spl8_29 | spl8_30 | ~spl8_4 | ~spl8_31 | spl8_9 | ~spl8_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f161,f148,f83,f208,f61,f204,f200,f196])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl8_9 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl8_20 <=> ! [X1,X3,X0,X2] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(sK6),sK5) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_9 | ~spl8_20)),
% 0.20/0.47    inference(superposition,[],[f85,f149])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl8_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f148])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl8_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f83])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    spl8_24 | ~spl8_3 | ~spl8_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f88,f56,f172])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl8_3 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl8_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    r1_tarski(sK5,sK2) | (~spl8_3 | ~spl8_10)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f58,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl8_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f88])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl8_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f56])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    spl8_23 | ~spl8_2 | ~spl8_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f104,f88,f51,f165])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl8_2 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    r1_tarski(sK4,sK1) | (~spl8_2 | ~spl8_10)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f53,f89])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl8_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f51])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    spl8_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f158])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    spl8_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f152])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    spl8_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f43,f148])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl8_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f144])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    spl8_18 | ~spl8_1 | ~spl8_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f103,f88,f46,f127])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl8_1 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    r1_tarski(sK3,sK0) | (~spl8_1 | ~spl8_10)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f89])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f46])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    spl8_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f123])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    spl8_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f119])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl8_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f115])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl8_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f111])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl8_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f88])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ~spl8_7 | ~spl8_8 | ~spl8_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f83,f79,f75])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f21,f20,f19,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl8_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f71])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl8_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f66])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl8_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f29,f61])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl8_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f56])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl8_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f51])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl8_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f46])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (6966)------------------------------
% 0.20/0.47  % (6966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6966)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (6966)Memory used [KB]: 6396
% 0.20/0.47  % (6966)Time elapsed: 0.059 s
% 0.20/0.47  % (6966)------------------------------
% 0.20/0.47  % (6966)------------------------------
% 0.20/0.47  % (6978)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (6974)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (6964)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (6960)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (6961)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (6976)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (6957)Success in time 0.125 s
%------------------------------------------------------------------------------
