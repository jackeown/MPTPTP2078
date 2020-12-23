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
% DateTime   : Thu Dec  3 13:14:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 299 expanded)
%              Number of leaves         :   41 ( 151 expanded)
%              Depth                    :    7
%              Number of atoms          :  539 (1353 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f811,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f99,f107,f125,f141,f145,f154,f172,f180,f190,f194,f224,f234,f256,f264,f288,f352,f431,f669,f808,f810])).

fof(f810,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_23
    | spl3_36
    | ~ spl3_41
    | ~ spl3_73
    | ~ spl3_80 ),
    inference(avatar_contradiction_clause,[],[f809])).

fof(f809,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_23
    | spl3_36
    | ~ spl3_41
    | ~ spl3_73
    | ~ spl3_80 ),
    inference(subsumption_resolution,[],[f671,f807])).

fof(f807,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f806])).

fof(f806,plain,
    ( spl3_80
  <=> ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

% (12185)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f671,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_23
    | spl3_36
    | ~ spl3_41
    | ~ spl3_73 ),
    inference(unit_resulting_resolution,[],[f59,f64,f74,f84,f351,f287,f668,f193])).

fof(f193,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ r1_tarski(X2,X1)
        | ~ v2_compts_1(X1,X0)
        | v2_compts_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( v2_compts_1(X2,X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ r1_tarski(X2,X1)
        | ~ v2_compts_1(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f668,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f666])).

fof(f666,plain,
    ( spl3_73
  <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f287,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl3_36
  <=> v2_compts_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f351,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl3_41
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f74,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_4
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f808,plain,
    ( spl3_80
    | ~ spl3_2
    | ~ spl3_27
    | ~ spl3_29
    | ~ spl3_41
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f456,f429,f350,f231,f221,f62,f806])).

fof(f221,plain,
    ( spl3_27
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f231,plain,
    ( spl3_29
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f429,plain,
    ( spl3_48
  <=> ! [X3,X2,X4] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X4,X3)
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f456,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_27
    | ~ spl3_29
    | ~ spl3_41
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f432,f233])).

fof(f233,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f231])).

fof(f432,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK1)),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_27
    | ~ spl3_41
    | ~ spl3_48 ),
    inference(unit_resulting_resolution,[],[f223,f64,f351,f430])).

fof(f430,plain,
    ( ! [X4,X2,X3] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X4,X3)
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X4)) )
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f429])).

fof(f223,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f221])).

fof(f669,plain,
    ( spl3_73
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_22
    | ~ spl3_31
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f268,f261,f253,f188,f87,f82,f62,f57,f666])).

fof(f87,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f188,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f253,plain,
    ( spl3_31
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f261,plain,
    ( spl3_32
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f268,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_22
    | ~ spl3_31
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f59,f64,f255,f84,f89,f263,f189])).

fof(f189,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k3_xboole_0(X1,X2),X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f188])).

fof(f263,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f261])).

fof(f89,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f255,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f253])).

fof(f431,plain,
    ( spl3_48
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f175,f170,f105,f429])).

fof(f105,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f170,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f175,plain,
    ( ! [X4,X2,X3] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X4,X3)
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X4)) )
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(resolution,[],[f171,f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f171,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f352,plain,
    ( spl3_41
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f128,f123,f97,f350])).

fof(f97,plain,
    ( spl3_9
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f123,plain,
    ( spl3_14
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f128,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(superposition,[],[f98,f124])).

fof(f124,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f98,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f288,plain,
    ( ~ spl3_7
    | ~ spl3_36
    | spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f162,f143,f92,f285,f87])).

fof(f92,plain,
    ( spl3_8
  <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f143,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f162,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8
    | ~ spl3_18 ),
    inference(superposition,[],[f94,f144])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f94,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f264,plain,
    ( spl3_32
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f182,f178,f87,f77,f67,f62,f57,f261])).

fof(f67,plain,
    ( spl3_3
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f77,plain,
    ( spl3_5
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f178,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v2_compts_1(X1,X0)
        | ~ v8_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f182,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f59,f64,f69,f79,f89,f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(X1,X0)
        | ~ v8_pre_topc(X0)
        | v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f79,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f69,plain,
    ( v8_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f256,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f181,f178,f82,f72,f67,f62,f57,f253])).

fof(f181,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f59,f64,f69,f74,f84,f179])).

fof(f234,plain,
    ( spl3_29
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f163,f152,f82,f62,f231])).

fof(f152,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f163,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f64,f84,f153])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f152])).

fof(f224,plain,
    ( spl3_27
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f155,f139,f82,f62,f221])).

fof(f139,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f155,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f64,f84,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f194,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f45,f192])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(f190,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f55,f188])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

fof(f180,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f44,f178])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

fof(f172,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f42,f170])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f154,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f43,f152])).

fof(f43,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f145,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f54,f143])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f141,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f51,f139])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f125,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f48,f123])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f107,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f53,f105])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f99,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f46,f97])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f95,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f41,f92])).

fof(f41,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_compts_1(X2,sK0)
            & v2_compts_1(X1,sK0)
            & v8_pre_topc(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_compts_1(X2,sK0)
          & v2_compts_1(sK1,sK0)
          & v8_pre_topc(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_compts_1(X2,sK0)
        & v2_compts_1(sK1,sK0)
        & v8_pre_topc(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_compts_1(sK2,sK0)
      & v2_compts_1(sK1,sK0)
      & v8_pre_topc(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

fof(f90,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f37,f87])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f34,f57])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:13:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (12172)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (12181)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (12174)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (12179)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (12184)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (12173)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (12171)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (12180)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (12169)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (12183)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (12174)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f811,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f99,f107,f125,f141,f145,f154,f172,f180,f190,f194,f224,f234,f256,f264,f288,f352,f431,f669,f808,f810])).
% 0.21/0.49  fof(f810,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_23 | spl3_36 | ~spl3_41 | ~spl3_73 | ~spl3_80),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f809])).
% 0.21/0.49  fof(f809,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_23 | spl3_36 | ~spl3_41 | ~spl3_73 | ~spl3_80)),
% 0.21/0.49    inference(subsumption_resolution,[],[f671,f807])).
% 0.21/0.49  fof(f807,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_80),
% 0.21/0.49    inference(avatar_component_clause,[],[f806])).
% 0.21/0.49  fof(f806,plain,(
% 0.21/0.49    spl3_80 <=> ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 0.21/0.49  % (12185)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  fof(f671,plain,(
% 0.21/0.49    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_23 | spl3_36 | ~spl3_41 | ~spl3_73)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f64,f74,f84,f351,f287,f668,f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | v2_compts_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    spl3_23 <=> ! [X1,X0,X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f668,plain,(
% 0.21/0.49    v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | ~spl3_73),
% 0.21/0.49    inference(avatar_component_clause,[],[f666])).
% 0.21/0.49  fof(f666,plain,(
% 0.21/0.49    spl3_73 <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    ~v2_compts_1(k3_xboole_0(sK1,sK2),sK0) | spl3_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f285])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    spl3_36 <=> v2_compts_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f350])).
% 0.21/0.49  fof(f350,plain,(
% 0.21/0.49    spl3_41 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    v2_compts_1(sK1,sK0) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_4 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_2 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_1 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f808,plain,(
% 0.21/0.49    spl3_80 | ~spl3_2 | ~spl3_27 | ~spl3_29 | ~spl3_41 | ~spl3_48),
% 0.21/0.49    inference(avatar_split_clause,[],[f456,f429,f350,f231,f221,f62,f806])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    spl3_27 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl3_29 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f429,plain,(
% 0.21/0.49    spl3_48 <=> ! [X3,X2,X4] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X4)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.49  fof(f456,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_27 | ~spl3_29 | ~spl3_41 | ~spl3_48)),
% 0.21/0.49    inference(forward_demodulation,[],[f432,f233])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f231])).
% 0.21/0.49  fof(f432,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK1)),X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_27 | ~spl3_41 | ~spl3_48)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f223,f64,f351,f430])).
% 0.21/0.49  fof(f430,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X4))) ) | ~spl3_48),
% 0.21/0.49    inference(avatar_component_clause,[],[f429])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f221])).
% 0.21/0.49  fof(f669,plain,(
% 0.21/0.49    spl3_73 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_22 | ~spl3_31 | ~spl3_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f268,f261,f253,f188,f87,f82,f62,f57,f666])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl3_22 <=> ! [X1,X0,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl3_31 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    spl3_32 <=> v4_pre_topc(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_22 | ~spl3_31 | ~spl3_32)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f64,f255,f84,f89,f263,f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f188])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    v4_pre_topc(sK2,sK0) | ~spl3_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f261])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    v4_pre_topc(sK1,sK0) | ~spl3_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    spl3_48 | ~spl3_11 | ~spl3_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f175,f170,f105,f429])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl3_11 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl3_20 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X4))) ) | (~spl3_11 | ~spl3_20)),
% 0.21/0.49    inference(resolution,[],[f171,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f105])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    spl3_41 | ~spl3_9 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f128,f123,f97,f350])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl3_14 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | (~spl3_9 | ~spl3_14)),
% 0.21/0.49    inference(superposition,[],[f98,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ~spl3_7 | ~spl3_36 | spl3_8 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f162,f143,f92,f285,f87])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl3_8 <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl3_18 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~v2_compts_1(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_8 | ~spl3_18)),
% 0.21/0.49    inference(superposition,[],[f94,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    spl3_32 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f182,f178,f87,f77,f67,f62,f57,f261])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_3 <=> v8_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_5 <=> v2_compts_1(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl3_21 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    v4_pre_topc(sK2,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_21)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f64,f69,f79,f89,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f178])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    v2_compts_1(sK2,sK0) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v8_pre_topc(sK0) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    spl3_31 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f181,f178,f82,f72,f67,f62,f57,f253])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    v4_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_21)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f64,f69,f74,f84,f179])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    spl3_29 | ~spl3_2 | ~spl3_6 | ~spl3_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f163,f152,f82,f62,f231])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    spl3_19 <=> ! [X1,X0] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_2 | ~spl3_6 | ~spl3_19)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f64,f84,f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f152])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    spl3_27 | ~spl3_2 | ~spl3_6 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f155,f139,f82,f62,f221])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl3_17 <=> ! [X1,X0] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_2 | ~spl3_6 | ~spl3_17)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f64,f84,f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f139])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl3_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f192])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    spl3_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f188])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f178])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl3_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f170])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl3_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f152])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f143])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f139])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f123])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f105])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f97])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f92])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f87])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f82])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f77])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v2_compts_1(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f72])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v2_compts_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f67])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v8_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f62])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f57])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (12174)------------------------------
% 0.21/0.49  % (12174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12174)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (12174)Memory used [KB]: 6780
% 0.21/0.49  % (12174)Time elapsed: 0.068 s
% 0.21/0.49  % (12174)------------------------------
% 0.21/0.49  % (12174)------------------------------
% 0.21/0.50  % (12160)Success in time 0.132 s
%------------------------------------------------------------------------------
