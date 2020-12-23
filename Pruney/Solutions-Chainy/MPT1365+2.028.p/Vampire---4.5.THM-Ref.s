%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
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
fof(f707,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f84,f89,f94,f98,f106,f124,f139,f143,f152,f169,f177,f187,f191,f220,f230,f252,f260,f284,f348,f412,f597,f704,f706])).

fof(f706,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_23
    | spl3_36
    | ~ spl3_41
    | ~ spl3_66
    | ~ spl3_72 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_23
    | spl3_36
    | ~ spl3_41
    | ~ spl3_66
    | ~ spl3_72 ),
    inference(subsumption_resolution,[],[f599,f703])).

fof(f703,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl3_72
  <=> ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f599,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_23
    | spl3_36
    | ~ spl3_41
    | ~ spl3_66 ),
    inference(unit_resulting_resolution,[],[f58,f63,f73,f83,f347,f283,f596,f190])).

fof(f190,plain,
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
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
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

fof(f596,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl3_66
  <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f283,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl3_36
  <=> v2_compts_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f347,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl3_41
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f73,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_4
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f63,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f704,plain,
    ( spl3_72
    | ~ spl3_2
    | ~ spl3_27
    | ~ spl3_29
    | ~ spl3_41
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f435,f410,f346,f227,f217,f61,f702])).

fof(f217,plain,
    ( spl3_27
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f227,plain,
    ( spl3_29
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f410,plain,
    ( spl3_47
  <=> ! [X3,X2,X4] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X4,X3)
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f435,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_27
    | ~ spl3_29
    | ~ spl3_41
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f415,f229])).

fof(f229,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f227])).

fof(f415,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK1)),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_27
    | ~ spl3_41
    | ~ spl3_47 ),
    inference(unit_resulting_resolution,[],[f219,f63,f347,f411])).

fof(f411,plain,
    ( ! [X4,X2,X3] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X4,X3)
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X4)) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f410])).

fof(f219,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f217])).

fof(f597,plain,
    ( spl3_66
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_22
    | ~ spl3_31
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f264,f257,f249,f185,f86,f81,f61,f56,f594])).

fof(f86,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f185,plain,
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

fof(f249,plain,
    ( spl3_31
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f257,plain,
    ( spl3_32
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f264,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_22
    | ~ spl3_31
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f58,f63,f251,f83,f88,f259,f186])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k3_xboole_0(X1,X2),X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f185])).

fof(f259,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f257])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f251,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f249])).

fof(f412,plain,
    ( spl3_47
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f172,f167,f104,f410])).

fof(f104,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f167,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f172,plain,
    ( ! [X4,X2,X3] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X4,X3)
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X4)) )
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(resolution,[],[f168,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f167])).

fof(f348,plain,
    ( spl3_41
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f126,f122,f96,f346])).

fof(f96,plain,
    ( spl3_9
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f122,plain,
    ( spl3_14
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f126,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(superposition,[],[f97,f123])).

fof(f123,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f97,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f284,plain,
    ( ~ spl3_7
    | ~ spl3_36
    | spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f160,f141,f91,f281,f86])).

fof(f91,plain,
    ( spl3_8
  <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f141,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f160,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8
    | ~ spl3_18 ),
    inference(superposition,[],[f93,f142])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f93,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f260,plain,
    ( spl3_32
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f179,f175,f86,f76,f66,f61,f56,f257])).

fof(f66,plain,
    ( spl3_3
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( spl3_5
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f175,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v2_compts_1(X1,X0)
        | ~ v8_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f179,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f58,f63,f68,f78,f88,f176])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(X1,X0)
        | ~ v8_pre_topc(X0)
        | v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f78,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f68,plain,
    ( v8_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f252,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f178,f175,f81,f71,f66,f61,f56,f249])).

fof(f178,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f58,f63,f68,f73,f83,f176])).

fof(f230,plain,
    ( spl3_29
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f161,f150,f81,f61,f227])).

fof(f150,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f161,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f63,f83,f151])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f220,plain,
    ( spl3_27
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f153,f137,f81,f61,f217])).

fof(f137,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f153,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f63,f83,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f137])).

fof(f191,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f44,f189])).

fof(f44,plain,(
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

% (7322)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (7315)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (7320)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (7327)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (7317)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% (7323)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (7321)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% (7330)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
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

fof(f187,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f54,f185])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f177,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f43,f175])).

fof(f43,plain,(
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

fof(f169,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f41,f167])).

fof(f41,plain,(
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

fof(f152,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f42,f150])).

fof(f42,plain,(
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

fof(f143,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f53,f141])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f139,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f50,f137])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f124,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f48,f122])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f106,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f52,f104])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f98,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f45,f96])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f94,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f30,plain,
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

fof(f89,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:26:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (7318)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (7325)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (7324)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (7326)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (7319)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (7316)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (7328)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (7329)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (7319)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f707,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f84,f89,f94,f98,f106,f124,f139,f143,f152,f169,f177,f187,f191,f220,f230,f252,f260,f284,f348,f412,f597,f704,f706])).
% 0.21/0.49  fof(f706,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_23 | spl3_36 | ~spl3_41 | ~spl3_66 | ~spl3_72),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f705])).
% 0.21/0.49  fof(f705,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_23 | spl3_36 | ~spl3_41 | ~spl3_66 | ~spl3_72)),
% 0.21/0.49    inference(subsumption_resolution,[],[f599,f703])).
% 0.21/0.49  fof(f703,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_72),
% 0.21/0.49    inference(avatar_component_clause,[],[f702])).
% 0.21/0.49  fof(f702,plain,(
% 0.21/0.49    spl3_72 <=> ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.49  fof(f599,plain,(
% 0.21/0.49    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_23 | spl3_36 | ~spl3_41 | ~spl3_66)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f58,f63,f73,f83,f347,f283,f596,f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | v2_compts_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    spl3_23 <=> ! [X1,X0,X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f596,plain,(
% 0.21/0.49    v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | ~spl3_66),
% 0.21/0.49    inference(avatar_component_clause,[],[f594])).
% 0.21/0.49  fof(f594,plain,(
% 0.21/0.49    spl3_66 <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ~v2_compts_1(k3_xboole_0(sK1,sK2),sK0) | spl3_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f281])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    spl3_36 <=> v2_compts_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f346])).
% 0.21/0.49  fof(f346,plain,(
% 0.21/0.49    spl3_41 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    v2_compts_1(sK1,sK0) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_4 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_2 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl3_1 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f704,plain,(
% 0.21/0.49    spl3_72 | ~spl3_2 | ~spl3_27 | ~spl3_29 | ~spl3_41 | ~spl3_47),
% 0.21/0.49    inference(avatar_split_clause,[],[f435,f410,f346,f227,f217,f61,f702])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl3_27 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    spl3_29 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f410,plain,(
% 0.21/0.49    spl3_47 <=> ! [X3,X2,X4] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X4)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.49  fof(f435,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_27 | ~spl3_29 | ~spl3_41 | ~spl3_47)),
% 0.21/0.49    inference(forward_demodulation,[],[f415,f229])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f227])).
% 0.21/0.49  fof(f415,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK1)),X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_27 | ~spl3_41 | ~spl3_47)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f219,f63,f347,f411])).
% 0.21/0.49  fof(f411,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X4))) ) | ~spl3_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f410])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f217])).
% 0.21/0.49  fof(f597,plain,(
% 0.21/0.49    spl3_66 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_22 | ~spl3_31 | ~spl3_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f264,f257,f249,f185,f86,f81,f61,f56,f594])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl3_22 <=> ! [X1,X0,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    spl3_31 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    spl3_32 <=> v4_pre_topc(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_22 | ~spl3_31 | ~spl3_32)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f58,f63,f251,f83,f88,f259,f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    v4_pre_topc(sK2,sK0) | ~spl3_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f257])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    v4_pre_topc(sK1,sK0) | ~spl3_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f249])).
% 0.21/0.49  fof(f412,plain,(
% 0.21/0.49    spl3_47 | ~spl3_11 | ~spl3_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f172,f167,f104,f410])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl3_11 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    spl3_20 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X4))) ) | (~spl3_11 | ~spl3_20)),
% 0.21/0.49    inference(resolution,[],[f168,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f167])).
% 0.21/0.49  fof(f348,plain,(
% 0.21/0.49    spl3_41 | ~spl3_9 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f122,f96,f346])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl3_14 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | (~spl3_9 | ~spl3_14)),
% 0.21/0.49    inference(superposition,[],[f97,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ~spl3_7 | ~spl3_36 | spl3_8 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f160,f141,f91,f281,f86])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl3_8 <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl3_18 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~v2_compts_1(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_8 | ~spl3_18)),
% 0.21/0.49    inference(superposition,[],[f93,f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f141])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    spl3_32 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f179,f175,f86,f76,f66,f61,f56,f257])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl3_3 <=> v8_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl3_5 <=> v2_compts_1(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl3_21 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    v4_pre_topc(sK2,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_21)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f58,f63,f68,f78,f88,f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    v2_compts_1(sK2,sK0) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v8_pre_topc(sK0) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    spl3_31 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f178,f175,f81,f71,f66,f61,f56,f249])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    v4_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_21)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f58,f63,f68,f73,f83,f176])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    spl3_29 | ~spl3_2 | ~spl3_6 | ~spl3_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f161,f150,f81,f61,f227])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl3_19 <=> ! [X1,X0] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_2 | ~spl3_6 | ~spl3_19)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f63,f83,f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f150])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    spl3_27 | ~spl3_2 | ~spl3_6 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f153,f137,f81,f61,f217])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl3_17 <=> ! [X1,X0] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_2 | ~spl3_6 | ~spl3_17)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f63,f83,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl3_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f189])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  % (7322)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (7315)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (7320)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (7327)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (7317)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (7323)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (7321)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (7330)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl3_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f185])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl3_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f175])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl3_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f167])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl3_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f150])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f141])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl3_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f137])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f122])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f104])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f96])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ~spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f91])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30,f29,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f86])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f76])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v2_compts_1(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f71])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    v2_compts_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f66])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    v8_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f61])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f56])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (7319)------------------------------
% 0.21/0.50  % (7319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7319)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (7319)Memory used [KB]: 6652
% 0.21/0.50  % (7319)Time elapsed: 0.063 s
% 0.21/0.50  % (7319)------------------------------
% 0.21/0.50  % (7319)------------------------------
% 0.21/0.50  % (7313)Success in time 0.141 s
%------------------------------------------------------------------------------
