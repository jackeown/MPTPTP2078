%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 252 expanded)
%              Number of leaves         :   36 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  527 (1251 expanded)
%              Number of equality atoms :   55 ( 120 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f106,f111,f116,f121,f126,f166,f170,f184,f249,f254,f260,f301,f323,f343,f351,f357,f366,f372,f376])).

fof(f376,plain,
    ( ~ spl4_1
    | spl4_47 ),
    inference(avatar_split_clause,[],[f374,f369,f63])).

fof(f63,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f369,plain,
    ( spl4_47
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f374,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_47 ),
    inference(resolution,[],[f371,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f371,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_47 ),
    inference(avatar_component_clause,[],[f369])).

fof(f372,plain,
    ( spl4_3
    | ~ spl4_47
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f367,f363,f369,f73])).

fof(f73,plain,
    ( spl4_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f363,plain,
    ( spl4_46
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f367,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_46 ),
    inference(resolution,[],[f365,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f365,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f363])).

fof(f366,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_46
    | ~ spl4_13
    | spl4_45 ),
    inference(avatar_split_clause,[],[f361,f354,f123,f363,f118,f113])).

fof(f113,plain,
    ( spl4_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f118,plain,
    ( spl4_12
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f123,plain,
    ( spl4_13
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f354,plain,
    ( spl4_45
  <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f361,plain,
    ( ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl4_45 ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,
    ( ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl4_45 ),
    inference(condensation,[],[f359])).

fof(f359,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK0))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | spl4_45 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK0))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl4_45 ),
    inference(resolution,[],[f356,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f356,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f354])).

fof(f357,plain,
    ( ~ spl4_45
    | spl4_21
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f352,f348,f181,f354])).

fof(f181,plain,
    ( spl4_21
  <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f348,plain,
    ( spl4_44
  <=> sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f352,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | spl4_21
    | ~ spl4_44 ),
    inference(backward_demodulation,[],[f183,f350])).

fof(f350,plain,
    ( sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f348])).

fof(f183,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f181])).

fof(f351,plain,
    ( spl4_44
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_30
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f346,f341,f257,f159,f93,f348])).

fof(f93,plain,
    ( spl4_7
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f159,plain,
    ( spl4_18
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f257,plain,
    ( spl4_30
  <=> sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f341,plain,
    ( spl4_43
  <=> ! [X0] :
        ( k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f346,plain,
    ( sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_30
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f345,f259])).

fof(f259,plain,
    ( sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f257])).

fof(f345,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f344,f161])).

fof(f161,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f344,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ spl4_7
    | ~ spl4_43 ),
    inference(resolution,[],[f342,f95])).

fof(f95,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f341])).

fof(f343,plain,
    ( ~ spl4_11
    | spl4_43
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f338,f321,f123,f118,f341,f113])).

fof(f321,plain,
    ( spl4_39
  <=> ! [X3,X2] :
        ( k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl4_13
    | ~ spl4_39 ),
    inference(resolution,[],[f322,f125])).

fof(f125,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f322,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f321])).

fof(f323,plain,
    ( ~ spl4_4
    | spl4_6
    | spl4_39
    | ~ spl4_5
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f315,f299,f83,f321,f88,f78])).

fof(f78,plain,
    ( spl4_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f88,plain,
    ( spl4_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f83,plain,
    ( spl4_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f299,plain,
    ( spl4_34
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f315,plain,
    ( ! [X2,X3] :
        ( k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3))
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK1) )
    | ~ spl4_5
    | ~ spl4_34 ),
    inference(resolution,[],[f300,f85])).

fof(f85,plain,
    ( v2_pre_topc(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f300,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f299])).

fof(f301,plain,
    ( ~ spl4_1
    | spl4_3
    | spl4_34
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f292,f68,f299,f73,f63])).

fof(f68,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f292,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X2,X0)
        | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f46,f70])).

fof(f70,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f260,plain,
    ( spl4_30
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f255,f252,f257])).

fof(f252,plain,
    ( spl4_29
  <=> ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f255,plain,
    ( sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | ~ spl4_29 ),
    inference(resolution,[],[f253,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f253,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( ~ spl4_13
    | spl4_29
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f250,f247,f118,f113,f252,f123])).

fof(f247,plain,
    ( spl4_28
  <=> ! [X0] :
        ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
        | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ r1_tarski(u1_struct_0(sK1),X0)
        | ~ v1_funct_1(sK3)
        | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) )
    | ~ spl4_28 ),
    inference(resolution,[],[f52,f248])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
        | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f247])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X0,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

fof(f249,plain,
    ( ~ spl4_11
    | spl4_28
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f244,f123,f113,f247,f113])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) )
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(resolution,[],[f241,f125])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1) )
    | ~ spl4_11 ),
    inference(resolution,[],[f235,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | sK3 = X0
        | ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3) )
    | ~ spl4_11 ),
    inference(resolution,[],[f56,f115])).

fof(f115,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f184,plain,
    ( ~ spl4_21
    | spl4_9
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f173,f159,f103,f181])).

fof(f103,plain,
    ( spl4_9
  <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f173,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl4_9
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f105,f161])).

fof(f105,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f170,plain,
    ( ~ spl4_4
    | spl4_19 ),
    inference(avatar_split_clause,[],[f168,f163,f78])).

fof(f163,plain,
    ( spl4_19
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f168,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_19 ),
    inference(resolution,[],[f165,f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f165,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f166,plain,
    ( spl4_18
    | ~ spl4_19
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f157,f108,f163,f159])).

fof(f108,plain,
    ( spl4_10
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f157,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_10 ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | u1_struct_0(sK2) = X0 )
    | ~ spl4_10 ),
    inference(superposition,[],[f47,f110])).

fof(f110,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f126,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f30,f123])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

fof(f121,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f31,f118])).

fof(f31,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f116,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f32,f113])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f111,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f33,f108])).

fof(f33,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f106,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f34,f103])).

fof(f34,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f40,f73])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f68])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f42,f63])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (13596)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.47  % (13596)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (13605)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f377,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f106,f111,f116,f121,f126,f166,f170,f184,f249,f254,f260,f301,f323,f343,f351,f357,f366,f372,f376])).
% 0.19/0.48  fof(f376,plain,(
% 0.19/0.48    ~spl4_1 | spl4_47),
% 0.19/0.48    inference(avatar_split_clause,[],[f374,f369,f63])).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    spl4_1 <=> l1_pre_topc(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.48  fof(f369,plain,(
% 0.19/0.48    spl4_47 <=> l1_struct_0(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.19/0.48  fof(f374,plain,(
% 0.19/0.48    ~l1_pre_topc(sK0) | spl4_47),
% 0.19/0.48    inference(resolution,[],[f371,f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.48  fof(f371,plain,(
% 0.19/0.48    ~l1_struct_0(sK0) | spl4_47),
% 0.19/0.48    inference(avatar_component_clause,[],[f369])).
% 0.19/0.48  fof(f372,plain,(
% 0.19/0.48    spl4_3 | ~spl4_47 | ~spl4_46),
% 0.19/0.48    inference(avatar_split_clause,[],[f367,f363,f369,f73])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    spl4_3 <=> v2_struct_0(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.48  fof(f363,plain,(
% 0.19/0.48    spl4_46 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.19/0.48  fof(f367,plain,(
% 0.19/0.48    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_46),
% 0.19/0.48    inference(resolution,[],[f365,f45])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.48  fof(f365,plain,(
% 0.19/0.48    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_46),
% 0.19/0.48    inference(avatar_component_clause,[],[f363])).
% 0.19/0.48  fof(f366,plain,(
% 0.19/0.48    ~spl4_11 | ~spl4_12 | spl4_46 | ~spl4_13 | spl4_45),
% 0.19/0.48    inference(avatar_split_clause,[],[f361,f354,f123,f363,f118,f113])).
% 0.19/0.48  fof(f113,plain,(
% 0.19/0.48    spl4_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.48  fof(f118,plain,(
% 0.19/0.48    spl4_12 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.48  fof(f123,plain,(
% 0.19/0.48    spl4_13 <=> v1_funct_1(sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.48  fof(f354,plain,(
% 0.19/0.48    spl4_45 <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.19/0.48  fof(f361,plain,(
% 0.19/0.48    ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl4_45),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f360])).
% 0.19/0.48  fof(f360,plain,(
% 0.19/0.48    ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl4_45),
% 0.19/0.48    inference(condensation,[],[f359])).
% 0.19/0.48  fof(f359,plain,(
% 0.19/0.48    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ) | spl4_45),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f358])).
% 0.19/0.48  fof(f358,plain,(
% 0.19/0.48    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK0))) ) | spl4_45),
% 0.19/0.48    inference(resolution,[],[f356,f57])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.19/0.48    inference(flattening,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 0.19/0.48  fof(f356,plain,(
% 0.19/0.48    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | spl4_45),
% 0.19/0.48    inference(avatar_component_clause,[],[f354])).
% 0.19/0.48  fof(f357,plain,(
% 0.19/0.48    ~spl4_45 | spl4_21 | ~spl4_44),
% 0.19/0.48    inference(avatar_split_clause,[],[f352,f348,f181,f354])).
% 0.19/0.48  fof(f181,plain,(
% 0.19/0.48    spl4_21 <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.19/0.48  fof(f348,plain,(
% 0.19/0.48    spl4_44 <=> sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.19/0.48  fof(f352,plain,(
% 0.19/0.48    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | (spl4_21 | ~spl4_44)),
% 0.19/0.48    inference(backward_demodulation,[],[f183,f350])).
% 0.19/0.48  fof(f350,plain,(
% 0.19/0.48    sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) | ~spl4_44),
% 0.19/0.48    inference(avatar_component_clause,[],[f348])).
% 0.19/0.48  fof(f183,plain,(
% 0.19/0.48    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | spl4_21),
% 0.19/0.48    inference(avatar_component_clause,[],[f181])).
% 0.19/0.48  fof(f351,plain,(
% 0.19/0.48    spl4_44 | ~spl4_7 | ~spl4_18 | ~spl4_30 | ~spl4_43),
% 0.19/0.48    inference(avatar_split_clause,[],[f346,f341,f257,f159,f93,f348])).
% 0.19/0.48  fof(f93,plain,(
% 0.19/0.48    spl4_7 <=> m1_pre_topc(sK2,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.48  fof(f159,plain,(
% 0.19/0.48    spl4_18 <=> u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.19/0.48  fof(f257,plain,(
% 0.19/0.48    spl4_30 <=> sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.19/0.48  fof(f341,plain,(
% 0.19/0.48    spl4_43 <=> ! [X0] : (k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.19/0.48  fof(f346,plain,(
% 0.19/0.48    sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) | (~spl4_7 | ~spl4_18 | ~spl4_30 | ~spl4_43)),
% 0.19/0.48    inference(forward_demodulation,[],[f345,f259])).
% 0.19/0.48  fof(f259,plain,(
% 0.19/0.48    sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) | ~spl4_30),
% 0.19/0.48    inference(avatar_component_clause,[],[f257])).
% 0.19/0.48  fof(f345,plain,(
% 0.19/0.48    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) | (~spl4_7 | ~spl4_18 | ~spl4_43)),
% 0.19/0.48    inference(forward_demodulation,[],[f344,f161])).
% 0.19/0.48  fof(f161,plain,(
% 0.19/0.48    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl4_18),
% 0.19/0.48    inference(avatar_component_clause,[],[f159])).
% 0.19/0.48  fof(f344,plain,(
% 0.19/0.48    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | (~spl4_7 | ~spl4_43)),
% 0.19/0.48    inference(resolution,[],[f342,f95])).
% 0.19/0.48  fof(f95,plain,(
% 0.19/0.48    m1_pre_topc(sK2,sK1) | ~spl4_7),
% 0.19/0.48    inference(avatar_component_clause,[],[f93])).
% 0.19/0.48  fof(f342,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) ) | ~spl4_43),
% 0.19/0.48    inference(avatar_component_clause,[],[f341])).
% 0.19/0.48  fof(f343,plain,(
% 0.19/0.48    ~spl4_11 | spl4_43 | ~spl4_12 | ~spl4_13 | ~spl4_39),
% 0.19/0.48    inference(avatar_split_clause,[],[f338,f321,f123,f118,f341,f113])).
% 0.19/0.48  fof(f321,plain,(
% 0.19/0.48    spl4_39 <=> ! [X3,X2] : (k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.19/0.48  fof(f338,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1)) ) | (~spl4_13 | ~spl4_39)),
% 0.19/0.48    inference(resolution,[],[f322,f125])).
% 0.19/0.48  fof(f125,plain,(
% 0.19/0.48    v1_funct_1(sK3) | ~spl4_13),
% 0.19/0.48    inference(avatar_component_clause,[],[f123])).
% 0.19/0.48  fof(f322,plain,(
% 0.19/0.48    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X3,sK1)) ) | ~spl4_39),
% 0.19/0.48    inference(avatar_component_clause,[],[f321])).
% 0.19/0.48  fof(f323,plain,(
% 0.19/0.48    ~spl4_4 | spl4_6 | spl4_39 | ~spl4_5 | ~spl4_34),
% 0.19/0.48    inference(avatar_split_clause,[],[f315,f299,f83,f321,f88,f78])).
% 0.19/0.48  fof(f78,plain,(
% 0.19/0.48    spl4_4 <=> l1_pre_topc(sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.48  fof(f88,plain,(
% 0.19/0.48    spl4_6 <=> v2_struct_0(sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.48  fof(f83,plain,(
% 0.19/0.48    spl4_5 <=> v2_pre_topc(sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.48  fof(f299,plain,(
% 0.19/0.48    spl4_34 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.19/0.48  fof(f315,plain,(
% 0.19/0.48    ( ! [X2,X3] : (k2_tmap_1(sK1,sK0,X2,X3) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK1)) ) | (~spl4_5 | ~spl4_34)),
% 0.19/0.48    inference(resolution,[],[f300,f85])).
% 0.19/0.48  fof(f85,plain,(
% 0.19/0.48    v2_pre_topc(sK1) | ~spl4_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f83])).
% 0.19/0.48  fof(f300,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | v2_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl4_34),
% 0.19/0.48    inference(avatar_component_clause,[],[f299])).
% 0.19/0.48  fof(f301,plain,(
% 0.19/0.48    ~spl4_1 | spl4_3 | spl4_34 | ~spl4_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f292,f68,f299,f73,f63])).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    spl4_2 <=> v2_pre_topc(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.48  fof(f292,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,sK0,X1,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),X1,u1_struct_0(X2))) ) | ~spl4_2),
% 0.19/0.48    inference(resolution,[],[f46,f70])).
% 0.19/0.48  fof(f70,plain,(
% 0.19/0.48    v2_pre_topc(sK0) | ~spl4_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f68])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,axiom,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.19/0.48  fof(f260,plain,(
% 0.19/0.48    spl4_30 | ~spl4_29),
% 0.19/0.48    inference(avatar_split_clause,[],[f255,f252,f257])).
% 0.19/0.48  fof(f252,plain,(
% 0.19/0.48    spl4_29 <=> ! [X0] : (~r1_tarski(u1_struct_0(sK1),X0) | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.19/0.48  fof(f255,plain,(
% 0.19/0.48    sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) | ~spl4_29),
% 0.19/0.48    inference(resolution,[],[f253,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.48    inference(equality_resolution,[],[f50])).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.48  fof(f253,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(u1_struct_0(sK1),X0) | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0)) ) | ~spl4_29),
% 0.19/0.48    inference(avatar_component_clause,[],[f252])).
% 0.19/0.48  fof(f254,plain,(
% 0.19/0.48    ~spl4_13 | spl4_29 | ~spl4_11 | ~spl4_12 | ~spl4_28),
% 0.19/0.48    inference(avatar_split_clause,[],[f250,f247,f118,f113,f252,f123])).
% 0.19/0.48  fof(f247,plain,(
% 0.19/0.48    spl4_28 <=> ! [X0] : (~r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3) | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.19/0.48  fof(f250,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tarski(u1_struct_0(sK1),X0) | ~v1_funct_1(sK3) | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0)) ) | ~spl4_28),
% 0.19/0.48    inference(resolution,[],[f52,f248])).
% 0.19/0.48  fof(f248,plain,(
% 0.19/0.48    ( ! [X0] : (~r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3) | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0)) ) | ~spl4_28),
% 0.19/0.48    inference(avatar_component_clause,[],[f247])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X0,X2) | ~v1_funct_1(X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.48    inference(flattening,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).
% 0.19/0.48  fof(f249,plain,(
% 0.19/0.48    ~spl4_11 | spl4_28 | ~spl4_11 | ~spl4_13),
% 0.19/0.48    inference(avatar_split_clause,[],[f244,f123,f113,f247,f113])).
% 0.19/0.48  fof(f244,plain,(
% 0.19/0.48    ( ! [X0] : (~r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0)) ) | (~spl4_11 | ~spl4_13)),
% 0.19/0.48    inference(resolution,[],[f241,f125])).
% 0.19/0.48  fof(f241,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1)) ) | ~spl4_11),
% 0.19/0.48    inference(resolution,[],[f235,f54])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.48    inference(flattening,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.19/0.48  fof(f235,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | sK3 = X0 | ~r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3)) ) | ~spl4_11),
% 0.19/0.48    inference(resolution,[],[f56,f115])).
% 0.19/0.48  fof(f115,plain,(
% 0.19/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl4_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f113])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(flattening,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.48  fof(f184,plain,(
% 0.19/0.48    ~spl4_21 | spl4_9 | ~spl4_18),
% 0.19/0.48    inference(avatar_split_clause,[],[f173,f159,f103,f181])).
% 0.19/0.48  fof(f103,plain,(
% 0.19/0.48    spl4_9 <=> r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.48  fof(f173,plain,(
% 0.19/0.48    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | (spl4_9 | ~spl4_18)),
% 0.19/0.48    inference(backward_demodulation,[],[f105,f161])).
% 0.19/0.48  fof(f105,plain,(
% 0.19/0.48    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | spl4_9),
% 0.19/0.48    inference(avatar_component_clause,[],[f103])).
% 0.19/0.48  fof(f170,plain,(
% 0.19/0.48    ~spl4_4 | spl4_19),
% 0.19/0.48    inference(avatar_split_clause,[],[f168,f163,f78])).
% 0.19/0.48  fof(f163,plain,(
% 0.19/0.48    spl4_19 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.19/0.48  fof(f168,plain,(
% 0.19/0.48    ~l1_pre_topc(sK1) | spl4_19),
% 0.19/0.48    inference(resolution,[],[f165,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.19/0.48  fof(f165,plain,(
% 0.19/0.48    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl4_19),
% 0.19/0.48    inference(avatar_component_clause,[],[f163])).
% 0.19/0.48  fof(f166,plain,(
% 0.19/0.48    spl4_18 | ~spl4_19 | ~spl4_10),
% 0.19/0.48    inference(avatar_split_clause,[],[f157,f108,f163,f159])).
% 0.19/0.48  fof(f108,plain,(
% 0.19/0.48    spl4_10 <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.48  fof(f157,plain,(
% 0.19/0.48    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl4_10),
% 0.19/0.48    inference(equality_resolution,[],[f137])).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | u1_struct_0(sK2) = X0) ) | ~spl4_10),
% 0.19/0.48    inference(superposition,[],[f47,f110])).
% 0.19/0.48  fof(f110,plain,(
% 0.19/0.48    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl4_10),
% 0.19/0.48    inference(avatar_component_clause,[],[f108])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | X0 = X2) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.19/0.48  fof(f126,plain,(
% 0.19/0.48    spl4_13),
% 0.19/0.48    inference(avatar_split_clause,[],[f30,f123])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    v1_funct_1(sK3)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,negated_conjecture,(
% 0.19/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.19/0.48    inference(negated_conjecture,[],[f11])).
% 0.19/0.48  fof(f11,conjecture,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).
% 0.19/0.48  fof(f121,plain,(
% 0.19/0.48    spl4_12),
% 0.19/0.48    inference(avatar_split_clause,[],[f31,f118])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    spl4_11),
% 0.19/0.48    inference(avatar_split_clause,[],[f32,f113])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f111,plain,(
% 0.19/0.48    spl4_10),
% 0.19/0.48    inference(avatar_split_clause,[],[f33,f108])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f106,plain,(
% 0.19/0.48    ~spl4_9),
% 0.19/0.48    inference(avatar_split_clause,[],[f34,f103])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f96,plain,(
% 0.19/0.48    spl4_7),
% 0.19/0.48    inference(avatar_split_clause,[],[f36,f93])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    m1_pre_topc(sK2,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f91,plain,(
% 0.19/0.48    ~spl4_6),
% 0.19/0.48    inference(avatar_split_clause,[],[f37,f88])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ~v2_struct_0(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f86,plain,(
% 0.19/0.48    spl4_5),
% 0.19/0.48    inference(avatar_split_clause,[],[f38,f83])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    v2_pre_topc(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f81,plain,(
% 0.19/0.48    spl4_4),
% 0.19/0.48    inference(avatar_split_clause,[],[f39,f78])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    l1_pre_topc(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f76,plain,(
% 0.19/0.48    ~spl4_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f40,f73])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ~v2_struct_0(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    spl4_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f41,f68])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    v2_pre_topc(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    spl4_1),
% 0.19/0.48    inference(avatar_split_clause,[],[f42,f63])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    l1_pre_topc(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (13596)------------------------------
% 0.19/0.48  % (13596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (13596)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (13596)Memory used [KB]: 6524
% 0.19/0.48  % (13596)Time elapsed: 0.065 s
% 0.19/0.48  % (13596)------------------------------
% 0.19/0.48  % (13596)------------------------------
% 0.19/0.49  % (13580)Success in time 0.136 s
%------------------------------------------------------------------------------
