%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 294 expanded)
%              Number of leaves         :   42 ( 136 expanded)
%              Depth                    :   10
%              Number of atoms          :  431 ( 936 expanded)
%              Number of equality atoms :   35 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f69,f74,f79,f88,f93,f97,f123,f128,f132,f136,f149,f157,f183,f187,f193,f202,f207,f212,f270,f276,f285,f294,f314,f322])).

fof(f322,plain,
    ( spl3_18
    | ~ spl3_25
    | ~ spl3_42 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl3_18
    | ~ spl3_25
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f316,f148])).

fof(f148,plain,
    ( ~ v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_18
  <=> v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f316,plain,
    ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)
    | ~ spl3_25
    | ~ spl3_42 ),
    inference(resolution,[],[f313,f186])).

fof(f186,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl3_25
  <=> ! [X1] : m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f313,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k9_subset_1(X3,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k9_subset_1(X3,sK1,X3),sK0) )
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl3_42
  <=> ! [X3] :
        ( ~ m1_subset_1(k9_subset_1(X3,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k9_subset_1(X3,sK1,X3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f314,plain,
    ( spl3_42
    | ~ spl3_27
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f298,f292,f200,f312])).

fof(f200,plain,
    ( spl3_27
  <=> ! [X1,X0] : r1_tarski(k9_subset_1(X1,X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f292,plain,
    ( spl3_40
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f298,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k9_subset_1(X3,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k9_subset_1(X3,sK1,X3),sK0) )
    | ~ spl3_27
    | ~ spl3_40 ),
    inference(resolution,[],[f293,f201])).

fof(f201,plain,
    ( ! [X0,X1] : r1_tarski(k9_subset_1(X1,X0,X1),X0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f200])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f292])).

fof(f294,plain,
    ( spl3_40
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f290,f268,f81,f71,f292])).

fof(f71,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( spl3_6
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f268,plain,
    ( spl3_38
  <=> ! [X1,X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f289,f73])).

fof(f73,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_6
    | ~ spl3_38 ),
    inference(resolution,[],[f83,f269])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f268])).

fof(f83,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f285,plain,
    ( spl3_18
    | ~ spl3_25
    | ~ spl3_29
    | ~ spl3_39 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl3_18
    | ~ spl3_25
    | ~ spl3_29
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f148,f283])).

fof(f283,plain,
    ( ! [X2] : v2_tex_2(k9_subset_1(sK2,X2,sK2),sK0)
    | ~ spl3_25
    | ~ spl3_29
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f279,f186])).

fof(f279,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k9_subset_1(sK2,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k9_subset_1(sK2,X2,sK2),sK0) )
    | ~ spl3_29
    | ~ spl3_39 ),
    inference(resolution,[],[f275,f211])).

fof(f211,plain,
    ( ! [X0,X1] : r1_tarski(k9_subset_1(X1,X0,X1),X1)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_29
  <=> ! [X1,X0] : r1_tarski(k9_subset_1(X1,X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl3_39
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f276,plain,
    ( spl3_39
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f272,f268,f85,f76,f274])).

fof(f76,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( spl3_7
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f271,f78])).

fof(f78,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_7
    | ~ spl3_38 ),
    inference(resolution,[],[f269,f87])).

fof(f87,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f270,plain,
    ( spl3_38
    | ~ spl3_1
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f246,f181,f58,f268])).

fof(f58,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f181,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( v2_tex_2(X2,X0)
        | ~ v2_tex_2(X1,X0)
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) )
    | ~ spl3_1
    | ~ spl3_24 ),
    inference(resolution,[],[f182,f60])).

fof(f60,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_tex_2(X1,X0)
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_tex_2(X2,X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f212,plain,
    ( spl3_29
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f208,f205,f191,f210])).

fof(f191,plain,
    ( spl3_26
  <=> ! [X1,X0] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f205,plain,
    ( spl3_28
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f208,plain,
    ( ! [X0,X1] : r1_tarski(k9_subset_1(X1,X0,X1),X1)
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(superposition,[],[f206,f192])).

fof(f192,plain,
    ( ! [X0,X1] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f206,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( spl3_28
    | ~ spl3_3
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f197,f191,f126,f67,f205])).

fof(f67,plain,
    ( spl3_3
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(k9_subset_1(X1,X2,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f197,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0)
    | ~ spl3_3
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f194,f68])).

fof(f68,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) )
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(superposition,[],[f127,f192])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_subset_1(X1,X2,X0),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f202,plain,
    ( spl3_27
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f196,f191,f130,f200])).

fof(f130,plain,
    ( spl3_16
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f196,plain,
    ( ! [X0,X1] : r1_tarski(k9_subset_1(X1,X0,X1),X0)
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(superposition,[],[f131,f192])).

fof(f131,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f193,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f137,f134,f67,f191])).

fof(f134,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f137,plain,
    ( ! [X0,X1] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(resolution,[],[f135,f68])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f187,plain,
    ( spl3_25
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f175,f155,f121,f76,f185])).

fof(f121,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f155,plain,
    ( spl3_20
  <=> ! [X10] : k9_subset_1(u1_struct_0(sK0),X10,sK2) = k9_subset_1(sK2,X10,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f175,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f173,f78])).

fof(f173,plain,
    ( ! [X1] :
        ( m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_14
    | ~ spl3_20 ),
    inference(superposition,[],[f122,f156])).

fof(f156,plain,
    ( ! [X10] : k9_subset_1(u1_struct_0(sK0),X10,sK2) = k9_subset_1(sK2,X10,sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f183,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f35,f181])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f157,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f143,f134,f76,f67,f155])).

fof(f143,plain,
    ( ! [X10] : k9_subset_1(u1_struct_0(sK0),X10,sK2) = k9_subset_1(sK2,X10,sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f141,f137])).

fof(f141,plain,
    ( ! [X10] : k9_subset_1(u1_struct_0(sK0),X10,sK2) = k1_setfam_1(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,sK2))
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(resolution,[],[f135,f78])).

fof(f149,plain,
    ( ~ spl3_18
    | ~ spl3_3
    | ~ spl3_5
    | spl3_8
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f144,f134,f90,f76,f67,f146])).

fof(f90,plain,
    ( spl3_8
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f144,plain,
    ( ~ v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)
    | ~ spl3_3
    | ~ spl3_5
    | spl3_8
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f92,f143])).

fof(f92,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f136,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f55,f134])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f132,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f54,f130])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f53])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f128,plain,
    ( spl3_15
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f124,f121,f95,f126])).

fof(f95,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(k9_subset_1(X1,X2,X0),X1) )
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(resolution,[],[f122,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f123,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f42,f121])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f97,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f39,f95])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & ( v2_tex_2(X2,sK0)
              | v2_tex_2(X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & ( v2_tex_2(X2,sK0)
            | v2_tex_2(sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & ( v2_tex_2(X2,sK0)
          | v2_tex_2(sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & ( v2_tex_2(sK2,sK0)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(f88,plain,
    ( spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f31,f85,f81])).

fof(f31,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f76])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f56,f67])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f61,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (13544)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (13544)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (13552)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f61,f69,f74,f79,f88,f93,f97,f123,f128,f132,f136,f149,f157,f183,f187,f193,f202,f207,f212,f270,f276,f285,f294,f314,f322])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    spl3_18 | ~spl3_25 | ~spl3_42),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f321])).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    $false | (spl3_18 | ~spl3_25 | ~spl3_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f316,f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) | spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl3_18 <=> v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) | (~spl3_25 | ~spl3_42)),
% 0.21/0.49    inference(resolution,[],[f313,f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    ( ! [X1] : (m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl3_25 <=> ! [X1] : m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ( ! [X3] : (~m1_subset_1(k9_subset_1(X3,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k9_subset_1(X3,sK1,X3),sK0)) ) | ~spl3_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f312])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    spl3_42 <=> ! [X3] : (~m1_subset_1(k9_subset_1(X3,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k9_subset_1(X3,sK1,X3),sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    spl3_42 | ~spl3_27 | ~spl3_40),
% 0.21/0.49    inference(avatar_split_clause,[],[f298,f292,f200,f312])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    spl3_27 <=> ! [X1,X0] : r1_tarski(k9_subset_1(X1,X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    spl3_40 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ( ! [X3] : (~m1_subset_1(k9_subset_1(X3,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k9_subset_1(X3,sK1,X3),sK0)) ) | (~spl3_27 | ~spl3_40)),
% 0.21/0.49    inference(resolution,[],[f293,f201])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_subset_1(X1,X0,X1),X0)) ) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f200])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl3_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f292])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    spl3_40 | ~spl3_4 | ~spl3_6 | ~spl3_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f290,f268,f81,f71,f292])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl3_6 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    spl3_38 <=> ! [X1,X0] : (~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (~spl3_4 | ~spl3_6 | ~spl3_38)),
% 0.21/0.49    inference(subsumption_resolution,[],[f289,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (~spl3_6 | ~spl3_38)),
% 0.21/0.49    inference(resolution,[],[f83,f269])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) ) | ~spl3_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f268])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    spl3_18 | ~spl3_25 | ~spl3_29 | ~spl3_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    $false | (spl3_18 | ~spl3_25 | ~spl3_29 | ~spl3_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f148,f283])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ( ! [X2] : (v2_tex_2(k9_subset_1(sK2,X2,sK2),sK0)) ) | (~spl3_25 | ~spl3_29 | ~spl3_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f279,f186])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ( ! [X2] : (~m1_subset_1(k9_subset_1(sK2,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k9_subset_1(sK2,X2,sK2),sK0)) ) | (~spl3_29 | ~spl3_39)),
% 0.21/0.49    inference(resolution,[],[f275,f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_subset_1(X1,X0,X1),X1)) ) | ~spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    spl3_29 <=> ! [X1,X0] : r1_tarski(k9_subset_1(X1,X0,X1),X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl3_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f274])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    spl3_39 <=> ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    spl3_39 | ~spl3_5 | ~spl3_7 | ~spl3_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f272,f268,f85,f76,f274])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_7 <=> v2_tex_2(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (~spl3_5 | ~spl3_7 | ~spl3_38)),
% 0.21/0.49    inference(subsumption_resolution,[],[f271,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (~spl3_7 | ~spl3_38)),
% 0.21/0.49    inference(resolution,[],[f269,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    v2_tex_2(sK2,sK0) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    spl3_38 | ~spl3_1 | ~spl3_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f246,f181,f58,f268])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    spl3_24 <=> ! [X1,X0,X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) ) | (~spl3_1 | ~spl3_24)),
% 0.21/0.49    inference(resolution,[],[f182,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) ) | ~spl3_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f181])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl3_29 | ~spl3_26 | ~spl3_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f208,f205,f191,f210])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl3_26 <=> ! [X1,X0] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    spl3_28 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_subset_1(X1,X0,X1),X1)) ) | (~spl3_26 | ~spl3_28)),
% 0.21/0.49    inference(superposition,[],[f206,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) ) | ~spl3_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0)) ) | ~spl3_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f205])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    spl3_28 | ~spl3_3 | ~spl3_15 | ~spl3_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f197,f191,f126,f67,f205])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_3 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl3_15 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k9_subset_1(X1,X2,X0),X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0)) ) | (~spl3_3 | ~spl3_15 | ~spl3_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f194,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl3_15 | ~spl3_26)),
% 0.21/0.49    inference(superposition,[],[f127,f192])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f126])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    spl3_27 | ~spl3_16 | ~spl3_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f196,f191,f130,f200])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl3_16 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_subset_1(X1,X0,X1),X0)) ) | (~spl3_16 | ~spl3_26)),
% 0.21/0.49    inference(superposition,[],[f131,f192])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) ) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl3_26 | ~spl3_3 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f137,f134,f67,f191])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl3_17 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) ) | (~spl3_3 | ~spl3_17)),
% 0.21/0.49    inference(resolution,[],[f135,f68])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f134])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl3_25 | ~spl3_5 | ~spl3_14 | ~spl3_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f175,f155,f121,f76,f185])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl3_14 <=> ! [X1,X0,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl3_20 <=> ! [X10] : k9_subset_1(u1_struct_0(sK0),X10,sK2) = k9_subset_1(sK2,X10,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ( ! [X1] : (m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_5 | ~spl3_14 | ~spl3_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f173,f78])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ( ! [X1] : (m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_14 | ~spl3_20)),
% 0.21/0.49    inference(superposition,[],[f122,f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X10] : (k9_subset_1(u1_struct_0(sK0),X10,sK2) = k9_subset_1(sK2,X10,sK2)) ) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f155])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl3_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f181])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl3_20 | ~spl3_3 | ~spl3_5 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f143,f134,f76,f67,f155])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X10] : (k9_subset_1(u1_struct_0(sK0),X10,sK2) = k9_subset_1(sK2,X10,sK2)) ) | (~spl3_3 | ~spl3_5 | ~spl3_17)),
% 0.21/0.49    inference(forward_demodulation,[],[f141,f137])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X10] : (k9_subset_1(u1_struct_0(sK0),X10,sK2) = k1_setfam_1(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,sK2))) ) | (~spl3_5 | ~spl3_17)),
% 0.21/0.49    inference(resolution,[],[f135,f78])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~spl3_18 | ~spl3_3 | ~spl3_5 | spl3_8 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f144,f134,f90,f76,f67,f146])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_8 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) | (~spl3_3 | ~spl3_5 | spl3_8 | ~spl3_17)),
% 0.21/0.49    inference(backward_demodulation,[],[f92,f143])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f134])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f43,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f37,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f38,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f41,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f44,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f45,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f46,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f130])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f36,f53])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl3_15 | ~spl3_9 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f124,f121,f95,f126])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k9_subset_1(X1,X2,X0),X1)) ) | (~spl3_9 | ~spl3_14)),
% 0.21/0.49    inference(resolution,[],[f122,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f95])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f121])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f95])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f90])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25,f24,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f15])).
% 0.21/0.49  fof(f15,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl3_6 | spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f85,f81])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f76])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f71])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f67])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f34,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (13544)------------------------------
% 0.21/0.50  % (13544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13544)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (13544)Memory used [KB]: 6268
% 0.21/0.50  % (13544)Time elapsed: 0.060 s
% 0.21/0.50  % (13544)------------------------------
% 0.21/0.50  % (13544)------------------------------
% 0.21/0.50  % (13529)Success in time 0.14 s
%------------------------------------------------------------------------------
