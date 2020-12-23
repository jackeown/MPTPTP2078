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
% DateTime   : Thu Dec  3 13:15:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 225 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :    7
%              Number of atoms          :  435 ( 701 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f73,f77,f81,f85,f89,f93,f97,f103,f108,f112,f118,f130,f135,f139,f152,f169,f176,f181,f188,f192,f201,f207,f212])).

fof(f212,plain,
    ( ~ spl3_9
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f80,f197])).

fof(f197,plain,
    ( ! [X2] : ~ r1_tarski(X2,k2_struct_0(sK0))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl3_32
  <=> ! [X2] : ~ r1_tarski(X2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f80,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_9
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f207,plain,
    ( ~ spl3_11
    | spl3_30
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl3_11
    | spl3_30
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f203,f187])).

fof(f187,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_30
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f203,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_11
    | ~ spl3_33 ),
    inference(resolution,[],[f200,f88])).

fof(f88,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_11
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f200,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_33
  <=> r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f201,plain,
    ( spl3_32
    | spl3_33
    | ~ spl3_17
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f194,f190,f116,f199,f196])).

fof(f116,plain,
    ( spl3_17
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f190,plain,
    ( spl3_31
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f194,plain,
    ( ! [X2] :
        ( r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X2,k2_struct_0(sK0)) )
    | ~ spl3_17
    | ~ spl3_31 ),
    inference(resolution,[],[f191,f117])).

fof(f117,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f116])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X2,X1) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl3_31
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f177,f174,f75,f190])).

fof(f75,plain,
    ( spl3_8
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f174,plain,
    ( spl3_28
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,X1)
        | r2_hidden(X2,X1)
        | ~ r1_tarski(X3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X2,X1) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(resolution,[],[f175,f76])).

fof(f76,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f175,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,X1)
        | r2_hidden(X2,X1)
        | ~ r1_tarski(X3,X0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f174])).

fof(f188,plain,
    ( ~ spl3_30
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_16
    | spl3_29 ),
    inference(avatar_split_clause,[],[f184,f179,f110,f55,f51,f186])).

fof(f51,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f110,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f179,plain,
    ( spl3_29
  <=> r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f184,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_16
    | spl3_29 ),
    inference(subsumption_resolution,[],[f183,f52])).

fof(f52,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f183,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_16
    | spl3_29 ),
    inference(subsumption_resolution,[],[f182,f56])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f182,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_16
    | spl3_29 ),
    inference(superposition,[],[f180,f111])).

fof(f111,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f180,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,
    ( ~ spl3_29
    | spl3_5
    | ~ spl3_17
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f172,f167,f116,f63,f179])).

fof(f63,plain,
    ( spl3_5
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f167,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f172,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | spl3_5
    | ~ spl3_17
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f170,f117])).

fof(f170,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_5
    | ~ spl3_27 ),
    inference(resolution,[],[f168,f64])).

fof(f64,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f168,plain,
    ( ! [X0] :
        ( m2_connsp_2(k2_struct_0(sK0),sK0,X0)
        | ~ r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f167])).

fof(f176,plain,
    ( spl3_28
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f144,f137,f91,f174])).

fof(f91,plain,
    ( spl3_12
  <=> ! [X0,X2] :
        ( ~ r1_tarski(X2,X0)
        | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f137,plain,
    ( spl3_22
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,X1)
        | r2_hidden(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f144,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,X1)
        | r2_hidden(X2,X1)
        | ~ r1_tarski(X3,X0) )
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(resolution,[],[f138,f92])).

fof(f92,plain,
    ( ! [X2,X0] :
        ( r2_hidden(X2,k1_zfmisc_1(X0))
        | ~ r1_tarski(X2,X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f138,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X3,X1)
        | r2_hidden(X3,X1) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f169,plain,
    ( spl3_27
    | ~ spl3_8
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f153,f150,f75,f167])).

fof(f150,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0)))
        | m2_connsp_2(k2_struct_0(sK0),sK0,X0) )
    | ~ spl3_8
    | ~ spl3_24 ),
    inference(resolution,[],[f151,f76])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl3_24
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f148,f133,f128,f55,f51,f150])).

fof(f128,plain,
    ( spl3_20
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f133,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(X1,k1_tops_1(X0,X2))
        | m2_connsp_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f147,f129])).

fof(f129,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f128])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f146,f129])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f145,f56])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(resolution,[],[f134,f52])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(X1,k1_tops_1(X0,X2))
        | m2_connsp_2(X2,X0,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f133])).

fof(f139,plain,
    ( spl3_22
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f104,f101,f95,f137])).

fof(f95,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f101,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f104,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,X1)
        | r2_hidden(X3,X1) )
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(resolution,[],[f102,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f135,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f34,f133])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f130,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f113,f106,f55,f128])).

fof(f106,plain,
    ( spl3_15
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f113,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(resolution,[],[f107,f56])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f118,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f114,f106,f59,f55,f116])).

fof(f59,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f114,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f60,f113])).

fof(f60,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f112,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f33,f110])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f108,plain,
    ( spl3_15
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f98,f83,f71,f106])).

fof(f71,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f83,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f98,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f84,f72])).

fof(f72,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f103,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f42,f101])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f97,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f93,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f89,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f85,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f83])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f81,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f77,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f30,f29])).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f73,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f65,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f61,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (6881)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (6882)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (6881)Refutation not found, incomplete strategy% (6881)------------------------------
% 0.21/0.47  % (6881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (6881)Memory used [KB]: 6140
% 0.21/0.47  % (6881)Time elapsed: 0.063 s
% 0.21/0.47  % (6881)------------------------------
% 0.21/0.47  % (6881)------------------------------
% 0.21/0.48  % (6882)Refutation not found, incomplete strategy% (6882)------------------------------
% 0.21/0.48  % (6882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (6882)Memory used [KB]: 10618
% 0.21/0.48  % (6882)Time elapsed: 0.060 s
% 0.21/0.48  % (6882)------------------------------
% 0.21/0.48  % (6882)------------------------------
% 0.21/0.48  % (6889)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (6890)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (6896)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (6890)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f73,f77,f81,f85,f89,f93,f97,f103,f108,f112,f118,f130,f135,f139,f152,f169,f176,f181,f188,f192,f201,f207,f212])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    ~spl3_9 | ~spl3_32),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    $false | (~spl3_9 | ~spl3_32)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f80,f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    ( ! [X2] : (~r1_tarski(X2,k2_struct_0(sK0))) ) | ~spl3_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f196])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    spl3_32 <=> ! [X2] : ~r1_tarski(X2,k2_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_9 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ~spl3_11 | spl3_30 | ~spl3_33),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    $false | (~spl3_11 | spl3_30 | ~spl3_33)),
% 0.21/0.48    inference(subsumption_resolution,[],[f203,f187])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k2_struct_0(sK0)) | spl3_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl3_30 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    r1_tarski(sK1,k2_struct_0(sK0)) | (~spl3_11 | ~spl3_33)),
% 0.21/0.48    inference(resolution,[],[f200,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl3_11 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f199])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    spl3_33 <=> r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl3_32 | spl3_33 | ~spl3_17 | ~spl3_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f194,f190,f116,f199,f196])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl3_17 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    spl3_31 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X2,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ( ! [X2] : (r2_hidden(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,k2_struct_0(sK0))) ) | (~spl3_17 | ~spl3_31)),
% 0.21/0.49    inference(resolution,[],[f191,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X2,X1)) ) | ~spl3_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f190])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    spl3_31 | ~spl3_8 | ~spl3_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f177,f174,f75,f190])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_8 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl3_28 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,X1) | r2_hidden(X2,X1) | ~r1_tarski(X3,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X2,X1)) ) | (~spl3_8 | ~spl3_28)),
% 0.21/0.49    inference(resolution,[],[f175,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,X1) | r2_hidden(X2,X1) | ~r1_tarski(X3,X0)) ) | ~spl3_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f174])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ~spl3_30 | ~spl3_2 | ~spl3_3 | ~spl3_16 | spl3_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f184,f179,f110,f55,f51,f186])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_2 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_3 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl3_16 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl3_29 <=> r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k2_struct_0(sK0)) | (~spl3_2 | ~spl3_3 | ~spl3_16 | spl3_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f183,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_16 | spl3_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f182,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_16 | spl3_29)),
% 0.21/0.49    inference(superposition,[],[f180,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f110])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f179])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ~spl3_29 | spl3_5 | ~spl3_17 | ~spl3_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f172,f167,f116,f63,f179])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_5 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    spl3_27 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | (spl3_5 | ~spl3_17 | ~spl3_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f170,f117])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (spl3_5 | ~spl3_27)),
% 0.21/0.49    inference(resolution,[],[f168,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ( ! [X0] : (m2_connsp_2(k2_struct_0(sK0),sK0,X0) | ~r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f167])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl3_28 | ~spl3_12 | ~spl3_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f144,f137,f91,f174])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl3_12 <=> ! [X0,X2] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl3_22 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,X1) | r2_hidden(X3,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,X1) | r2_hidden(X2,X1) | ~r1_tarski(X3,X0)) ) | (~spl3_12 | ~spl3_22)),
% 0.21/0.49    inference(resolution,[],[f138,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X3,X1) | r2_hidden(X3,X1)) ) | ~spl3_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl3_27 | ~spl3_8 | ~spl3_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f153,f150,f75,f167])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl3_24 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) ) | (~spl3_8 | ~spl3_24)),
% 0.21/0.49    inference(resolution,[],[f151,f76])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | ~spl3_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f150])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    spl3_24 | ~spl3_2 | ~spl3_3 | ~spl3_20 | ~spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f148,f133,f128,f55,f51,f150])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl3_20 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl3_21 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_20 | ~spl3_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f147,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_20 | ~spl3_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f146,f129])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f145,f56])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_21)),
% 0.21/0.49    inference(resolution,[],[f134,f52])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) ) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f133])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl3_22 | ~spl3_13 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f104,f101,f95,f137])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl3_13 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl3_14 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,X1) | r2_hidden(X3,X1)) ) | (~spl3_13 | ~spl3_14)),
% 0.21/0.49    inference(resolution,[],[f102,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) ) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f95])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f133])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl3_20 | ~spl3_3 | ~spl3_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f113,f106,f55,f128])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl3_15 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_3 | ~spl3_15)),
% 0.21/0.49    inference(resolution,[],[f107,f56])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f106])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl3_17 | ~spl3_3 | ~spl3_4 | ~spl3_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f114,f106,f59,f55,f116])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_4 | ~spl3_15)),
% 0.21/0.49    inference(backward_demodulation,[],[f60,f113])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f110])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl3_15 | ~spl3_7 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f83,f71,f106])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_7 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl3_10 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl3_7 | ~spl3_10)),
% 0.21/0.49    inference(resolution,[],[f84,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f101])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f95])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f91])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f87])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f83])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f79])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f75])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f30,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f71])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f63])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f59])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f55])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f51])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (6890)------------------------------
% 0.21/0.49  % (6890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6890)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (6890)Memory used [KB]: 10618
% 0.21/0.49  % (6890)Time elapsed: 0.079 s
% 0.21/0.49  % (6890)------------------------------
% 0.21/0.49  % (6890)------------------------------
% 0.21/0.49  % (6886)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (6880)Success in time 0.133 s
%------------------------------------------------------------------------------
