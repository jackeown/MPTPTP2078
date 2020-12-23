%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 229 expanded)
%              Number of leaves         :   37 ( 100 expanded)
%              Depth                    :    6
%              Number of atoms          :  473 ( 788 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f101,f107,f117,f121,f125,f133,f138,f143,f149,f155,f162,f170,f181,f195,f201])).

fof(f201,plain,
    ( ~ spl4_4
    | ~ spl4_19
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_19
    | spl4_29 ),
    inference(subsumption_resolution,[],[f197,f58])).

% (28659)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f58,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f197,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_19
    | spl4_29 ),
    inference(resolution,[],[f180,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f180,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_29
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f195,plain,
    ( ~ spl4_14
    | ~ spl4_19
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_19
    | spl4_28 ),
    inference(subsumption_resolution,[],[f191,f100])).

fof(f100,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_14
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f191,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_19
    | spl4_28 ),
    inference(resolution,[],[f177,f124])).

fof(f177,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_28
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f181,plain,
    ( ~ spl4_28
    | ~ spl4_29
    | spl4_15
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f172,f168,f105,f179,f176])).

fof(f105,plain,
    ( spl4_15
  <=> v1_tops_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f168,plain,
    ( spl4_27
  <=> ! [X0] :
        ( v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f172,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | spl4_15
    | ~ spl4_27 ),
    inference(resolution,[],[f169,f106])).

fof(f106,plain,
    ( ~ v1_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f105])).

fof(f169,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl4_27
    | ~ spl4_1
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f166,f160,f115,f45,f168])).

fof(f45,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f115,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | r2_hidden(sK3(X0,X1),X1)
        | v1_tops_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f160,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f166,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | ~ spl4_1
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f165,f46])).

fof(f46,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f165,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0)
        | v1_tops_2(X0,sK0) )
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(resolution,[],[f161,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v1_tops_2(X1,X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK0,X0),X1)
        | v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl4_26
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f157,f153,f73,f160])).

fof(f73,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f153,plain,
    ( spl4_25
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) )
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(resolution,[],[f154,f74])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl4_25
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f151,f147,f57,f49,f153])).

fof(f49,plain,
    ( spl4_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f147,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f150,f58])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(resolution,[],[f148,f50])).

fof(f50,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl4_24
    | ~ spl4_1
    | ~ spl4_18
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f145,f141,f119,f45,f147])).

fof(f119,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v3_pre_topc(sK3(X0,X1),X0)
        | v1_tops_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f141,plain,
    ( spl4_23
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X1,X0)
        | v3_pre_topc(X1,sK0)
        | ~ v1_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl4_1
    | ~ spl4_18
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f144,f46])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0)
        | v1_tops_2(X0,sK0) )
    | ~ spl4_18
    | ~ spl4_23 ),
    inference(resolution,[],[f142,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK3(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v1_tops_2(X1,X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(X1,sK0)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X0,sK0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl4_23
    | ~ spl4_1
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f139,f136,f45,f141])).

fof(f136,plain,
    ( spl4_22
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r2_hidden(X2,X1)
        | v3_pre_topc(X2,X0)
        | ~ v1_tops_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X1,X0)
        | v3_pre_topc(X1,sK0)
        | ~ v1_tops_2(X0,sK0) )
    | ~ spl4_1
    | ~ spl4_22 ),
    inference(resolution,[],[f137,f46])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r2_hidden(X2,X1)
        | v3_pre_topc(X2,X0)
        | ~ v1_tops_2(X1,X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl4_22
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f134,f131,f77,f136])).

fof(f77,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f131,plain,
    ( spl4_21
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(X2,X1)
        | v3_pre_topc(X2,X0)
        | ~ v1_tops_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r2_hidden(X2,X1)
        | v3_pre_topc(X2,X0)
        | ~ v1_tops_2(X1,X0) )
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f132,f78])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(X2,X1)
        | v3_pre_topc(X2,X0)
        | ~ v1_tops_2(X1,X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f30,f131])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f125,plain,
    ( spl4_19
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f109,f93,f85,f123])).

fof(f85,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f93,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(superposition,[],[f86,f94])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f121,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f33,f119])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f32,f115])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,
    ( ~ spl4_15
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f103,f89,f61,f53,f105])).

fof(f53,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f61,plain,
    ( spl4_5
  <=> v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f89,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f103,plain,
    ( ~ v1_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f102,f54])).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f102,plain,
    ( ~ v1_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_5
    | ~ spl4_12 ),
    inference(superposition,[],[f62,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f62,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f101,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f97,f81,f69,f65,f99])).

fof(f65,plain,
    ( spl4_6
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f69,plain,
    ( spl4_7
  <=> ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f81,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f97,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f96,f66])).

fof(f66,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f96,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(superposition,[],[f82,f70])).

fof(f70,plain,
    ( ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f95,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f40,f93])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

fof(f91,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f87,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_subset_1)).

fof(f83,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f79,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f75,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f71,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f43,f69])).

% (28661)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f43,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f67,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f63,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f13])).

% (28671)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

fof(f59,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f28,f45])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (28660)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (28656)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (28658)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (28674)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (28665)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (28656)Refutation not found, incomplete strategy% (28656)------------------------------
% 0.22/0.48  % (28656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28656)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (28656)Memory used [KB]: 10618
% 0.22/0.48  % (28656)Time elapsed: 0.061 s
% 0.22/0.48  % (28656)------------------------------
% 0.22/0.48  % (28656)------------------------------
% 0.22/0.48  % (28665)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f101,f107,f117,f121,f125,f133,f138,f143,f149,f155,f162,f170,f181,f195,f201])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    ~spl4_4 | ~spl4_19 | spl4_29),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f200])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    $false | (~spl4_4 | ~spl4_19 | spl4_29)),
% 0.22/0.48    inference(subsumption_resolution,[],[f197,f58])).
% 0.22/0.48  % (28659)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl4_19 | spl4_29)),
% 0.22/0.48    inference(resolution,[],[f180,f124])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    spl4_19 <=> ! [X1,X0,X2] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f179])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    spl4_29 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    ~spl4_14 | ~spl4_19 | spl4_28),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f194])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    $false | (~spl4_14 | ~spl4_19 | spl4_28)),
% 0.22/0.48    inference(subsumption_resolution,[],[f191,f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl4_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl4_14 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl4_19 | spl4_28)),
% 0.22/0.48    inference(resolution,[],[f177,f124])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | spl4_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f176])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    spl4_28 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    ~spl4_28 | ~spl4_29 | spl4_15 | ~spl4_27),
% 0.22/0.48    inference(avatar_split_clause,[],[f172,f168,f105,f179,f176])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl4_15 <=> v1_tops_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    spl4_27 <=> ! [X0] : (v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | (spl4_15 | ~spl4_27)),
% 0.22/0.48    inference(resolution,[],[f169,f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ~v1_tops_2(k3_xboole_0(sK1,sK2),sK0) | spl4_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f105])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    ( ! [X0] : (v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | ~spl4_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f168])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    spl4_27 | ~spl4_1 | ~spl4_17 | ~spl4_26),
% 0.22/0.48    inference(avatar_split_clause,[],[f166,f160,f115,f45,f168])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl4_1 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    spl4_17 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),X1) | v1_tops_2(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    spl4_26 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    ( ! [X0] : (v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | (~spl4_1 | ~spl4_17 | ~spl4_26)),
% 0.22/0.48    inference(subsumption_resolution,[],[f165,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    l1_pre_topc(sK0) | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f45])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    ( ! [X0] : (v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0)) ) | (~spl4_17 | ~spl4_26)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f163])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    ( ! [X0] : (v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v1_tops_2(X0,sK0)) ) | (~spl4_17 | ~spl4_26)),
% 0.22/0.48    inference(resolution,[],[f161,f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v1_tops_2(X1,X0)) ) | ~spl4_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f115])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,X0),X1) | v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(sK1))) ) | ~spl4_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f160])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    spl4_26 | ~spl4_8 | ~spl4_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f157,f153,f73,f160])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl4_8 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    spl4_25 <=> ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1))) ) | (~spl4_8 | ~spl4_25)),
% 0.22/0.48    inference(resolution,[],[f154,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f73])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | ~spl4_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f153])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    spl4_25 | ~spl4_2 | ~spl4_4 | ~spl4_24),
% 0.22/0.48    inference(avatar_split_clause,[],[f151,f147,f57,f49,f153])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl4_2 <=> v1_tops_2(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl4_24 <=> ! [X1,X0] : (~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | (~spl4_2 | ~spl4_4 | ~spl4_24)),
% 0.22/0.48    inference(subsumption_resolution,[],[f150,f58])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | (~spl4_2 | ~spl4_24)),
% 0.22/0.48    inference(resolution,[],[f148,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    v1_tops_2(sK1,sK0) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f49])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | ~spl4_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f147])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    spl4_24 | ~spl4_1 | ~spl4_18 | ~spl4_23),
% 0.22/0.48    inference(avatar_split_clause,[],[f145,f141,f119,f45,f147])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    spl4_18 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(sK3(X0,X1),X0) | v1_tops_2(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    spl4_23 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X0) | v3_pre_topc(X1,sK0) | ~v1_tops_2(X0,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | (~spl4_1 | ~spl4_18 | ~spl4_23)),
% 0.22/0.48    inference(subsumption_resolution,[],[f144,f46])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v1_tops_2(X0,sK0)) ) | (~spl4_18 | ~spl4_23)),
% 0.22/0.48    inference(resolution,[],[f142,f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v1_tops_2(X1,X0)) ) | ~spl4_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f119])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v3_pre_topc(X1,sK0) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X0,sK0)) ) | ~spl4_23),
% 0.22/0.48    inference(avatar_component_clause,[],[f141])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl4_23 | ~spl4_1 | ~spl4_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f139,f136,f45,f141])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl4_22 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X0) | v3_pre_topc(X1,sK0) | ~v1_tops_2(X0,sK0)) ) | (~spl4_1 | ~spl4_22)),
% 0.22/0.48    inference(resolution,[],[f137,f46])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0)) ) | ~spl4_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f136])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    spl4_22 | ~spl4_9 | ~spl4_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f134,f131,f77,f136])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl4_9 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl4_21 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0)) ) | (~spl4_9 | ~spl4_21)),
% 0.22/0.48    inference(subsumption_resolution,[],[f132,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl4_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f77])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0)) ) | ~spl4_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f131])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl4_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f30,f131])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl4_19 | ~spl4_11 | ~spl4_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f109,f93,f85,f123])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl4_11 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl4_13 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl4_11 | ~spl4_13)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl4_11 | ~spl4_13)),
% 0.22/0.48    inference(superposition,[],[f86,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f93])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f85])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    spl4_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f119])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(sK3(X0,X1),X0) | v1_tops_2(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    spl4_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f115])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),X1) | v1_tops_2(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ~spl4_15 | ~spl4_3 | spl4_5 | ~spl4_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f103,f89,f61,f53,f105])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl4_5 <=> v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    spl4_12 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ~v1_tops_2(k3_xboole_0(sK1,sK2),sK0) | (~spl4_3 | spl4_5 | ~spl4_12)),
% 0.22/0.48    inference(subsumption_resolution,[],[f102,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f53])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ~v1_tops_2(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl4_5 | ~spl4_12)),
% 0.22/0.48    inference(superposition,[],[f62,f90])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl4_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f89])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    spl4_14 | ~spl4_6 | ~spl4_7 | ~spl4_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f97,f81,f69,f65,f99])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl4_6 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl4_7 <=> ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl4_10 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl4_6 | ~spl4_7 | ~spl4_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f96,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f65])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl4_7 | ~spl4_10)),
% 0.22/0.48    inference(superposition,[],[f82,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) ) | ~spl4_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f69])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f81])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl4_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f93])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl4_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f39,f89])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl4_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f85])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_subset_1)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl4_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f81])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl4_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f41,f77])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f73])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f43,f69])).
% 0.22/0.48  % (28661)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f42,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(equality_resolution,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f65])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ~spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f61])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  % (28671)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f57])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f53])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f49])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    v1_tops_2(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f45])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (28665)------------------------------
% 0.22/0.48  % (28665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28665)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (28665)Memory used [KB]: 10746
% 0.22/0.48  % (28665)Time elapsed: 0.080 s
% 0.22/0.48  % (28665)------------------------------
% 0.22/0.48  % (28665)------------------------------
% 0.22/0.49  % (28654)Success in time 0.126 s
%------------------------------------------------------------------------------
