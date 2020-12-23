%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 162 expanded)
%              Number of leaves         :   28 (  77 expanded)
%              Depth                    :    7
%              Number of atoms          :  313 ( 624 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f61,f65,f69,f73,f77,f85,f103,f109,f144,f149,f154,f160,f170,f178])).

fof(f178,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f175,f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f175,plain,
    ( r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(resolution,[],[f169,f41])).

fof(f41,plain,
    ( r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
        | r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),sK2)) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_28
  <=> ! [X0] :
        ( r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),sK2))
        | ~ r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f170,plain,
    ( spl3_28
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f165,f158,f44,f168])).

fof(f44,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f158,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f165,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),sK2))
        | ~ r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) )
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(resolution,[],[f159,f46])).

fof(f46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),X1))
        | ~ r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X1))) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f158])).

fof(f160,plain,
    ( spl3_26
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f155,f152,f49,f158])).

fof(f49,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f152,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X2)),k1_tops_2(sK0,X2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X1))) )
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(resolution,[],[f153,f51])).

fof(f51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X2)),k1_tops_2(sK0,X2,X0))) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl3_25
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f150,f147,f75,f152])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f147,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X2,k5_setfam_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,X1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X2)),k1_tops_2(sK0,X2,X0))) )
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(resolution,[],[f148,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,X1))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X2,k5_setfam_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl3_24
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f145,f142,f54,f147])).

fof(f54,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f142,plain,
    ( spl3_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | r1_tarski(X3,k5_setfam_1(u1_struct_0(X1),X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X2,k5_setfam_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,X1)))) )
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(resolution,[],[f143,f56])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f143,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | r1_tarski(X3,k5_setfam_1(u1_struct_0(X1),X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X0)))) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( spl3_23
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f140,f107,f67,f142])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f107,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f140,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | r1_tarski(X3,k5_setfam_1(u1_struct_0(X1),X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X0)))) )
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(resolution,[],[f68,f108])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f109,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f105,f101,f71,f59,f107])).

fof(f59,plain,
    ( spl3_6
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f101,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f104,f60])).

fof(f60,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X2,X1)
        | v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(resolution,[],[f102,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | ~ r1_tarski(X0,X1)
        | r1_tarski(X2,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl3_15
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f99,f83,f63,f101])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f83,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X2,X1)
        | ~ r2_hidden(X2,X0)
        | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X1) )
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(superposition,[],[f84,f64])).

fof(f64,plain,
    ( ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),X1)
        | ~ r2_hidden(X2,X0)
        | r1_tarski(X2,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f57,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
    & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
                & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2))
            & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2))
          & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2))
        & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
      & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                 => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
               => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f34])).

fof(f25,plain,(
    ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:27:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (23721)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (23719)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (23718)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.42  % (23719)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f179,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f61,f65,f69,f73,f77,f85,f103,f109,f144,f149,f154,f160,f170,f178])).
% 0.22/0.42  fof(f178,plain,(
% 0.22/0.42    spl3_1 | ~spl3_2 | ~spl3_28),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.42  fof(f177,plain,(
% 0.22/0.42    $false | (spl3_1 | ~spl3_2 | ~spl3_28)),
% 0.22/0.42    inference(subsumption_resolution,[],[f175,f36])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    ~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) | spl3_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f34])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    spl3_1 <=> r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.42  fof(f175,plain,(
% 0.22/0.42    r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) | (~spl3_2 | ~spl3_28)),
% 0.22/0.42    inference(resolution,[],[f169,f41])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) | ~spl3_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f39])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    spl3_2 <=> r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.42  fof(f169,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) | r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),sK2))) ) | ~spl3_28),
% 0.22/0.42    inference(avatar_component_clause,[],[f168])).
% 0.22/0.42  fof(f168,plain,(
% 0.22/0.42    spl3_28 <=> ! [X0] : (r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),sK2)) | ~r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.42  fof(f170,plain,(
% 0.22/0.42    spl3_28 | ~spl3_3 | ~spl3_26),
% 0.22/0.42    inference(avatar_split_clause,[],[f165,f158,f44,f168])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.42  fof(f158,plain,(
% 0.22/0.42    spl3_26 <=> ! [X1,X0] : (r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X1))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.42  fof(f165,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),sK2)) | ~r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))) ) | (~spl3_3 | ~spl3_26)),
% 0.22/0.42    inference(resolution,[],[f159,f46])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f44])).
% 0.22/0.42  fof(f159,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),X1)) | ~r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X1)))) ) | ~spl3_26),
% 0.22/0.42    inference(avatar_component_clause,[],[f158])).
% 0.22/0.42  fof(f160,plain,(
% 0.22/0.42    spl3_26 | ~spl3_4 | ~spl3_25),
% 0.22/0.42    inference(avatar_split_clause,[],[f155,f152,f49,f158])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.42  fof(f152,plain,(
% 0.22/0.42    spl3_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X2)),k1_tops_2(sK0,X2,X0))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.42  fof(f155,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X1)))) ) | (~spl3_4 | ~spl3_25)),
% 0.22/0.42    inference(resolution,[],[f153,f51])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f49])).
% 0.22/0.42  fof(f153,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X2)),k1_tops_2(sK0,X2,X0)))) ) | ~spl3_25),
% 0.22/0.42    inference(avatar_component_clause,[],[f152])).
% 0.22/0.42  fof(f154,plain,(
% 0.22/0.42    spl3_25 | ~spl3_10 | ~spl3_24),
% 0.22/0.42    inference(avatar_split_clause,[],[f150,f147,f75,f152])).
% 0.22/0.42  fof(f75,plain,(
% 0.22/0.42    spl3_10 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.42  fof(f147,plain,(
% 0.22/0.42    spl3_24 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X2,k5_setfam_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,X1)))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.42  fof(f150,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X2)),k1_tops_2(sK0,X2,X0)))) ) | (~spl3_10 | ~spl3_24)),
% 0.22/0.42    inference(resolution,[],[f148,f76])).
% 0.22/0.42  fof(f76,plain,(
% 0.22/0.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f75])).
% 0.22/0.42  fof(f148,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X2,k5_setfam_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_24),
% 0.22/0.42    inference(avatar_component_clause,[],[f147])).
% 0.22/0.42  fof(f149,plain,(
% 0.22/0.42    spl3_24 | ~spl3_5 | ~spl3_23),
% 0.22/0.42    inference(avatar_split_clause,[],[f145,f142,f54,f147])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    spl3_5 <=> l1_pre_topc(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.42  fof(f142,plain,(
% 0.22/0.42    spl3_23 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | r1_tarski(X3,k5_setfam_1(u1_struct_0(X1),X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X0)))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.42  fof(f145,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X2,k5_setfam_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,X1))))) ) | (~spl3_5 | ~spl3_23)),
% 0.22/0.42    inference(resolution,[],[f143,f56])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    l1_pre_topc(sK0) | ~spl3_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f54])).
% 0.22/0.42  fof(f143,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | r1_tarski(X3,k5_setfam_1(u1_struct_0(X1),X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X0))))) ) | ~spl3_23),
% 0.22/0.42    inference(avatar_component_clause,[],[f142])).
% 0.22/0.42  fof(f144,plain,(
% 0.22/0.42    spl3_23 | ~spl3_8 | ~spl3_16),
% 0.22/0.42    inference(avatar_split_clause,[],[f140,f107,f67,f142])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl3_8 <=> ! [X1,X0,X2] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.42  fof(f107,plain,(
% 0.22/0.42    spl3_16 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.42  fof(f140,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | r1_tarski(X3,k5_setfam_1(u1_struct_0(X1),X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X0))))) ) | (~spl3_8 | ~spl3_16)),
% 0.22/0.42    inference(resolution,[],[f68,f108])).
% 0.22/0.42  fof(f108,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_16),
% 0.22/0.42    inference(avatar_component_clause,[],[f107])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f67])).
% 0.22/0.42  fof(f109,plain,(
% 0.22/0.42    spl3_16 | ~spl3_6 | ~spl3_9 | ~spl3_15),
% 0.22/0.42    inference(avatar_split_clause,[],[f105,f101,f71,f59,f107])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    spl3_6 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    spl3_9 <=> ! [X1,X0] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.42  fof(f101,plain,(
% 0.22/0.42    spl3_15 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.42  fof(f105,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | (~spl3_6 | ~spl3_9 | ~spl3_15)),
% 0.22/0.42    inference(subsumption_resolution,[],[f104,f60])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f59])).
% 0.22/0.42  fof(f104,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X2,X1) | v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | (~spl3_9 | ~spl3_15)),
% 0.22/0.42    inference(resolution,[],[f102,f72])).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl3_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f71])).
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X0,X1) | r1_tarski(X2,X1)) ) | ~spl3_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f101])).
% 0.22/0.42  fof(f103,plain,(
% 0.22/0.42    spl3_15 | ~spl3_7 | ~spl3_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f99,f83,f63,f101])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    spl3_7 <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.42  fof(f83,plain,(
% 0.22/0.42    spl3_12 <=> ! [X1,X0,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.42  fof(f99,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X1)) ) | (~spl3_7 | ~spl3_12)),
% 0.22/0.42    inference(superposition,[],[f84,f64])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) ) | ~spl3_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f63])).
% 0.22/0.42  fof(f84,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) ) | ~spl3_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f83])).
% 0.22/0.42  fof(f85,plain,(
% 0.22/0.42    spl3_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f32,f83])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl3_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f31,f75])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.43    inference(nnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f29,f71])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl3_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f28,f67])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f63])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f59])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f54])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    l1_pre_topc(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ((~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ? [X2] : (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.22/0.43    inference(negated_conjecture,[],[f7])).
% 0.22/0.43  fof(f7,conjecture,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl3_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f49])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    spl3_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f39])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ~spl3_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f25,f34])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (23719)------------------------------
% 0.22/0.43  % (23719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (23719)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (23719)Memory used [KB]: 10618
% 0.22/0.43  % (23719)Time elapsed: 0.007 s
% 0.22/0.43  % (23719)------------------------------
% 0.22/0.43  % (23719)------------------------------
% 0.22/0.43  % (23713)Success in time 0.065 s
%------------------------------------------------------------------------------
