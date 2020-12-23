%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 247 expanded)
%              Number of leaves         :   27 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  530 (1044 expanded)
%              Number of equality atoms :   26 (  40 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f64,f68,f72,f79,f83,f115,f123,f131,f135,f142,f146,f153,f161,f170,f181,f187,f202,f205])).

fof(f205,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_28
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f203,f198])).

fof(f198,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f67,f192])).

fof(f192,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f191,f160])).

fof(f160,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_26
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f191,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f190,f59])).

fof(f59,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f190,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f189,f71])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f189,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_20
    | ~ spl4_28 ),
    inference(resolution,[],[f173,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ v1_tops_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f173,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_28
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f67,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_6
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f203,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(resolution,[],[f201,f82])).

fof(f82,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ v1_subset_1(X1,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_10
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ v1_subset_1(X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f201,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_30
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f202,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f197,f172,f159,f121,f70,f58,f200])).

fof(f197,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f71,f192])).

fof(f187,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f186,f133,f74,f70,f58,f54,f50,f77])).

fof(f77,plain,
    ( spl4_9
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f50,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,
    ( spl4_3
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f74,plain,
    ( spl4_8
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f133,plain,
    ( spl4_23
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | v3_pre_topc(X1,X0)
        | ~ v3_tdlat_3(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f186,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f185,f55])).

fof(f55,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f185,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f184,f51])).

fof(f51,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f184,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f183,f71])).

fof(f183,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f154,f59])).

fof(f154,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl4_8
    | ~ spl4_23 ),
    inference(resolution,[],[f75,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | v3_pre_topc(X1,X0)
        | ~ v3_tdlat_3(X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f133])).

fof(f75,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f181,plain,
    ( spl4_28
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f180,f168,f77,f70,f62,f172])).

fof(f62,plain,
    ( spl4_5
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f168,plain,
    ( spl4_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f180,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f179,f71])).

fof(f179,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f178,f78])).

fof(f78,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f178,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(resolution,[],[f169,f63])).

fof(f63,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl4_27
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f152,f144,f58,f50,f46,f168])).

fof(f46,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | ~ v3_tex_2(X1,X0)
        | v1_tops_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f151,f59])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f150,f51])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) )
    | spl4_1
    | ~ spl4_25 ),
    inference(resolution,[],[f145,f47])).

fof(f47,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | ~ v3_tex_2(X1,X0)
        | v1_tops_1(X1,X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f144])).

fof(f161,plain,
    ( spl4_26
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f157,f113,f74,f70,f58,f159])).

fof(f113,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f157,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f156,f59])).

fof(f156,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f155,f71])).

fof(f155,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(resolution,[],[f75,f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f153,plain,
    ( spl4_8
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f149,f140,f77,f70,f74])).

fof(f140,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f149,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f147,f71])).

fof(f147,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(resolution,[],[f141,f78])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f140])).

fof(f146,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f33,f144])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f142,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f138,f129,f58,f54,f50,f140])).

fof(f129,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v4_pre_topc(X1,X0)
        | ~ v3_tdlat_3(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f137,f55])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0)
        | ~ v3_tdlat_3(sK0) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f136,f59])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0)
        | ~ v3_tdlat_3(sK0) )
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(resolution,[],[f130,f51])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v4_pre_topc(X1,X0)
        | ~ v3_tdlat_3(X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f129])).

fof(f135,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f38,f133])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f131,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f34,f129])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(f123,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f32,f121])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f115,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f30,f113])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f83,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f44,f81])).

fof(f44,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f79,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f21,f77,f74])).

fof(f21,plain,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

% (7523)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (7525)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(f72,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f22,f70])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f66])).

fof(f24,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (7540)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (7532)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (7532)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f64,f68,f72,f79,f83,f115,f123,f131,f135,f142,f146,f153,f161,f170,f181,f187,f202,f205])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_20 | ~spl4_26 | ~spl4_28 | ~spl4_30),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f204])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    $false | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_20 | ~spl4_26 | ~spl4_28 | ~spl4_30)),
% 0.21/0.46    inference(subsumption_resolution,[],[f203,f198])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    v1_subset_1(sK1,sK1) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_20 | ~spl4_26 | ~spl4_28)),
% 0.21/0.46    inference(backward_demodulation,[],[f67,f192])).
% 0.21/0.46  fof(f192,plain,(
% 0.21/0.46    sK1 = u1_struct_0(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_20 | ~spl4_26 | ~spl4_28)),
% 0.21/0.46    inference(forward_demodulation,[],[f191,f160])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    sK1 = k2_pre_topc(sK0,sK1) | ~spl4_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f159])).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    spl4_26 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.46  fof(f191,plain,(
% 0.21/0.46    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_7 | ~spl4_20 | ~spl4_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f190,f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    l1_pre_topc(sK0) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl4_4 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl4_7 | ~spl4_20 | ~spl4_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f189,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl4_20 | ~spl4_28)),
% 0.21/0.46    inference(resolution,[],[f173,f122])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) ) | ~spl4_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f121])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    spl4_20 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    v1_tops_1(sK1,sK0) | ~spl4_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f172])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    spl4_28 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl4_6 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    ~v1_subset_1(sK1,sK1) | (~spl4_10 | ~spl4_30)),
% 0.21/0.46    inference(resolution,[],[f201,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) ) | ~spl4_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl4_10 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl4_30),
% 0.21/0.46    inference(avatar_component_clause,[],[f200])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    spl4_30 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    spl4_30 | ~spl4_4 | ~spl4_7 | ~spl4_20 | ~spl4_26 | ~spl4_28),
% 0.21/0.46    inference(avatar_split_clause,[],[f197,f172,f159,f121,f70,f58,f200])).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl4_4 | ~spl4_7 | ~spl4_20 | ~spl4_26 | ~spl4_28)),
% 0.21/0.46    inference(backward_demodulation,[],[f71,f192])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    spl4_9 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f186,f133,f74,f70,f58,f54,f50,f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl4_9 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl4_3 <=> v3_tdlat_3(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl4_8 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl4_23 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    v3_pre_topc(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f185,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    v3_tdlat_3(sK0) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f54])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0) | (~spl4_2 | ~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f184,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    v2_pre_topc(sK0) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f183,f71])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0) | (~spl4_4 | ~spl4_8 | ~spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f154,f59])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0) | (~spl4_8 | ~spl4_23)),
% 0.21/0.46    inference(resolution,[],[f75,f134])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) ) | ~spl4_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f133])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    v4_pre_topc(sK1,sK0) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f74])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    spl4_28 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_27),
% 0.21/0.46    inference(avatar_split_clause,[],[f180,f168,f77,f70,f62,f172])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl4_5 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    spl4_27 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.46  fof(f180,plain,(
% 0.21/0.46    v1_tops_1(sK1,sK0) | (~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_27)),
% 0.21/0.46    inference(subsumption_resolution,[],[f179,f71])).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0) | (~spl4_5 | ~spl4_9 | ~spl4_27)),
% 0.21/0.46    inference(subsumption_resolution,[],[f178,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    v3_pre_topc(sK1,sK0) | ~spl4_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0) | (~spl4_5 | ~spl4_27)),
% 0.21/0.46    inference(resolution,[],[f169,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    v3_tex_2(sK1,sK0) | ~spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f62])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | ~spl4_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f168])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    spl4_27 | spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_25),
% 0.21/0.46    inference(avatar_split_clause,[],[f152,f144,f58,f50,f46,f168])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    spl4_25 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_25)),
% 0.21/0.46    inference(subsumption_resolution,[],[f151,f59])).
% 0.21/0.46  fof(f151,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_25)),
% 0.21/0.46    inference(subsumption_resolution,[],[f150,f51])).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) ) | (spl4_1 | ~spl4_25)),
% 0.21/0.46    inference(resolution,[],[f145,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f46])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) ) | ~spl4_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f144])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    spl4_26 | ~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f157,f113,f74,f70,f58,f159])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    spl4_18 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    sK1 = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f156,f59])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1) | (~spl4_7 | ~spl4_8 | ~spl4_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f155,f71])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1) | (~spl4_8 | ~spl4_18)),
% 0.21/0.46    inference(resolution,[],[f75,f114])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) ) | ~spl4_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f113])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    spl4_8 | ~spl4_7 | ~spl4_9 | ~spl4_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f149,f140,f77,f70,f74])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    spl4_24 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    v4_pre_topc(sK1,sK0) | (~spl4_7 | ~spl4_9 | ~spl4_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f147,f71])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | (~spl4_9 | ~spl4_24)),
% 0.21/0.46    inference(resolution,[],[f141,f78])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl4_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f140])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    spl4_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f144])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl4_24 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f138,f129,f58,f54,f50,f140])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl4_22 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f137,f55])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0) | ~v3_tdlat_3(sK0)) ) | (~spl4_2 | ~spl4_4 | ~spl4_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f136,f59])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0) | ~v3_tdlat_3(sK0)) ) | (~spl4_2 | ~spl4_22)),
% 0.21/0.47    inference(resolution,[],[f130,f51])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) ) | ~spl4_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f129])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl4_23),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f133])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    spl4_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f129])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    spl4_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f121])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl4_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f113])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl4_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f44,f81])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl4_8 | spl4_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f77,f74])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    v3_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  % (7523)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (7525)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl4_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f70])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f66])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f62])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v3_tex_2(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f54])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v3_tdlat_3(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f50])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f46])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (7532)------------------------------
% 0.21/0.47  % (7532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7532)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (7532)Memory used [KB]: 10618
% 0.21/0.47  % (7532)Time elapsed: 0.052 s
% 0.21/0.47  % (7532)------------------------------
% 0.21/0.47  % (7532)------------------------------
% 0.21/0.47  % (7522)Success in time 0.115 s
%------------------------------------------------------------------------------
