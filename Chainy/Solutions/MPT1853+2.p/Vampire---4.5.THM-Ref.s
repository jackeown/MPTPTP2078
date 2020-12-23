%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1853+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 222 expanded)
%              Number of leaves         :   30 ( 101 expanded)
%              Depth                    :    9
%              Number of atoms          :  446 ( 846 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6737,f6740,f6744,f6748,f6752,f6819,f6823,f6880,f6898,f6909,f6911,f6987,f6994,f7005,f7227,f7245,f7248,f7250])).

fof(f7250,plain,
    ( spl323_5
    | ~ spl323_34
    | ~ spl323_4
    | ~ spl323_35
    | spl323_36
    | ~ spl323_1 ),
    inference(avatar_split_clause,[],[f7249,f6732,f6892,f6889,f6746,f6886,f6750])).

fof(f6750,plain,
    ( spl323_5
  <=> v2_struct_0(sK147) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_5])])).

fof(f6886,plain,
    ( spl323_34
  <=> v7_struct_0(sK147) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_34])])).

fof(f6746,plain,
    ( spl323_4
  <=> l1_pre_topc(sK147) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_4])])).

fof(f6889,plain,
    ( spl323_35
  <=> m1_pre_topc(k1_tex_2(sK147,sK148),sK147) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_35])])).

fof(f6892,plain,
    ( spl323_36
  <=> v2_struct_0(k1_tex_2(sK147,sK148)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_36])])).

fof(f6732,plain,
    ( spl323_1
  <=> v1_tex_2(k1_tex_2(sK147,sK148),sK147) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_1])])).

fof(f7249,plain,
    ( v2_struct_0(k1_tex_2(sK147,sK148))
    | ~ m1_pre_topc(k1_tex_2(sK147,sK148),sK147)
    | ~ l1_pre_topc(sK147)
    | ~ v7_struct_0(sK147)
    | v2_struct_0(sK147)
    | ~ spl323_1 ),
    inference(resolution,[],[f6738,f5270])).

fof(f5270,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3701])).

fof(f3701,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3700])).

fof(f3700,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3540])).

fof(f3540,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f6738,plain,
    ( v1_tex_2(k1_tex_2(sK147,sK148),sK147)
    | ~ spl323_1 ),
    inference(avatar_component_clause,[],[f6732])).

fof(f7248,plain,
    ( ~ spl323_93
    | spl323_2
    | ~ spl323_33 ),
    inference(avatar_split_clause,[],[f7246,f6878,f6735,f7243])).

fof(f7243,plain,
    ( spl323_93
  <=> v1_subset_1(k2_tarski(sK148,sK148),u1_struct_0(sK147)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_93])])).

fof(f6735,plain,
    ( spl323_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_2])])).

fof(f6878,plain,
    ( spl323_33
  <=> k6_domain_1(u1_struct_0(sK147),sK148) = k2_tarski(sK148,sK148) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_33])])).

fof(f7246,plain,
    ( ~ v1_subset_1(k2_tarski(sK148,sK148),u1_struct_0(sK147))
    | spl323_2
    | ~ spl323_33 ),
    inference(forward_demodulation,[],[f6736,f6879])).

fof(f6879,plain,
    ( k6_domain_1(u1_struct_0(sK147),sK148) = k2_tarski(sK148,sK148)
    | ~ spl323_33 ),
    inference(avatar_component_clause,[],[f6878])).

fof(f6736,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
    | spl323_2 ),
    inference(avatar_component_clause,[],[f6735])).

fof(f7245,plain,
    ( spl323_5
    | spl323_34
    | ~ spl323_11
    | spl323_93
    | ~ spl323_3
    | ~ spl323_33 ),
    inference(avatar_split_clause,[],[f7241,f6878,f6742,f7243,f6779,f6886,f6750])).

fof(f6779,plain,
    ( spl323_11
  <=> l1_struct_0(sK147) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_11])])).

fof(f6742,plain,
    ( spl323_3
  <=> m1_subset_1(sK148,u1_struct_0(sK147)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_3])])).

fof(f7241,plain,
    ( v1_subset_1(k2_tarski(sK148,sK148),u1_struct_0(sK147))
    | ~ l1_struct_0(sK147)
    | v7_struct_0(sK147)
    | v2_struct_0(sK147)
    | ~ spl323_3
    | ~ spl323_33 ),
    inference(forward_demodulation,[],[f6782,f6879])).

fof(f6782,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
    | ~ l1_struct_0(sK147)
    | v7_struct_0(sK147)
    | v2_struct_0(sK147)
    | ~ spl323_3 ),
    inference(resolution,[],[f6743,f5222])).

fof(f5222,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3659])).

fof(f3659,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3658])).

fof(f3658,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3624])).

fof(f3624,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

fof(f6743,plain,
    ( m1_subset_1(sK148,u1_struct_0(sK147))
    | ~ spl323_3 ),
    inference(avatar_component_clause,[],[f6742])).

fof(f7227,plain,
    ( ~ spl323_18
    | ~ spl323_36 ),
    inference(avatar_split_clause,[],[f7222,f6892,f6821])).

fof(f6821,plain,
    ( spl323_18
  <=> sP11(sK148,sK147) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_18])])).

fof(f7222,plain,
    ( ~ sP11(sK148,sK147)
    | ~ spl323_36 ),
    inference(resolution,[],[f6893,f5290])).

fof(f5290,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X1,X0))
      | ~ sP11(X0,X1) ) ),
    inference(cnf_transformation,[],[f4558])).

fof(f4558,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X1,X0))
        & v7_struct_0(k1_tex_2(X1,X0))
        & ~ v2_struct_0(k1_tex_2(X1,X0)) )
      | ~ sP11(X0,X1) ) ),
    inference(rectify,[],[f4557])).

fof(f4557,plain,(
    ! [X1,X0] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP11(X1,X0) ) ),
    inference(nnf_transformation,[],[f4302])).

fof(f4302,plain,(
    ! [X1,X0] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP11(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

fof(f6893,plain,
    ( v2_struct_0(k1_tex_2(sK147,sK148))
    | ~ spl323_36 ),
    inference(avatar_component_clause,[],[f6892])).

fof(f7005,plain,
    ( spl323_5
    | ~ spl323_11
    | ~ spl323_30 ),
    inference(avatar_split_clause,[],[f7001,f6865,f6779,f6750])).

fof(f6865,plain,
    ( spl323_30
  <=> v1_xboole_0(u1_struct_0(sK147)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_30])])).

fof(f7001,plain,
    ( ~ l1_struct_0(sK147)
    | v2_struct_0(sK147)
    | ~ spl323_30 ),
    inference(resolution,[],[f6866,f5361])).

fof(f5361,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3763])).

fof(f3763,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3762])).

fof(f3762,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f6866,plain,
    ( v1_xboole_0(u1_struct_0(sK147))
    | ~ spl323_30 ),
    inference(avatar_component_clause,[],[f6865])).

fof(f6994,plain,
    ( spl323_37
    | ~ spl323_18 ),
    inference(avatar_split_clause,[],[f6992,f6821,f6895])).

fof(f6895,plain,
    ( spl323_37
  <=> v7_struct_0(k1_tex_2(sK147,sK148)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_37])])).

fof(f6992,plain,
    ( v7_struct_0(k1_tex_2(sK147,sK148))
    | ~ spl323_18 ),
    inference(resolution,[],[f6822,f5291])).

fof(f5291,plain,(
    ! [X0,X1] :
      ( ~ sP11(X0,X1)
      | v7_struct_0(k1_tex_2(X1,X0)) ) ),
    inference(cnf_transformation,[],[f4558])).

fof(f6822,plain,
    ( sP11(sK148,sK147)
    | ~ spl323_18 ),
    inference(avatar_component_clause,[],[f6821])).

fof(f6987,plain,
    ( spl323_35
    | ~ spl323_17 ),
    inference(avatar_split_clause,[],[f6971,f6817,f6889])).

fof(f6817,plain,
    ( spl323_17
  <=> sP10(sK147,sK148) ),
    introduced(avatar_definition,[new_symbols(naming,[spl323_17])])).

fof(f6971,plain,
    ( m1_pre_topc(k1_tex_2(sK147,sK148),sK147)
    | ~ spl323_17 ),
    inference(resolution,[],[f6818,f5288])).

fof(f5288,plain,(
    ! [X0,X1] :
      ( ~ sP10(X0,X1)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f4556])).

fof(f4556,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP10(X0,X1) ) ),
    inference(nnf_transformation,[],[f4300])).

fof(f4300,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP10(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f6818,plain,
    ( sP10(sK147,sK148)
    | ~ spl323_17 ),
    inference(avatar_component_clause,[],[f6817])).

fof(f6911,plain,
    ( spl323_5
    | ~ spl323_11
    | ~ spl323_3
    | ~ spl323_34
    | ~ spl323_2 ),
    inference(avatar_split_clause,[],[f6906,f6735,f6886,f6742,f6779,f6750])).

fof(f6906,plain,
    ( ~ v7_struct_0(sK147)
    | ~ m1_subset_1(sK148,u1_struct_0(sK147))
    | ~ l1_struct_0(sK147)
    | v2_struct_0(sK147)
    | ~ spl323_2 ),
    inference(resolution,[],[f6739,f5202])).

fof(f5202,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3647])).

fof(f3647,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3646])).

fof(f3646,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3623])).

fof(f3623,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f6739,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
    | ~ spl323_2 ),
    inference(avatar_component_clause,[],[f6735])).

fof(f6909,plain,
    ( ~ spl323_4
    | spl323_11 ),
    inference(avatar_split_clause,[],[f6908,f6779,f6746])).

fof(f6908,plain,
    ( ~ l1_pre_topc(sK147)
    | spl323_11 ),
    inference(resolution,[],[f6780,f5362])).

fof(f5362,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3764])).

fof(f3764,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f6780,plain,
    ( ~ l1_struct_0(sK147)
    | spl323_11 ),
    inference(avatar_component_clause,[],[f6779])).

fof(f6898,plain,
    ( spl323_5
    | spl323_34
    | ~ spl323_4
    | ~ spl323_35
    | spl323_36
    | ~ spl323_37
    | spl323_1 ),
    inference(avatar_split_clause,[],[f6882,f6732,f6895,f6892,f6889,f6746,f6886,f6750])).

fof(f6882,plain,
    ( ~ v7_struct_0(k1_tex_2(sK147,sK148))
    | v2_struct_0(k1_tex_2(sK147,sK148))
    | ~ m1_pre_topc(k1_tex_2(sK147,sK148),sK147)
    | ~ l1_pre_topc(sK147)
    | v7_struct_0(sK147)
    | v2_struct_0(sK147)
    | spl323_1 ),
    inference(resolution,[],[f6733,f5272])).

fof(f5272,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3703])).

fof(f3703,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | v1_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3702])).

fof(f3702,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | v1_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3545])).

fof(f3545,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc13_tex_2)).

fof(f6733,plain,
    ( ~ v1_tex_2(k1_tex_2(sK147,sK148),sK147)
    | spl323_1 ),
    inference(avatar_component_clause,[],[f6732])).

fof(f6880,plain,
    ( spl323_30
    | spl323_33
    | ~ spl323_3 ),
    inference(avatar_split_clause,[],[f6797,f6742,f6878,f6865])).

fof(f6797,plain,
    ( k6_domain_1(u1_struct_0(sK147),sK148) = k2_tarski(sK148,sK148)
    | v1_xboole_0(u1_struct_0(sK147))
    | ~ spl323_3 ),
    inference(resolution,[],[f6743,f6453])).

fof(f6453,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f5250,f6370])).

fof(f6370,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f5250,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3688])).

fof(f3688,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3687])).

fof(f3687,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1935])).

fof(f1935,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f6823,plain,
    ( spl323_5
    | ~ spl323_4
    | spl323_18
    | ~ spl323_3 ),
    inference(avatar_split_clause,[],[f6786,f6742,f6821,f6746,f6750])).

fof(f6786,plain,
    ( sP11(sK148,sK147)
    | ~ l1_pre_topc(sK147)
    | v2_struct_0(sK147)
    | ~ spl323_3 ),
    inference(resolution,[],[f6743,f5293])).

fof(f5293,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP11(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4303])).

fof(f4303,plain,(
    ! [X0,X1] :
      ( sP11(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f3717,f4302])).

fof(f3717,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3716])).

fof(f3716,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3579])).

fof(f3579,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f6819,plain,
    ( spl323_5
    | ~ spl323_4
    | spl323_17
    | ~ spl323_3 ),
    inference(avatar_split_clause,[],[f6785,f6742,f6817,f6746,f6750])).

fof(f6785,plain,
    ( sP10(sK147,sK148)
    | ~ l1_pre_topc(sK147)
    | v2_struct_0(sK147)
    | ~ spl323_3 ),
    inference(resolution,[],[f6743,f5289])).

fof(f5289,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP10(X0,X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4301])).

fof(f4301,plain,(
    ! [X0,X1] :
      ( sP10(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f3715,f4300])).

fof(f3715,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3714])).

fof(f3714,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3577])).

fof(f3577,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f6752,plain,(
    ~ spl323_5 ),
    inference(avatar_split_clause,[],[f5189,f6750])).

fof(f5189,plain,(
    ~ v2_struct_0(sK147) ),
    inference(cnf_transformation,[],[f4520])).

fof(f4520,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
      | ~ v1_tex_2(k1_tex_2(sK147,sK148),sK147) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
      | v1_tex_2(k1_tex_2(sK147,sK148),sK147) )
    & m1_subset_1(sK148,u1_struct_0(sK147))
    & l1_pre_topc(sK147)
    & ~ v2_struct_0(sK147) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK147,sK148])],[f4517,f4519,f4518])).

fof(f4518,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK147),X1),u1_struct_0(sK147))
            | ~ v1_tex_2(k1_tex_2(sK147,X1),sK147) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK147),X1),u1_struct_0(sK147))
            | v1_tex_2(k1_tex_2(sK147,X1),sK147) )
          & m1_subset_1(X1,u1_struct_0(sK147)) )
      & l1_pre_topc(sK147)
      & ~ v2_struct_0(sK147) ) ),
    introduced(choice_axiom,[])).

fof(f4519,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK147),X1),u1_struct_0(sK147))
          | ~ v1_tex_2(k1_tex_2(sK147,X1),sK147) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK147),X1),u1_struct_0(sK147))
          | v1_tex_2(k1_tex_2(sK147,X1),sK147) )
        & m1_subset_1(X1,u1_struct_0(sK147)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
        | ~ v1_tex_2(k1_tex_2(sK147,sK148),sK147) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
        | v1_tex_2(k1_tex_2(sK147,sK148),sK147) )
      & m1_subset_1(sK148,u1_struct_0(sK147)) ) ),
    introduced(choice_axiom,[])).

fof(f4517,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4516])).

fof(f4516,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3640])).

fof(f3640,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3639])).

fof(f3639,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3618])).

fof(f3618,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3617])).

fof(f3617,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f6748,plain,(
    spl323_4 ),
    inference(avatar_split_clause,[],[f5190,f6746])).

fof(f5190,plain,(
    l1_pre_topc(sK147) ),
    inference(cnf_transformation,[],[f4520])).

fof(f6744,plain,(
    spl323_3 ),
    inference(avatar_split_clause,[],[f5191,f6742])).

fof(f5191,plain,(
    m1_subset_1(sK148,u1_struct_0(sK147)) ),
    inference(cnf_transformation,[],[f4520])).

fof(f6740,plain,
    ( spl323_1
    | spl323_2 ),
    inference(avatar_split_clause,[],[f5192,f6735,f6732])).

fof(f5192,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
    | v1_tex_2(k1_tex_2(sK147,sK148),sK147) ),
    inference(cnf_transformation,[],[f4520])).

fof(f6737,plain,
    ( ~ spl323_1
    | ~ spl323_2 ),
    inference(avatar_split_clause,[],[f5193,f6735,f6732])).

fof(f5193,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK147),sK148),u1_struct_0(sK147))
    | ~ v1_tex_2(k1_tex_2(sK147,sK148),sK147) ),
    inference(cnf_transformation,[],[f4520])).
%------------------------------------------------------------------------------
