%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1130+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:19 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  233 ( 567 expanded)
%              Number of leaves         :   45 ( 222 expanded)
%              Depth                    :   11
%              Number of atoms          :  718 (2112 expanded)
%              Number of equality atoms :   39 ( 174 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f575,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f74,f77,f94,f98,f115,f128,f136,f176,f180,f192,f210,f215,f231,f251,f257,f262,f279,f289,f296,f316,f318,f334,f388,f403,f408,f424,f429,f430,f455,f457,f529,f530,f533,f534,f544,f568,f574])).

fof(f574,plain,
    ( ~ spl2_2
    | spl2_4
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl2_2
    | spl2_4
    | ~ spl2_14 ),
    inference(resolution,[],[f572,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f572,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_4
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f72,f197])).

fof(f197,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_14 ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f72,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f568,plain,
    ( ~ spl2_6
    | ~ spl2_14
    | spl2_46 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_14
    | spl2_46 ),
    inference(resolution,[],[f542,f199])).

fof(f199,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f93,f197])).

fof(f93,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_6
  <=> v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f542,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_46 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl2_46
  <=> v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f544,plain,
    ( ~ spl2_2
    | ~ spl2_46
    | spl2_3
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f431,f174,f87,f66,f540,f62])).

fof(f66,plain,
    ( spl2_3
  <=> v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f87,plain,
    ( spl2_5
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f431,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(resolution,[],[f68,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f200,f197])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f101,f197])).

fof(f101,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f88,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

% (19652)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f88,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f68,plain,
    ( ~ v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f534,plain,
    ( ~ spl2_7
    | ~ spl2_38
    | spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f449,f174,f91,f410,f108])).

fof(f108,plain,
    ( spl2_7
  <=> l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f410,plain,
    ( spl2_38
  <=> v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f449,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_6
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f436,f197])).

fof(f436,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f426,f42])).

fof(f42,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f426,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_6
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f92,f197])).

fof(f92,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f533,plain,
    ( ~ spl2_20
    | spl2_38
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f531,f405,f410,f233])).

fof(f233,plain,
    ( spl2_20
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f405,plain,
    ( spl2_37
  <=> v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f531,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl2_37 ),
    inference(superposition,[],[f406,f42])).

fof(f406,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f405])).

fof(f530,plain,
    ( ~ spl2_22
    | ~ spl2_35
    | spl2_37 ),
    inference(avatar_split_clause,[],[f526,f405,f395,f242])).

fof(f242,plain,
    ( spl2_22
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f395,plain,
    ( spl2_35
  <=> v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f526,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_37 ),
    inference(superposition,[],[f407,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f407,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_37 ),
    inference(avatar_component_clause,[],[f405])).

fof(f529,plain,
    ( ~ spl2_5
    | ~ spl2_19
    | ~ spl2_18
    | ~ spl2_14
    | ~ spl2_15
    | spl2_37 ),
    inference(avatar_split_clause,[],[f528,f405,f178,f174,f224,f228,f87])).

fof(f228,plain,
    ( spl2_19
  <=> r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f224,plain,
    ( spl2_18
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f178,plain,
    ( spl2_15
  <=> ! [X5,X4] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X4,X5)
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f528,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_14
    | ~ spl2_15
    | spl2_37 ),
    inference(forward_demodulation,[],[f527,f197])).

fof(f527,plain,
    ( ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_15
    | spl2_37 ),
    inference(forward_demodulation,[],[f524,f371])).

fof(f371,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_15 ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X4,X5)
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X5 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f178])).

fof(f524,plain,
    ( ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_37 ),
    inference(resolution,[],[f407,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f457,plain,
    ( ~ spl2_5
    | ~ spl2_25
    | ~ spl2_24
    | ~ spl2_14
    | ~ spl2_15
    | spl2_35 ),
    inference(avatar_split_clause,[],[f456,f395,f178,f174,f267,f271,f87])).

fof(f271,plain,
    ( spl2_25
  <=> r2_hidden(k4_xboole_0(k2_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f267,plain,
    ( spl2_24
  <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f456,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k4_xboole_0(k2_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_14
    | ~ spl2_15
    | spl2_35 ),
    inference(forward_demodulation,[],[f416,f197])).

fof(f416,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_15
    | spl2_35 ),
    inference(forward_demodulation,[],[f414,f371])).

% (19634)Refutation not found, incomplete strategy% (19634)------------------------------
% (19634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19634)Termination reason: Refutation not found, incomplete strategy

% (19634)Memory used [KB]: 10746
% (19634)Time elapsed: 0.136 s
% (19634)------------------------------
% (19634)------------------------------
% (19649)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (19642)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (19647)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (19644)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (19644)Refutation not found, incomplete strategy% (19644)------------------------------
% (19644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19644)Termination reason: Refutation not found, incomplete strategy

% (19644)Memory used [KB]: 1663
% (19644)Time elapsed: 0.159 s
% (19644)------------------------------
% (19644)------------------------------
fof(f414,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_struct_0(sK0),sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_35 ),
    inference(resolution,[],[f397,f48])).

fof(f397,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_35 ),
    inference(avatar_component_clause,[],[f395])).

fof(f455,plain,
    ( ~ spl2_17
    | ~ spl2_24
    | ~ spl2_23
    | spl2_25 ),
    inference(avatar_split_clause,[],[f297,f271,f246,f267,f220])).

fof(f220,plain,
    ( spl2_17
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f246,plain,
    ( spl2_23
  <=> v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f297,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_25 ),
    inference(resolution,[],[f273,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f273,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f271])).

fof(f430,plain,
    ( ~ spl2_17
    | ~ spl2_18
    | ~ spl2_16
    | spl2_19 ),
    inference(avatar_split_clause,[],[f320,f228,f212,f224,f220])).

fof(f212,plain,
    ( spl2_16
  <=> v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f320,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_19 ),
    inference(resolution,[],[f230,f47])).

fof(f230,plain,
    ( ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f228])).

fof(f429,plain,
    ( ~ spl2_17
    | ~ spl2_2
    | spl2_16
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f428,f58,f212,f62,f220])).

fof(f58,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f428,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f424,plain,
    ( spl2_36
    | ~ spl2_29
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f423,f174,f112,f293,f400])).

fof(f400,plain,
    ( spl2_36
  <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f293,plain,
    ( spl2_29
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f112,plain,
    ( spl2_8
  <=> v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f423,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f422,f197])).

fof(f422,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f144,f197])).

fof(f144,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_8 ),
    inference(superposition,[],[f114,f56])).

fof(f114,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f408,plain,
    ( ~ spl2_18
    | ~ spl2_37
    | spl2_19
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f392,f386,f228,f405,f224])).

fof(f386,plain,
    ( spl2_34
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f392,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_19
    | ~ spl2_34 ),
    inference(resolution,[],[f387,f230])).

fof(f387,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f386])).

fof(f403,plain,
    ( ~ spl2_27
    | ~ spl2_36
    | spl2_28
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f391,f386,f286,f400,f282])).

fof(f282,plain,
    ( spl2_27
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f286,plain,
    ( spl2_28
  <=> r2_hidden(k4_xboole_0(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f391,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_28
    | ~ spl2_34 ),
    inference(resolution,[],[f387,f288])).

fof(f288,plain,
    ( ~ r2_hidden(k4_xboole_0(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | spl2_28 ),
    inference(avatar_component_clause,[],[f286])).

fof(f388,plain,
    ( ~ spl2_5
    | spl2_34
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f384,f178,f174,f386,f87])).

fof(f384,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f382,f197])).

fof(f382,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_15 ),
    inference(superposition,[],[f47,f371])).

fof(f334,plain,
    ( spl2_18
    | ~ spl2_22 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | spl2_18
    | ~ spl2_22 ),
    inference(resolution,[],[f328,f243])).

fof(f243,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f242])).

fof(f328,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_18 ),
    inference(resolution,[],[f226,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f226,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f318,plain,
    ( ~ spl2_20
    | spl2_27
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f317,f267,f282,f233])).

fof(f317,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl2_24 ),
    inference(superposition,[],[f268,f42])).

fof(f268,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f267])).

fof(f316,plain,
    ( ~ spl2_22
    | spl2_24 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl2_22
    | spl2_24 ),
    inference(resolution,[],[f311,f243])).

fof(f311,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_24 ),
    inference(resolution,[],[f269,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f55,f56])).

fof(f269,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f267])).

fof(f296,plain,
    ( ~ spl2_7
    | spl2_29
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f291,f174,f117,f293,f108])).

fof(f117,plain,
    ( spl2_9
  <=> m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f291,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f290,f197])).

fof(f290,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(superposition,[],[f202,f42])).

fof(f202,plain,
    ( m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f118,f197])).

fof(f118,plain,
    ( m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f289,plain,
    ( ~ spl2_17
    | ~ spl2_27
    | ~ spl2_28
    | spl2_26 ),
    inference(avatar_split_clause,[],[f280,f276,f286,f282,f220])).

fof(f276,plain,
    ( spl2_26
  <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f280,plain,
    ( ~ r2_hidden(k4_xboole_0(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_26 ),
    inference(resolution,[],[f278,f48])).

fof(f278,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | spl2_26 ),
    inference(avatar_component_clause,[],[f276])).

fof(f279,plain,
    ( ~ spl2_20
    | ~ spl2_26
    | spl2_23 ),
    inference(avatar_split_clause,[],[f265,f246,f276,f233])).

fof(f265,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_struct_0(sK0)
    | spl2_23 ),
    inference(superposition,[],[f248,f42])).

fof(f248,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | spl2_23 ),
    inference(avatar_component_clause,[],[f246])).

fof(f262,plain,
    ( ~ spl2_20
    | spl2_22 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl2_20
    | spl2_22 ),
    inference(resolution,[],[f258,f234])).

fof(f234,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f233])).

fof(f258,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_22 ),
    inference(resolution,[],[f244,f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f244,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f242])).

fof(f257,plain,(
    spl2_20 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl2_20 ),
    inference(resolution,[],[f252,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v4_pre_topc(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v4_pre_topc(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v4_pre_topc(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v4_pre_topc(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v4_pre_topc(X1,sK0) ) ) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v4_pre_topc(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v4_pre_topc(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          & v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v4_pre_topc(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f252,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_20 ),
    inference(resolution,[],[f235,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f235,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f233])).

fof(f251,plain,(
    spl2_17 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl2_17 ),
    inference(resolution,[],[f222,f36])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_17 ),
    inference(avatar_component_clause,[],[f220])).

fof(f231,plain,
    ( ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | spl2_16 ),
    inference(avatar_split_clause,[],[f216,f212,f228,f224,f220])).

fof(f216,plain,
    ( ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_16 ),
    inference(resolution,[],[f214,f48])).

fof(f214,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | spl2_16 ),
    inference(avatar_component_clause,[],[f212])).

fof(f215,plain,
    ( ~ spl2_16
    | ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f102,f58,f62,f212])).

fof(f102,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | spl2_1 ),
    inference(resolution,[],[f99,f60])).

fof(f60,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f99,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f50,f36])).

fof(f210,plain,
    ( spl2_2
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl2_2
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(resolution,[],[f198,f64])).

fof(f64,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f198,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f71,f197])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f192,plain,
    ( ~ spl2_5
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl2_5
    | spl2_12 ),
    inference(resolution,[],[f186,f88])).

fof(f186,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_12 ),
    inference(resolution,[],[f167,f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f167,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl2_12
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f180,plain,
    ( ~ spl2_12
    | spl2_15 ),
    inference(avatar_split_clause,[],[f160,f178,f165])).

fof(f160,plain,(
    ! [X4,X5] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X4,X5)
      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X5
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ) ),
    inference(superposition,[],[f54,f152])).

fof(f152,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f147,f36])).

fof(f147,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(resolution,[],[f133,f45])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(g1_pre_topc(X0,X1))
      | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f176,plain,
    ( ~ spl2_12
    | spl2_14 ),
    inference(avatar_split_clause,[],[f158,f174,f165])).

fof(f158,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ) ),
    inference(superposition,[],[f53,f152])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f136,plain,
    ( ~ spl2_7
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl2_7
    | spl2_9 ),
    inference(resolution,[],[f129,f109])).

fof(f109,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f129,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_9 ),
    inference(resolution,[],[f119,f43])).

fof(f119,plain,
    ( ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f128,plain,
    ( ~ spl2_5
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl2_5
    | spl2_7 ),
    inference(resolution,[],[f125,f88])).

fof(f125,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_7 ),
    inference(resolution,[],[f110,f44])).

fof(f110,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f115,plain,
    ( ~ spl2_7
    | spl2_8
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f105,f91,f112,f108])).

fof(f105,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6 ),
    inference(superposition,[],[f93,f42])).

fof(f98,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f96,f36])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(resolution,[],[f95,f45])).

fof(f95,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_5 ),
    inference(resolution,[],[f89,f52])).

fof(f89,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f94,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f85,f66,f91,f70,f87])).

fof(f85,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f49,f67])).

fof(f67,plain,
    ( v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f77,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f37,f66,f58])).

fof(f37,plain,
    ( v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,
    ( spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f40,f70,f62])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f41,f70,f66,f62,f58])).

fof(f41,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v4_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
