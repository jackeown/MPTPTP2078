%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1271+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:36 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 249 expanded)
%              Number of leaves         :   27 ( 121 expanded)
%              Depth                    :    7
%              Number of atoms          :  369 ( 985 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f885,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f78,f83,f90,f95,f102,f126,f138,f143,f171,f188,f476,f824])).

% (1084)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
fof(f824,plain,
    ( ~ spl3_54
    | spl3_1
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f704,f123,f75,f50,f469])).

fof(f469,plain,
    ( spl3_54
  <=> v2_tops_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f50,plain,
    ( spl3_1
  <=> v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f75,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f123,plain,
    ( spl3_14
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f704,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f77,f52,f125,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(f125,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f52,plain,
    ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f77,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f476,plain,
    ( spl3_54
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f475,f185,f140,f135,f99,f92,f87,f80,f75,f469])).

fof(f80,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f87,plain,
    ( spl3_8
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f92,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f99,plain,
    ( spl3_10
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f135,plain,
    ( spl3_16
  <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f140,plain,
    ( spl3_17
  <=> v2_tops_1(k2_pre_topc(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f185,plain,
    ( spl3_22
  <=> k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f475,plain,
    ( v2_tops_1(k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f324,f187])).

fof(f187,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f185])).

fof(f324,plain,
    ( v2_tops_1(k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)),sK0)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f82,f77,f101,f137,f89,f142,f94,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_tops_1(X2,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v2_tops_1(X2,X0)
              | ~ v2_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v2_tops_1(X2,X0)
              | ~ v2_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (1078)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (1079)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (1072)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (1080)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (1081)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (1085)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v2_tops_1(X2,X0)
                  & v2_tops_1(X1,X0) )
               => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tops_1)).

% (1076)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f94,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f142,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f89,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f137,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f101,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f82,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f188,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f183,f167,f80,f75,f70,f65,f185])).

fof(f65,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f167,plain,
    ( spl3_20
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f183,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f175,f169])).

fof(f169,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f167])).

fof(f175,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f82,f77,f67,f72,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f171,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f159,f70,f65,f167])).

fof(f159,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f72,f67,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f143,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f132,f75,f65,f55,f140])).

fof(f55,plain,
    ( spl3_2
  <=> v3_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f132,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f77,f57,f67,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,
    ( v3_tops_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f138,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f133,f75,f70,f60,f135])).

fof(f60,plain,
    ( spl3_3
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f133,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f77,f62,f72,f44])).

fof(f62,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f126,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f109,f70,f65,f123])).

fof(f109,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f72,f67,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f97,f80,f75,f70,f99])).

fof(f97,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f82,f77,f72,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f95,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f84,f75,f65,f92])).

fof(f84,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f77,f67,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f90,plain,
    ( spl3_8
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f85,f75,f70,f87])).

fof(f85,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f77,f72,f47])).

fof(f83,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_tops_1(sK2,sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_tops_1(X2,X0)
                & v3_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_tops_1(X2,sK0)
              & v3_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_tops_1(X2,sK0)
            & v3_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_tops_1(X2,sK0)
          & v3_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_tops_1(X2,sK0)
        & v3_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_tops_1(sK2,sK0)
      & v3_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_tops_1(X2,X0)
              & v3_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_tops_1(X2,X0)
              & v3_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_tops_1(X2,X0)
                    & v3_tops_1(X1,X0) )
                 => v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_tops_1(X2,X0)
                  & v3_tops_1(X1,X0) )
               => v3_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_tops_1)).

fof(f78,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f75])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f60])).

fof(f37,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f55])).

fof(f38,plain,(
    v3_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f39,f50])).

fof(f39,plain,(
    ~ v3_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f31])).

%------------------------------------------------------------------------------
