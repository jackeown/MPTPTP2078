%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1302+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 221 expanded)
%              Number of leaves         :   19 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  332 ( 712 expanded)
%              Number of equality atoms :   10 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f93,f183,f276,f307,f311,f315,f324,f335,f365,f394])).

% (8047)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f394,plain,
    ( ~ spl6_26
    | spl6_27
    | spl6_35 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl6_26
    | spl6_27
    | spl6_35 ),
    inference(subsumption_resolution,[],[f392,f334])).

fof(f334,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl6_27
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f392,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_26
    | spl6_35 ),
    inference(subsumption_resolution,[],[f390,f364])).

fof(f364,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl6_35
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f390,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_26 ),
    inference(resolution,[],[f323,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f323,plain,
    ( sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl6_26
  <=> sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f365,plain,
    ( ~ spl6_35
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_23
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f331,f313,f305,f65,f61,f53,f363])).

fof(f53,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f61,plain,
    ( spl6_3
  <=> v1_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f65,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f305,plain,
    ( spl6_23
  <=> v3_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f313,plain,
    ( spl6_25
  <=> m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f331,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_23
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f326,f306])).

fof(f306,plain,
    ( ~ v3_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f305])).

fof(f326,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | v3_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(resolution,[],[f314,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v3_pre_topc(X0,sK0) )
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f79,f62])).

fof(f62,plain,
    ( v1_tops_2(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK2,sK0) )
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f72,f54])).

fof(f54,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK2,sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f66,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f314,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f313])).

fof(f335,plain,
    ( ~ spl6_27
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_23
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f330,f313,f305,f69,f57,f53,f333])).

fof(f57,plain,
    ( spl6_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f69,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f330,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_23
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f325,f306])).

fof(f325,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | v3_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_25 ),
    inference(resolution,[],[f314,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f88,f58])).

fof(f58,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK1,sK0) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f81,f54])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK1,sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f34])).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f324,plain,
    ( spl6_26
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f316,f309,f322])).

fof(f309,plain,
    ( spl6_24
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f316,plain,
    ( sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl6_24 ),
    inference(resolution,[],[f310,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f310,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f309])).

fof(f315,plain,
    ( spl6_25
    | ~ spl6_1
    | spl6_6
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f299,f274,f181,f91,f53,f313])).

fof(f91,plain,
    ( spl6_6
  <=> v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f181,plain,
    ( spl6_16
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f274,plain,
    ( spl6_20
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f299,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | spl6_6
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f230,f296])).

fof(f296,plain,
    ( ~ v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | spl6_6
    | ~ spl6_20 ),
    inference(superposition,[],[f92,f275])).

fof(f275,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f274])).

fof(f92,plain,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f230,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f223,f54])).

fof(f223,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f182,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f182,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f311,plain,
    ( spl6_24
    | ~ spl6_1
    | spl6_6
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f298,f274,f181,f91,f53,f309])).

fof(f298,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl6_1
    | spl6_6
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f231,f296])).

fof(f231,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f224,f54])).

fof(f224,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f182,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f307,plain,
    ( ~ spl6_23
    | ~ spl6_1
    | spl6_6
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f297,f274,f181,f91,f53,f305])).

fof(f297,plain,
    ( ~ v3_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | spl6_6
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f232,f296])).

fof(f232,plain,
    ( ~ v3_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f225,f54])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f182,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f276,plain,
    ( spl6_20
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f127,f69,f65,f274])).

fof(f127,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f86,f66])).

fof(f86,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2) = k2_xboole_0(sK1,X2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f183,plain,
    ( spl6_16
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f164,f69,f65,f181])).

fof(f164,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f162,f127])).

fof(f162,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f85,f66])).

fof(f85,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f93,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f29,f91])).

fof(f29,plain,(
    ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
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
               => ( ( v1_tops_2(X2,X0)
                    & v1_tops_2(X1,X0) )
                 => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & v1_tops_2(X1,X0) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tops_2)).

fof(f71,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
