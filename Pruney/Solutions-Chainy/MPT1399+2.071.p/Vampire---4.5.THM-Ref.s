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
% DateTime   : Thu Dec  3 13:15:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 221 expanded)
%              Number of leaves         :   35 (  93 expanded)
%              Depth                    :    8
%              Number of atoms          :  425 ( 817 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f66,f74,f98,f102,f106,f110,f119,f133,f138,f143,f155,f159,f163,f170,f180,f199,f203,f219,f230,f240,f250,f255,f266])).

fof(f266,plain,
    ( ~ spl3_37
    | ~ spl3_36
    | ~ spl3_12
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f261,f248,f201,f197,f168,f100,f222,f232])).

fof(f232,plain,
    ( spl3_37
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f222,plain,
    ( spl3_36
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f100,plain,
    ( spl3_12
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f168,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f197,plain,
    ( spl3_30
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f201,plain,
    ( spl3_31
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f248,plain,
    ( spl3_39
  <=> ! [X0] :
        ( r2_hidden(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f261,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl3_12
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f243,f257])).

fof(f257,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl3_30
    | ~ spl3_39 ),
    inference(resolution,[],[f249,f198])).

% (10834)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f198,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f197])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r2_hidden(X0,k2_struct_0(sK0)) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f248])).

fof(f243,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl3_12
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f242,f202])).

fof(f202,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f201])).

fof(f242,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_12
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f241,f202])).

fof(f241,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_12
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f172,f202])).

fof(f172,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(resolution,[],[f169,f101])).

fof(f101,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f168])).

fof(f255,plain,
    ( ~ spl3_3
    | ~ spl3_11
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f254])).

% (10841)Refutation not found, incomplete strategy% (10841)------------------------------
% (10841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10841)Termination reason: Refutation not found, incomplete strategy

% (10841)Memory used [KB]: 1663
% (10841)Time elapsed: 0.047 s
% (10841)------------------------------
% (10841)------------------------------
fof(f254,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_11
    | spl3_38 ),
    inference(subsumption_resolution,[],[f252,f65])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f252,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_11
    | spl3_38 ),
    inference(resolution,[],[f246,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f246,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_38 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl3_38
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f250,plain,
    ( ~ spl3_38
    | spl3_39
    | spl3_1
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f220,f217,f56,f248,f245])).

fof(f56,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f217,plain,
    ( spl3_35
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(X1))
        | r2_hidden(X0,k2_struct_0(X1))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f220,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_35 ),
    inference(resolution,[],[f218,f57])).

fof(f57,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X1)
        | r2_hidden(X0,k2_struct_0(X1))
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(X0,k2_struct_0(X1)) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f217])).

fof(f240,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_25
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_25
    | spl3_37 ),
    inference(subsumption_resolution,[],[f238,f61])).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f238,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_25
    | spl3_37 ),
    inference(subsumption_resolution,[],[f236,f65])).

fof(f236,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_25
    | spl3_37 ),
    inference(resolution,[],[f233,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_25
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f233,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_37 ),
    inference(avatar_component_clause,[],[f232])).

fof(f230,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24
    | spl3_36 ),
    inference(subsumption_resolution,[],[f228,f61])).

fof(f228,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_24
    | spl3_36 ),
    inference(subsumption_resolution,[],[f226,f65])).

% (10831)Refutation not found, incomplete strategy% (10831)------------------------------
% (10831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10831)Termination reason: Refutation not found, incomplete strategy

% (10831)Memory used [KB]: 10618
% (10831)Time elapsed: 0.085 s
% (10831)------------------------------
% (10831)------------------------------
fof(f226,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_24
    | spl3_36 ),
    inference(resolution,[],[f223,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( v4_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_24
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f223,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f222])).

fof(f219,plain,
    ( spl3_35
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f171,f161,f141,f217])).

fof(f141,plain,
    ( spl3_21
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f161,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k2_struct_0(X1))
        | r2_hidden(X0,k2_struct_0(X1))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1) )
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(resolution,[],[f162,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f141])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f161])).

fof(f203,plain,
    ( spl3_31
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f183,f178,f64,f201])).

fof(f178,plain,
    ( spl3_29
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f183,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(resolution,[],[f179,f65])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f178])).

fof(f199,plain,
    ( spl3_30
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f184,f178,f72,f64,f197])).

fof(f72,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f184,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f73,f183])).

fof(f73,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

% (10840)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f180,plain,
    ( spl3_29
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f165,f136,f96,f178])).

fof(f136,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f165,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(resolution,[],[f137,f97])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f170,plain,
    ( spl3_27
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f139,f131,f117,f168])).

fof(f117,plain,
    ( spl3_16
  <=> ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ v4_pre_topc(X3,sK0)
        | ~ r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f131,plain,
    ( spl3_19
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(resolution,[],[f132,f118])).

fof(f118,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ v4_pre_topc(X3,sK0)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f117])).

fof(f132,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f163,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f43,f161])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f159,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f41,f157])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f155,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f40,f153])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f143,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f39,f141])).

fof(f39,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f138,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f37,f136])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f133,plain,
    ( spl3_19
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f129,f108,f104,f131])).

fof(f104,plain,
    ( spl3_13
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f108,plain,
    ( spl3_14
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f129,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(superposition,[],[f105,f109])).

fof(f109,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f105,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f119,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f50,f117])).

fof(f50,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f28,f30])).

fof(f30,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f28,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f110,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f47,f108])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f106,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f42,f104])).

fof(f42,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f102,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f54,f100])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f36,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f98,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f38,f96])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f74,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:17:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (10835)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (10836)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (10844)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (10838)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (10837)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (10849)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (10844)Refutation not found, incomplete strategy% (10844)------------------------------
% 0.21/0.49  % (10844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10830)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (10844)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10844)Memory used [KB]: 6140
% 0.21/0.49  % (10844)Time elapsed: 0.073 s
% 0.21/0.49  % (10844)------------------------------
% 0.21/0.49  % (10844)------------------------------
% 0.21/0.49  % (10831)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (10841)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (10837)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f58,f62,f66,f74,f98,f102,f106,f110,f119,f133,f138,f143,f155,f159,f163,f170,f180,f199,f203,f219,f230,f240,f250,f255,f266])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ~spl3_37 | ~spl3_36 | ~spl3_12 | ~spl3_27 | ~spl3_30 | ~spl3_31 | ~spl3_39),
% 0.21/0.49    inference(avatar_split_clause,[],[f261,f248,f201,f197,f168,f100,f222,f232])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    spl3_37 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl3_36 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl3_12 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl3_27 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl3_30 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl3_31 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    spl3_39 <=> ! [X0] : (r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl3_12 | ~spl3_27 | ~spl3_30 | ~spl3_31 | ~spl3_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f243,f257])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    r2_hidden(sK1,k2_struct_0(sK0)) | (~spl3_30 | ~spl3_39)),
% 0.21/0.49    inference(resolution,[],[f249,f198])).
% 0.21/0.49  % (10834)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,k2_struct_0(sK0))) ) | ~spl3_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f248])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl3_12 | ~spl3_27 | ~spl3_31)),
% 0.21/0.49    inference(forward_demodulation,[],[f242,f202])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f201])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | (~spl3_12 | ~spl3_27 | ~spl3_31)),
% 0.21/0.49    inference(forward_demodulation,[],[f241,f202])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | (~spl3_12 | ~spl3_27 | ~spl3_31)),
% 0.21/0.49    inference(forward_demodulation,[],[f172,f202])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | (~spl3_12 | ~spl3_27)),
% 0.21/0.49    inference(resolution,[],[f169,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0)) ) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f168])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ~spl3_3 | ~spl3_11 | spl3_38),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f254])).
% 0.21/0.49  % (10841)Refutation not found, incomplete strategy% (10841)------------------------------
% 0.21/0.49  % (10841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10841)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10841)Memory used [KB]: 1663
% 0.21/0.49  % (10841)Time elapsed: 0.047 s
% 0.21/0.49  % (10841)------------------------------
% 0.21/0.49  % (10841)------------------------------
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    $false | (~spl3_3 | ~spl3_11 | spl3_38)),
% 0.21/0.49    inference(subsumption_resolution,[],[f252,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_3 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | (~spl3_11 | spl3_38)),
% 0.21/0.49    inference(resolution,[],[f246,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_11 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | spl3_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f245])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    spl3_38 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ~spl3_38 | spl3_39 | spl3_1 | ~spl3_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f220,f217,f56,f248,f245])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl3_35 <=> ! [X1,X0] : (~m1_subset_1(X0,k2_struct_0(X1)) | r2_hidden(X0,k2_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,k2_struct_0(sK0)) | ~l1_struct_0(sK0) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | (spl3_1 | ~spl3_35)),
% 0.21/0.49    inference(resolution,[],[f218,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f56])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X1) | r2_hidden(X0,k2_struct_0(X1)) | ~l1_struct_0(X1) | ~m1_subset_1(X0,k2_struct_0(X1))) ) | ~spl3_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f217])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ~spl3_2 | ~spl3_3 | ~spl3_25 | spl3_37),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    $false | (~spl3_2 | ~spl3_3 | ~spl3_25 | spl3_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f238,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl3_2 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_25 | spl3_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f236,f65])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_25 | spl3_37)),
% 0.21/0.49    inference(resolution,[],[f233,f158])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl3_25 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl3_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f232])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ~spl3_2 | ~spl3_3 | ~spl3_24 | spl3_36),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    $false | (~spl3_2 | ~spl3_3 | ~spl3_24 | spl3_36)),
% 0.21/0.49    inference(subsumption_resolution,[],[f228,f61])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_24 | spl3_36)),
% 0.21/0.49    inference(subsumption_resolution,[],[f226,f65])).
% 0.21/0.49  % (10831)Refutation not found, incomplete strategy% (10831)------------------------------
% 0.21/0.49  % (10831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10831)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10831)Memory used [KB]: 10618
% 0.21/0.49  % (10831)Time elapsed: 0.085 s
% 0.21/0.49  % (10831)------------------------------
% 0.21/0.49  % (10831)------------------------------
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_24 | spl3_36)),
% 0.21/0.49    inference(resolution,[],[f223,f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl3_24 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl3_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f222])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl3_35 | ~spl3_21 | ~spl3_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f171,f161,f141,f217])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl3_21 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl3_26 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(X1)) | r2_hidden(X0,k2_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1)) ) | (~spl3_21 | ~spl3_26)),
% 0.21/0.49    inference(resolution,[],[f162,f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f141])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) ) | ~spl3_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f161])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    spl3_31 | ~spl3_3 | ~spl3_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f183,f178,f64,f201])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl3_29 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_3 | ~spl3_29)),
% 0.21/0.50    inference(resolution,[],[f179,f65])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f178])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl3_30 | ~spl3_3 | ~spl3_5 | ~spl3_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f184,f178,f72,f64,f197])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl3_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_5 | ~spl3_29)),
% 0.21/0.50    inference(backward_demodulation,[],[f73,f183])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  % (10840)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl3_29 | ~spl3_11 | ~spl3_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f165,f136,f96,f178])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl3_20 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl3_11 | ~spl3_20)),
% 0.21/0.50    inference(resolution,[],[f137,f97])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl3_27 | ~spl3_16 | ~spl3_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f139,f131,f117,f168])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl3_16 <=> ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl3_19 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0)) ) | (~spl3_16 | ~spl3_19)),
% 0.21/0.50    inference(resolution,[],[f132,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) ) | ~spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f131])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl3_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f161])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl3_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f157])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f153])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl3_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f141])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl3_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f136])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl3_19 | ~spl3_13 | ~spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f129,f108,f104,f131])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl3_13 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl3_14 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_13 | ~spl3_14)),
% 0.21/0.50    inference(superposition,[],[f105,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f108])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl3_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f117])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f28,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    k1_xboole_0 = sK2),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f108])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f104])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f100])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f36,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f96])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f72])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f64])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f60])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f56])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (10837)------------------------------
% 0.21/0.50  % (10837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10837)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (10837)Memory used [KB]: 10746
% 0.21/0.50  % (10837)Time elapsed: 0.070 s
% 0.21/0.50  % (10837)------------------------------
% 0.21/0.50  % (10837)------------------------------
% 0.21/0.50  % (10846)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (10833)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (10849)Refutation not found, incomplete strategy% (10849)------------------------------
% 0.21/0.50  % (10849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10849)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10849)Memory used [KB]: 10618
% 0.21/0.50  % (10849)Time elapsed: 0.088 s
% 0.21/0.50  % (10849)------------------------------
% 0.21/0.50  % (10849)------------------------------
% 0.21/0.50  % (10827)Success in time 0.137 s
%------------------------------------------------------------------------------
