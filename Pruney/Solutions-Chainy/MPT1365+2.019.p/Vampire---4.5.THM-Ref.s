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
% DateTime   : Thu Dec  3 13:14:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 287 expanded)
%              Number of leaves         :   25 ( 117 expanded)
%              Depth                    :   11
%              Number of atoms          :  382 (1211 expanded)
%              Number of equality atoms :   14 (  61 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f126,f131,f255,f271,f277,f512])).

% (12669)Refutation not found, incomplete strategy% (12669)------------------------------
% (12669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f512,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | spl3_15
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | spl3_15
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f439,f195])).

fof(f195,plain,(
    ! [X0,X1] : r1_tarski(k9_subset_1(X0,X1,X0),X0) ),
    inference(unit_resulting_resolution,[],[f95,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(k9_subset_1(X1,X2,X0),X1) ) ),
    inference(resolution,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f95,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f439,plain,
    ( ~ r1_tarski(k9_subset_1(sK2,sK1,sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | spl3_15
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f74,f84,f254,f276,f179,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v2_compts_1(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f118,f54])).

fof(f54,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f37,f59])).

fof(f59,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(f179,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f176,f149])).

% (12676)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f149,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(unit_resulting_resolution,[],[f95,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f38])).

% (12660)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f176,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f100,f108])).

fof(f108,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f84,f47])).

fof(f100,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f84,f44])).

fof(f276,plain,
    ( v4_pre_topc(k9_subset_1(sK2,sK1,sK2),sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl3_19
  <=> v4_pre_topc(k9_subset_1(sK2,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f254,plain,
    ( ~ v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl3_15
  <=> v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f84,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_5
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f277,plain,
    ( spl3_19
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f272,f268,f274])).

fof(f268,plain,
    ( spl3_18
  <=> v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f272,plain,
    ( v4_pre_topc(k9_subset_1(sK2,sK1,sK2),sK0)
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f270,f149])).

fof(f270,plain,
    ( v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f268])).

fof(f271,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f137,f128,f123,f82,f77,f57,f52,f268])).

fof(f77,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f123,plain,
    ( spl3_10
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f128,plain,
    ( spl3_11
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f137,plain,
    ( v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f54,f59,f125,f79,f84,f130,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

fof(f130,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f125,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f255,plain,
    ( ~ spl3_15
    | ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f178,f87,f82,f252])).

fof(f87,plain,
    ( spl3_8
  <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f178,plain,
    ( ~ v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0)
    | ~ spl3_7
    | spl3_8 ),
    inference(forward_demodulation,[],[f175,f149])).

fof(f175,plain,
    ( ~ v2_compts_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_7
    | spl3_8 ),
    inference(superposition,[],[f89,f108])).

fof(f89,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f131,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f114,f82,f72,f62,f57,f52,f128])).

fof(f62,plain,
    ( spl3_3
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f114,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f54,f59,f64,f74,f84,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
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
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

fof(f64,plain,
    ( v8_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f126,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f113,f77,f67,f62,f57,f52,f123])).

fof(f67,plain,
    ( spl3_4
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f113,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f54,f59,f64,f69,f79,f36])).

fof(f69,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f90,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f35,f87])).

fof(f35,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_compts_1(X2,sK0)
            & v2_compts_1(X1,sK0)
            & v8_pre_topc(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_compts_1(X2,sK0)
          & v2_compts_1(sK1,sK0)
          & v8_pre_topc(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_compts_1(X2,sK0)
        & v2_compts_1(sK1,sK0)
        & v8_pre_topc(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_compts_1(sK2,sK0)
      & v2_compts_1(sK1,sK0)
      & v8_pre_topc(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
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
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

fof(f85,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f31,f82])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (12661)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.48  % (12667)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (12659)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (12687)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (12687)Refutation not found, incomplete strategy% (12687)------------------------------
% 0.21/0.51  % (12687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12687)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12687)Memory used [KB]: 10746
% 0.21/0.51  % (12687)Time elapsed: 0.109 s
% 0.21/0.51  % (12687)------------------------------
% 0.21/0.51  % (12687)------------------------------
% 0.21/0.51  % (12663)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (12675)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (12679)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (12665)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (12682)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (12672)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (12662)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (12675)Refutation not found, incomplete strategy% (12675)------------------------------
% 0.21/0.52  % (12675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12675)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12675)Memory used [KB]: 10746
% 0.21/0.52  % (12675)Time elapsed: 0.108 s
% 0.21/0.52  % (12675)------------------------------
% 0.21/0.52  % (12675)------------------------------
% 0.21/0.52  % (12664)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (12669)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (12670)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (12686)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (12681)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (12685)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (12674)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (12666)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (12684)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (12688)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (12673)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (12680)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (12677)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (12679)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f540,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f126,f131,f255,f271,f277,f512])).
% 0.21/0.54  % (12669)Refutation not found, incomplete strategy% (12669)------------------------------
% 0.21/0.54  % (12669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  fof(f512,plain,(
% 0.21/0.54    ~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_7 | spl3_15 | ~spl3_19),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f511])).
% 0.21/0.54  fof(f511,plain,(
% 0.21/0.54    $false | (~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_7 | spl3_15 | ~spl3_19)),
% 0.21/0.54    inference(subsumption_resolution,[],[f439,f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k9_subset_1(X0,X1,X0),X0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f95,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k9_subset_1(X1,X2,X0),X1)) )),
% 0.21/0.54    inference(resolution,[],[f44,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f49,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f439,plain,(
% 0.21/0.54    ~r1_tarski(k9_subset_1(sK2,sK1,sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_7 | spl3_15 | ~spl3_19)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f74,f84,f254,f276,f179,f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_compts_1(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v2_compts_1(X0,sK0)) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f118,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    v2_pre_topc(sK0) | ~spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl3_1 <=> v2_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v4_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | ~v2_compts_1(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~v2_pre_topc(sK0)) ) | ~spl3_2),
% 0.21/0.54    inference(resolution,[],[f37,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    l1_pre_topc(sK0) | ~spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl3_2 <=> l1_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X2,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_7),
% 0.21/0.54    inference(forward_demodulation,[],[f176,f149])).
% 0.21/0.54  % (12676)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f95,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f45,f38])).
% 0.21/0.54  % (12660)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_7),
% 0.21/0.54    inference(superposition,[],[f100,f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2))) ) | ~spl3_7),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f84,f47])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_7),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f84,f44])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    v4_pre_topc(k9_subset_1(sK2,sK1,sK2),sK0) | ~spl3_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f274])).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    spl3_19 <=> v4_pre_topc(k9_subset_1(sK2,sK1,sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    ~v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) | spl3_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f252])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    spl3_15 <=> v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    v2_compts_1(sK2,sK0) | ~spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl3_5 <=> v2_compts_1(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    spl3_19 | ~spl3_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f272,f268,f274])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    spl3_18 <=> v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    v4_pre_topc(k9_subset_1(sK2,sK1,sK2),sK0) | ~spl3_18),
% 0.21/0.54    inference(forward_demodulation,[],[f270,f149])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | ~spl3_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f268])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    spl3_18 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f137,f128,f123,f82,f77,f57,f52,f268])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    spl3_10 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl3_11 <=> v4_pre_topc(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f54,f59,f125,f79,f84,f130,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f46,f38])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    v4_pre_topc(sK2,sK0) | ~spl3_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f128])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f77])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    v4_pre_topc(sK1,sK0) | ~spl3_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f123])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    ~spl3_15 | ~spl3_7 | spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f178,f87,f82,f252])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    spl3_8 <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    ~v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) | (~spl3_7 | spl3_8)),
% 0.21/0.54    inference(forward_demodulation,[],[f175,f149])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ~v2_compts_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | (~spl3_7 | spl3_8)),
% 0.21/0.54    inference(superposition,[],[f89,f108])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl3_11 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f114,f82,f72,f62,f57,f52,f128])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl3_3 <=> v8_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    v4_pre_topc(sK2,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f54,f59,f64,f74,f84,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v8_pre_topc(X0) | ~v2_compts_1(X1,X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    v8_pre_topc(sK0) | ~spl3_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f62])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    spl3_10 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f113,f77,f67,f62,f57,f52,f123])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl3_4 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    v4_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f54,f59,f64,f69,f79,f36])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    v2_compts_1(sK1,sK0) | ~spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f67])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ~spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f87])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f9])).
% 0.21/0.54  fof(f9,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f31,f82])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f77])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f72])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v2_compts_1(sK2,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f67])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    v2_compts_1(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl3_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f32,f62])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    v8_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f57])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    spl3_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f28,f52])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (12679)------------------------------
% 0.21/0.54  % (12679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12679)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (12679)Memory used [KB]: 11129
% 0.21/0.54  % (12679)Time elapsed: 0.140 s
% 0.21/0.54  % (12679)------------------------------
% 0.21/0.54  % (12679)------------------------------
% 0.21/0.55  % (12658)Success in time 0.187 s
%------------------------------------------------------------------------------
