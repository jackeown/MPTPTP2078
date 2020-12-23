%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 235 expanded)
%              Number of leaves         :   35 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  461 (1541 expanded)
%              Number of equality atoms :   39 ( 133 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f89,f118,f130,f148,f151,f169,f171,f187,f189,f246,f248,f249,f254,f256])).

fof(f256,plain,(
    spl3_31 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl3_31 ),
    inference(resolution,[],[f253,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f253,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_tarski(k1_xboole_0))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl3_31
  <=> r1_tarski(k1_xboole_0,k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f254,plain,
    ( ~ spl3_31
    | spl3_30 ),
    inference(avatar_split_clause,[],[f250,f244,f252])).

fof(f244,plain,
    ( spl3_30
  <=> m1_setfam_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f250,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_tarski(k1_xboole_0))
    | spl3_30 ),
    inference(resolution,[],[f245,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
     => m1_setfam_1(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f245,plain,
    ( ~ m1_setfam_1(k1_xboole_0,k1_xboole_0)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f244])).

fof(f249,plain,
    ( k1_xboole_0 != sK2
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f248,plain,
    ( ~ spl3_4
    | spl3_28 ),
    inference(avatar_split_clause,[],[f247,f238,f79])).

fof(f79,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f238,plain,
    ( spl3_28
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f247,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_28 ),
    inference(resolution,[],[f239,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f239,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f238])).

fof(f246,plain,
    ( ~ spl3_28
    | ~ spl3_29
    | ~ spl3_30
    | spl3_6
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f236,f166,f116,f87,f244,f241,f238])).

fof(f241,plain,
    ( spl3_29
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f87,plain,
    ( spl3_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f116,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f166,plain,
    ( spl3_18
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f236,plain,
    ( ~ m1_setfam_1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_struct_0(sK0)
    | spl3_6
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f235,f167])).

fof(f167,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f235,plain,
    ( ~ m1_setfam_1(k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_struct_0(sK0)
    | spl3_6
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f234,f117])).

fof(f117,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f234,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_struct_0(sK0)
    | ~ m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | spl3_6
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f233,f167])).

fof(f233,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | spl3_6
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f232,f117])).

fof(f232,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | spl3_6 ),
    inference(resolution,[],[f65,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f65,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | ~ m1_setfam_1(k1_xboole_0,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ m1_setfam_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 != X1
          | ~ m1_setfam_1(X1,u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 != X1
          | ~ m1_setfam_1(X1,u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f189,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl3_20 ),
    inference(resolution,[],[f186,f51])).

fof(f186,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_struct_0(sK0))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl3_20
  <=> r1_tarski(k1_xboole_0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f187,plain,
    ( ~ spl3_20
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f178,f143,f185])).

fof(f143,plain,
    ( spl3_16
  <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f178,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_16 ),
    inference(resolution,[],[f144,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f144,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f171,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_17 ),
    inference(resolution,[],[f147,f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f52])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f147,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_17
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f169,plain,
    ( spl3_18
    | ~ spl3_13
    | spl3_15 ),
    inference(avatar_split_clause,[],[f163,f138,f128,f166])).

fof(f128,plain,
    ( spl3_13
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f138,plain,
    ( spl3_15
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f163,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | k1_xboole_0 = k2_struct_0(sK0)
    | spl3_15 ),
    inference(resolution,[],[f160,f139])).

fof(f139,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f160,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f61,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f151,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | spl3_14 ),
    inference(avatar_split_clause,[],[f149,f135,f79,f83])).

fof(f83,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f135,plain,
    ( spl3_14
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f149,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_14 ),
    inference(resolution,[],[f136,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f136,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f148,plain,
    ( ~ spl3_14
    | ~ spl3_15
    | ~ spl3_5
    | ~ spl3_4
    | spl3_16
    | ~ spl3_17
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f133,f116,f67,f146,f143,f79,f83,f138,f135])).

fof(f67,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f133,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f132,f117])).

fof(f132,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f131,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f131,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | r2_hidden(k2_struct_0(sK0),sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f60,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f130,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f121,f116,f75,f128])).

fof(f75,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f121,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(superposition,[],[f76,f117])).

fof(f76,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f118,plain,
    ( spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f114,f79,f116])).

fof(f114,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f113,f80])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f56,f57])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f89,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f42,f83])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f44,f75])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f71])).

fof(f71,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f50,f67])).

fof(f50,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:00:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (30253)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (30253)Refutation not found, incomplete strategy% (30253)------------------------------
% 0.22/0.46  % (30253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (30253)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (30253)Memory used [KB]: 6140
% 0.22/0.46  % (30253)Time elapsed: 0.046 s
% 0.22/0.46  % (30253)------------------------------
% 0.22/0.46  % (30253)------------------------------
% 0.22/0.46  % (30259)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.46  % (30259)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f257,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f89,f118,f130,f148,f151,f169,f171,f187,f189,f246,f248,f249,f254,f256])).
% 0.22/0.46  fof(f256,plain,(
% 0.22/0.46    spl3_31),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f255])).
% 0.22/0.46  fof(f255,plain,(
% 0.22/0.46    $false | spl3_31),
% 0.22/0.46    inference(resolution,[],[f253,f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.46  fof(f253,plain,(
% 0.22/0.46    ~r1_tarski(k1_xboole_0,k3_tarski(k1_xboole_0)) | spl3_31),
% 0.22/0.46    inference(avatar_component_clause,[],[f252])).
% 0.22/0.46  fof(f252,plain,(
% 0.22/0.46    spl3_31 <=> r1_tarski(k1_xboole_0,k3_tarski(k1_xboole_0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.46  fof(f254,plain,(
% 0.22/0.46    ~spl3_31 | spl3_30),
% 0.22/0.46    inference(avatar_split_clause,[],[f250,f244,f252])).
% 0.22/0.46  fof(f244,plain,(
% 0.22/0.46    spl3_30 <=> m1_setfam_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.46  fof(f250,plain,(
% 0.22/0.46    ~r1_tarski(k1_xboole_0,k3_tarski(k1_xboole_0)) | spl3_30),
% 0.22/0.46    inference(resolution,[],[f245,f62])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    ( ! [X0,X1] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ! [X0,X1] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.46    inference(ennf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) => m1_setfam_1(X1,X0))),
% 0.22/0.46    inference(unused_predicate_definition_removal,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.22/0.46  fof(f245,plain,(
% 0.22/0.46    ~m1_setfam_1(k1_xboole_0,k1_xboole_0) | spl3_30),
% 0.22/0.46    inference(avatar_component_clause,[],[f244])).
% 0.22/0.46  fof(f249,plain,(
% 0.22/0.46    k1_xboole_0 != sK2 | u1_struct_0(sK0) != k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.46  fof(f248,plain,(
% 0.22/0.46    ~spl3_4 | spl3_28),
% 0.22/0.46    inference(avatar_split_clause,[],[f247,f238,f79])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    spl3_4 <=> l1_pre_topc(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.46  fof(f238,plain,(
% 0.22/0.46    spl3_28 <=> l1_struct_0(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.46  fof(f247,plain,(
% 0.22/0.46    ~l1_pre_topc(sK0) | spl3_28),
% 0.22/0.46    inference(resolution,[],[f239,f57])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,axiom,(
% 0.22/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.46  fof(f239,plain,(
% 0.22/0.46    ~l1_struct_0(sK0) | spl3_28),
% 0.22/0.46    inference(avatar_component_clause,[],[f238])).
% 0.22/0.46  fof(f246,plain,(
% 0.22/0.46    ~spl3_28 | ~spl3_29 | ~spl3_30 | spl3_6 | ~spl3_11 | ~spl3_18),
% 0.22/0.46    inference(avatar_split_clause,[],[f236,f166,f116,f87,f244,f241,f238])).
% 0.22/0.46  fof(f241,plain,(
% 0.22/0.46    spl3_29 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    spl3_6 <=> v2_struct_0(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.46  fof(f116,plain,(
% 0.22/0.46    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.46  fof(f166,plain,(
% 0.22/0.46    spl3_18 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.46  fof(f236,plain,(
% 0.22/0.46    ~m1_setfam_1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_struct_0(sK0) | (spl3_6 | ~spl3_11 | ~spl3_18)),
% 0.22/0.46    inference(forward_demodulation,[],[f235,f167])).
% 0.22/0.46  fof(f167,plain,(
% 0.22/0.46    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f166])).
% 0.22/0.46  fof(f235,plain,(
% 0.22/0.46    ~m1_setfam_1(k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_struct_0(sK0) | (spl3_6 | ~spl3_11 | ~spl3_18)),
% 0.22/0.46    inference(forward_demodulation,[],[f234,f117])).
% 0.22/0.46  fof(f117,plain,(
% 0.22/0.46    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 0.22/0.46    inference(avatar_component_clause,[],[f116])).
% 0.22/0.46  fof(f234,plain,(
% 0.22/0.46    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_struct_0(sK0) | ~m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | (spl3_6 | ~spl3_11 | ~spl3_18)),
% 0.22/0.46    inference(forward_demodulation,[],[f233,f167])).
% 0.22/0.46  fof(f233,plain,(
% 0.22/0.46    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_struct_0(sK0) | ~m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | (spl3_6 | ~spl3_11)),
% 0.22/0.46    inference(forward_demodulation,[],[f232,f117])).
% 0.22/0.46  fof(f232,plain,(
% 0.22/0.46    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_struct_0(sK0) | ~m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | spl3_6),
% 0.22/0.46    inference(resolution,[],[f65,f88])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    ~v2_struct_0(sK0) | spl3_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f87])).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    ( ! [X0] : (v2_struct_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | ~m1_setfam_1(k1_xboole_0,u1_struct_0(X0))) )),
% 0.22/0.46    inference(equality_resolution,[],[f58])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~m1_setfam_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (k1_xboole_0 != X1 | ~m1_setfam_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((k1_xboole_0 != X1 | ~m1_setfam_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,axiom,(
% 0.22/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).
% 0.22/0.46  fof(f189,plain,(
% 0.22/0.46    spl3_20),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f188])).
% 0.22/0.46  fof(f188,plain,(
% 0.22/0.46    $false | spl3_20),
% 0.22/0.46    inference(resolution,[],[f186,f51])).
% 0.22/0.46  fof(f186,plain,(
% 0.22/0.46    ~r1_tarski(k1_xboole_0,k2_struct_0(sK0)) | spl3_20),
% 0.22/0.46    inference(avatar_component_clause,[],[f185])).
% 0.22/0.46  fof(f185,plain,(
% 0.22/0.46    spl3_20 <=> r1_tarski(k1_xboole_0,k2_struct_0(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.46  fof(f187,plain,(
% 0.22/0.46    ~spl3_20 | ~spl3_16),
% 0.22/0.46    inference(avatar_split_clause,[],[f178,f143,f185])).
% 0.22/0.46  fof(f143,plain,(
% 0.22/0.46    spl3_16 <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.46  fof(f178,plain,(
% 0.22/0.46    ~r1_tarski(k1_xboole_0,k2_struct_0(sK0)) | ~spl3_16),
% 0.22/0.46    inference(resolution,[],[f144,f63])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.46  fof(f144,plain,(
% 0.22/0.46    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~spl3_16),
% 0.22/0.46    inference(avatar_component_clause,[],[f143])).
% 0.22/0.46  fof(f171,plain,(
% 0.22/0.46    spl3_17),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.46  fof(f170,plain,(
% 0.22/0.46    $false | spl3_17),
% 0.22/0.46    inference(resolution,[],[f147,f90])).
% 0.22/0.46  fof(f90,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f54,f52])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.46  fof(f147,plain,(
% 0.22/0.46    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_17),
% 0.22/0.46    inference(avatar_component_clause,[],[f146])).
% 0.22/0.46  fof(f146,plain,(
% 0.22/0.46    spl3_17 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.46  fof(f169,plain,(
% 0.22/0.46    spl3_18 | ~spl3_13 | spl3_15),
% 0.22/0.46    inference(avatar_split_clause,[],[f163,f138,f128,f166])).
% 0.22/0.46  fof(f128,plain,(
% 0.22/0.46    spl3_13 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.46  fof(f138,plain,(
% 0.22/0.46    spl3_15 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.46  fof(f163,plain,(
% 0.22/0.46    ~m1_subset_1(sK1,k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(sK0) | spl3_15),
% 0.22/0.46    inference(resolution,[],[f160,f139])).
% 0.22/0.46  fof(f139,plain,(
% 0.22/0.46    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl3_15),
% 0.22/0.46    inference(avatar_component_clause,[],[f138])).
% 0.22/0.46  fof(f160,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~m1_subset_1(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.46    inference(resolution,[],[f61,f55])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.46    inference(flattening,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.46  fof(f151,plain,(
% 0.22/0.46    ~spl3_5 | ~spl3_4 | spl3_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f149,f135,f79,f83])).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    spl3_5 <=> v2_pre_topc(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.46  fof(f135,plain,(
% 0.22/0.46    spl3_14 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.46  fof(f149,plain,(
% 0.22/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_14),
% 0.22/0.46    inference(resolution,[],[f136,f59])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(flattening,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.22/0.46  fof(f136,plain,(
% 0.22/0.46    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl3_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f135])).
% 0.22/0.46  fof(f148,plain,(
% 0.22/0.46    ~spl3_14 | ~spl3_15 | ~spl3_5 | ~spl3_4 | spl3_16 | ~spl3_17 | ~spl3_1 | ~spl3_11),
% 0.22/0.46    inference(avatar_split_clause,[],[f133,f116,f67,f146,f143,f79,f83,f138,f135])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    spl3_1 <=> k1_xboole_0 = sK2),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.46  fof(f133,plain,(
% 0.22/0.46    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | (~spl3_1 | ~spl3_11)),
% 0.22/0.46    inference(forward_demodulation,[],[f132,f117])).
% 0.22/0.46  fof(f132,plain,(
% 0.22/0.46    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_1),
% 0.22/0.46    inference(forward_demodulation,[],[f131,f68])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    k1_xboole_0 = sK2 | ~spl3_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f67])).
% 0.22/0.46  fof(f131,plain,(
% 0.22/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | r2_hidden(k2_struct_0(sK0),sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    inference(resolution,[],[f60,f49])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | r2_hidden(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.46    inference(nnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,negated_conjecture,(
% 0.22/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.46    inference(negated_conjecture,[],[f15])).
% 0.22/0.46  fof(f15,conjecture,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(flattening,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.46  fof(f130,plain,(
% 0.22/0.46    spl3_13 | ~spl3_3 | ~spl3_11),
% 0.22/0.46    inference(avatar_split_clause,[],[f121,f116,f75,f128])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    spl3_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.46  fof(f121,plain,(
% 0.22/0.46    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_11)),
% 0.22/0.46    inference(superposition,[],[f76,f117])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f75])).
% 0.22/0.46  fof(f118,plain,(
% 0.22/0.46    spl3_11 | ~spl3_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f114,f79,f116])).
% 0.22/0.46  fof(f114,plain,(
% 0.22/0.46    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_4),
% 0.22/0.46    inference(resolution,[],[f113,f80])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f79])).
% 0.22/0.46  fof(f113,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.46    inference(resolution,[],[f56,f57])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.46  fof(f89,plain,(
% 0.22/0.46    ~spl3_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f41,f87])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ~v2_struct_0(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    spl3_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f42,f83])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    v2_pre_topc(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    spl3_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f43,f79])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    l1_pre_topc(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f44,f75])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    spl3_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f45,f71])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    spl3_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f50,f67])).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    k1_xboole_0 = sK2),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (30259)------------------------------
% 0.22/0.46  % (30259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (30259)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (30259)Memory used [KB]: 10746
% 0.22/0.47  % (30259)Time elapsed: 0.054 s
% 0.22/0.47  % (30259)------------------------------
% 0.22/0.47  % (30259)------------------------------
% 0.22/0.47  % (30252)Success in time 0.104 s
%------------------------------------------------------------------------------
