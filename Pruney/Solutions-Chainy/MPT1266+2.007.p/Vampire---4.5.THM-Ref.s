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
% DateTime   : Thu Dec  3 13:12:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 332 expanded)
%              Number of leaves         :   38 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  478 ( 932 expanded)
%              Number of equality atoms :   95 ( 234 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f80,f85,f90,f98,f106,f112,f122,f142,f192,f373,f439,f490,f610,f1095,f1108,f1158,f1163,f1166,f1185,f1190,f1191])).

fof(f1191,plain,
    ( k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | k1_tops_1(sK0,sK1) != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1190,plain,(
    spl2_110 ),
    inference(avatar_contradiction_clause,[],[f1186])).

fof(f1186,plain,
    ( $false
    | spl2_110 ),
    inference(unit_resulting_resolution,[],[f158,f1184])).

fof(f1184,plain,
    ( k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl2_110 ),
    inference(avatar_component_clause,[],[f1182])).

fof(f1182,plain,
    ( spl2_110
  <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).

fof(f158,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f149,f68])).

fof(f68,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f47,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f149,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1185,plain,
    ( ~ spl2_110
    | spl2_50
    | ~ spl2_107 ),
    inference(avatar_split_clause,[],[f1175,f1071,f470,f1182])).

fof(f470,plain,
    ( spl2_50
  <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f1071,plain,
    ( spl2_107
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).

fof(f1175,plain,
    ( k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl2_50
    | ~ spl2_107 ),
    inference(backward_demodulation,[],[f471,f1073])).

fof(f1073,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_107 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f471,plain,
    ( k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | spl2_50 ),
    inference(avatar_component_clause,[],[f470])).

fof(f1166,plain,
    ( ~ spl2_4
    | spl2_107
    | ~ spl2_37
    | ~ spl2_6
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f1165,f369,f102,f379,f1071,f87])).

fof(f87,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f379,plain,
    ( spl2_37
  <=> m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f102,plain,
    ( spl2_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f369,plain,
    ( spl2_35
  <=> v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f1165,plain,
    ( ~ m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f1164,f104])).

fof(f104,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f1164,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_35 ),
    inference(resolution,[],[f370,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f370,plain,
    ( v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f369])).

fof(f1163,plain,
    ( ~ spl2_4
    | spl2_35
    | ~ spl2_7
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f1162,f184,f102,f72,f109,f369,f87])).

fof(f109,plain,
    ( spl2_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f72,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f184,plain,
    ( spl2_14
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f1162,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f1161,f104])).

fof(f1161,plain,
    ( v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f1160,f186])).

fof(f186,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f1160,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f1159,f104])).

fof(f1159,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f73,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f73,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f1158,plain,
    ( ~ spl2_4
    | spl2_35
    | ~ spl2_37
    | ~ spl2_6
    | ~ spl2_107 ),
    inference(avatar_split_clause,[],[f1157,f1071,f102,f379,f369,f87])).

fof(f1157,plain,
    ( ~ m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f1154,f104])).

fof(f1154,plain,
    ( v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_107 ),
    inference(trivial_inequality_removal,[],[f1153])).

fof(f1153,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_107 ),
    inference(superposition,[],[f54,f1073])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1108,plain,
    ( spl2_107
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_37
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f1069,f470,f379,f102,f87,f1071])).

fof(f1069,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_37
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f1068,f68])).

fof(f1068,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_37
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f1024,f472])).

fof(f472,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f470])).

fof(f1024,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_37 ),
    inference(unit_resulting_resolution,[],[f380,f319])).

fof(f319,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X1))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f220,f62])).

fof(f220,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f219,f104])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f212,f104])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f380,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f379])).

fof(f1095,plain,
    ( spl2_108
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f467,f184,f109,f102,f87,f1091])).

fof(f1091,plain,
    ( spl2_108
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).

fof(f467,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f461,f186])).

fof(f461,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f111,f268])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f267,f104])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f259,f104])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f52,f89])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f109])).

% (27631)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f610,plain,
    ( ~ spl2_48
    | spl2_37 ),
    inference(avatar_split_clause,[],[f602,f379,f436])).

fof(f436,plain,
    ( spl2_48
  <=> r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f602,plain,
    ( ~ r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | spl2_37 ),
    inference(unit_resulting_resolution,[],[f381,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f381,plain,
    ( ~ m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_37 ),
    inference(avatar_component_clause,[],[f379])).

fof(f490,plain,
    ( spl2_50
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f489,f184,f109,f102,f87,f76,f470])).

fof(f76,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f489,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f488,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f488,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f466,f186])).

fof(f466,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(resolution,[],[f268,f111])).

fof(f439,plain,
    ( spl2_48
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f432,f138,f436])).

fof(f138,plain,
    ( spl2_9
  <=> sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f432,plain,
    ( r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_9 ),
    inference(superposition,[],[f127,f140])).

fof(f140,plain,
    ( sK1 = k3_xboole_0(sK1,k2_struct_0(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f127,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f69,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f57,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f373,plain,
    ( spl2_1
    | ~ spl2_7
    | ~ spl2_35
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f362,f184,f102,f87,f369,f109,f72])).

fof(f362,plain,
    ( ~ v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_tops_1(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f257,f186])).

% (27640)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f257,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f256,f104])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f255,f104])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f56,f89])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f192,plain,
    ( spl2_14
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f191,f138,f109,f184])).

fof(f191,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f190,f140])).

fof(f190,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK1,k2_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f180,f58])).

fof(f180,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_7 ),
    inference(resolution,[],[f70,f111])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f59])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f142,plain,
    ( spl2_9
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f134,f118,f138])).

fof(f118,plain,
    ( spl2_8
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f134,plain,
    ( sK1 = k3_xboole_0(sK1,k2_struct_0(sK0))
    | ~ spl2_8 ),
    inference(resolution,[],[f60,f120])).

fof(f120,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f122,plain,
    ( spl2_8
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f116,f109,f118])).

fof(f116,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl2_7 ),
    inference(resolution,[],[f64,f111])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f107,f102,f82,f109])).

fof(f82,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f84,f104])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f106,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f100,f94,f102])).

fof(f94,plain,
    ( spl2_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f100,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f50,f96])).

fof(f96,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f98,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f92,f87,f94])).

fof(f92,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f51,f89])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f90,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

% (27648)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f37,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f85,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f44,f76,f72])).

fof(f44,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f45,f76,f72])).

fof(f45,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:35:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (27636)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (27639)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (27644)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (27645)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (27637)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (27638)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (27634)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (27635)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (27647)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (27646)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (27643)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (27642)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (27637)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1192,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f79,f80,f85,f90,f98,f106,f112,f122,f142,f192,f373,f439,f490,f610,f1095,f1108,f1158,f1163,f1166,f1185,f1190,f1191])).
% 0.21/0.54  fof(f1191,plain,(
% 0.21/0.54    k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) | k1_tops_1(sK0,sK1) != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f1190,plain,(
% 0.21/0.54    spl2_110),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1186])).
% 0.21/0.54  fof(f1186,plain,(
% 0.21/0.54    $false | spl2_110),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f158,f1184])).
% 0.21/0.54  fof(f1184,plain,(
% 0.21/0.54    k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | spl2_110),
% 0.21/0.54    inference(avatar_component_clause,[],[f1182])).
% 0.21/0.54  fof(f1182,plain,(
% 0.21/0.54    spl2_110 <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f149,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f46,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f49,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f48,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f1185,plain,(
% 0.21/0.54    ~spl2_110 | spl2_50 | ~spl2_107),
% 0.21/0.54    inference(avatar_split_clause,[],[f1175,f1071,f470,f1182])).
% 0.21/0.54  fof(f470,plain,(
% 0.21/0.54    spl2_50 <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.21/0.54  fof(f1071,plain,(
% 0.21/0.54    spl2_107 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).
% 0.21/0.54  fof(f1175,plain,(
% 0.21/0.54    k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | (spl2_50 | ~spl2_107)),
% 0.21/0.54    inference(backward_demodulation,[],[f471,f1073])).
% 0.21/0.54  fof(f1073,plain,(
% 0.21/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_107),
% 0.21/0.54    inference(avatar_component_clause,[],[f1071])).
% 0.21/0.54  fof(f471,plain,(
% 0.21/0.54    k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) | spl2_50),
% 0.21/0.54    inference(avatar_component_clause,[],[f470])).
% 0.21/0.54  fof(f1166,plain,(
% 0.21/0.54    ~spl2_4 | spl2_107 | ~spl2_37 | ~spl2_6 | ~spl2_35),
% 0.21/0.54    inference(avatar_split_clause,[],[f1165,f369,f102,f379,f1071,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    spl2_4 <=> l1_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    spl2_37 <=> m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl2_6 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    spl2_35 <=> v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.54  fof(f1165,plain,(
% 0.21/0.54    ~m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_35)),
% 0.21/0.54    inference(forward_demodulation,[],[f1164,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f1164,plain,(
% 0.21/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_35),
% 0.21/0.54    inference(resolution,[],[f370,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_35),
% 0.21/0.54    inference(avatar_component_clause,[],[f369])).
% 0.21/0.54  fof(f1163,plain,(
% 0.21/0.54    ~spl2_4 | spl2_35 | ~spl2_7 | ~spl2_1 | ~spl2_6 | ~spl2_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f1162,f184,f102,f72,f109,f369,f87])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl2_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    spl2_14 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.54  fof(f1162,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6 | ~spl2_14)),
% 0.21/0.54    inference(forward_demodulation,[],[f1161,f104])).
% 0.21/0.54  fof(f1161,plain,(
% 0.21/0.54    v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6 | ~spl2_14)),
% 0.21/0.54    inference(forward_demodulation,[],[f1160,f186])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | ~spl2_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f184])).
% 0.21/0.54  fof(f1160,plain,(
% 0.21/0.54    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f1159,f104])).
% 0.21/0.54  fof(f1159,plain,(
% 0.21/0.54    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.21/0.54    inference(resolution,[],[f73,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f72])).
% 0.21/0.54  fof(f1158,plain,(
% 0.21/0.54    ~spl2_4 | spl2_35 | ~spl2_37 | ~spl2_6 | ~spl2_107),
% 0.21/0.54    inference(avatar_split_clause,[],[f1157,f1071,f102,f379,f369,f87])).
% 0.21/0.54  fof(f1157,plain,(
% 0.21/0.54    ~m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_107)),
% 0.21/0.54    inference(forward_demodulation,[],[f1154,f104])).
% 0.21/0.54  fof(f1154,plain,(
% 0.21/0.54    v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_107),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f1153])).
% 0.21/0.54  fof(f1153,plain,(
% 0.21/0.54    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_107),
% 0.21/0.54    inference(superposition,[],[f54,f1073])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f1108,plain,(
% 0.21/0.54    spl2_107 | ~spl2_4 | ~spl2_6 | ~spl2_37 | ~spl2_50),
% 0.21/0.54    inference(avatar_split_clause,[],[f1069,f470,f379,f102,f87,f1071])).
% 0.21/0.54  fof(f1069,plain,(
% 0.21/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_37 | ~spl2_50)),
% 0.21/0.54    inference(forward_demodulation,[],[f1068,f68])).
% 0.21/0.54  fof(f1068,plain,(
% 0.21/0.54    k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_37 | ~spl2_50)),
% 0.21/0.54    inference(forward_demodulation,[],[f1024,f472])).
% 0.21/0.54  fof(f472,plain,(
% 0.21/0.54    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_50),
% 0.21/0.54    inference(avatar_component_clause,[],[f470])).
% 0.21/0.54  fof(f1024,plain,(
% 0.21/0.54    k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))) | (~spl2_4 | ~spl2_6 | ~spl2_37)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f380,f319])).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X1)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.54    inference(resolution,[],[f220,f62])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f219,f104])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f212,f104])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 0.21/0.54    inference(resolution,[],[f63,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_37),
% 0.21/0.54    inference(avatar_component_clause,[],[f379])).
% 0.21/0.54  fof(f1095,plain,(
% 0.21/0.54    spl2_108 | ~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f467,f184,f109,f102,f87,f1091])).
% 0.21/0.54  fof(f1091,plain,(
% 0.21/0.54    spl2_108 <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).
% 0.21/0.54  fof(f467,plain,(
% 0.21/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_14)),
% 0.21/0.54    inference(forward_demodulation,[],[f461,f186])).
% 0.21/0.54  fof(f461,plain,(
% 0.21/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_7)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f111,f268])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f267,f104])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f259,f104])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl2_4),
% 0.21/0.54    inference(resolution,[],[f52,f89])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f109])).
% 0.21/0.54  % (27631)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.54  fof(f610,plain,(
% 0.21/0.54    ~spl2_48 | spl2_37),
% 0.21/0.54    inference(avatar_split_clause,[],[f602,f379,f436])).
% 0.21/0.54  fof(f436,plain,(
% 0.21/0.54    spl2_48 <=> r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.21/0.54  fof(f602,plain,(
% 0.21/0.54    ~r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | spl2_37),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f381,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    ~m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_37),
% 0.21/0.54    inference(avatar_component_clause,[],[f379])).
% 0.21/0.54  fof(f490,plain,(
% 0.21/0.54    spl2_50 | ~spl2_2 | ~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f489,f184,f109,f102,f87,f76,f470])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.54  fof(f489,plain,(
% 0.21/0.54    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_14)),
% 0.21/0.54    inference(forward_demodulation,[],[f488,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f76])).
% 0.21/0.54  fof(f488,plain,(
% 0.21/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_14)),
% 0.21/0.54    inference(forward_demodulation,[],[f466,f186])).
% 0.21/0.54  fof(f466,plain,(
% 0.21/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_7)),
% 0.21/0.54    inference(resolution,[],[f268,f111])).
% 0.21/0.54  fof(f439,plain,(
% 0.21/0.54    spl2_48 | ~spl2_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f432,f138,f436])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    spl2_9 <=> sK1 = k3_xboole_0(sK1,k2_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.54  fof(f432,plain,(
% 0.21/0.54    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl2_9),
% 0.21/0.54    inference(superposition,[],[f127,f140])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)) | ~spl2_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f138])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 0.21/0.54    inference(superposition,[],[f69,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f57,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    spl2_1 | ~spl2_7 | ~spl2_35 | ~spl2_4 | ~spl2_6 | ~spl2_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f362,f184,f102,f87,f369,f109,f72])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    ~v1_tops_1(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(sK1,sK0) | (~spl2_4 | ~spl2_6 | ~spl2_14)),
% 0.21/0.54    inference(superposition,[],[f257,f186])).
% 0.21/0.54  % (27640)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f256,f104])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f255,f104])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | ~spl2_4),
% 0.21/0.54    inference(resolution,[],[f56,f89])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    spl2_14 | ~spl2_7 | ~spl2_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f191,f138,f109,f184])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | (~spl2_7 | ~spl2_9)),
% 0.21/0.54    inference(forward_demodulation,[],[f190,f140])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK1,k2_struct_0(sK0))) | ~spl2_7),
% 0.21/0.54    inference(forward_demodulation,[],[f180,f58])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_7),
% 0.21/0.54    inference(resolution,[],[f70,f111])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f61,f59])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    spl2_9 | ~spl2_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f134,f118,f138])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl2_8 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)) | ~spl2_8),
% 0.21/0.54    inference(resolution,[],[f60,f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl2_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f118])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    spl2_8 | ~spl2_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f116,f109,f118])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl2_7),
% 0.21/0.54    inference(resolution,[],[f64,f111])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    spl2_7 | ~spl2_3 | ~spl2_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f107,f102,f82,f109])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_3 | ~spl2_6)),
% 0.21/0.54    inference(backward_demodulation,[],[f84,f104])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f82])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    spl2_6 | ~spl2_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f100,f94,f102])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl2_5 <=> l1_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_5),
% 0.21/0.54    inference(resolution,[],[f50,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    l1_struct_0(sK0) | ~spl2_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f94])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl2_5 | ~spl2_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f92,f87,f94])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    l1_struct_0(sK0) | ~spl2_4),
% 0.21/0.54    inference(resolution,[],[f51,f89])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    spl2_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f87])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (27648)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f19])).
% 0.21/0.54  fof(f19,conjecture,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    spl2_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f82])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl2_1 | spl2_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f76,f72])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ~spl2_1 | ~spl2_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f76,f72])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (27637)------------------------------
% 0.21/0.54  % (27637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27637)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (27637)Memory used [KB]: 6908
% 0.21/0.54  % (27637)Time elapsed: 0.088 s
% 0.21/0.54  % (27637)------------------------------
% 0.21/0.54  % (27637)------------------------------
% 0.21/0.54  % (27632)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.54  % (27630)Success in time 0.179 s
%------------------------------------------------------------------------------
