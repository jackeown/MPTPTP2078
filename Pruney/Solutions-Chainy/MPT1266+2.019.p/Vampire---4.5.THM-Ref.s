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
% DateTime   : Thu Dec  3 13:12:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 364 expanded)
%              Number of leaves         :   35 ( 148 expanded)
%              Depth                    :   16
%              Number of atoms          :  417 ( 896 expanded)
%              Number of equality atoms :   97 ( 283 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1814,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f94,f99,f107,f115,f128,f134,f478,f631,f1253,f1273,f1279,f1284,f1804,f1812])).

fof(f1812,plain,
    ( ~ spl2_4
    | spl2_53
    | ~ spl2_9
    | ~ spl2_6
    | ~ spl2_140 ),
    inference(avatar_split_clause,[],[f1811,f1241,f111,f131,f475,f96])).

fof(f96,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f475,plain,
    ( spl2_53
  <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f131,plain,
    ( spl2_9
  <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f111,plain,
    ( spl2_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1241,plain,
    ( spl2_140
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_140])])).

fof(f1811,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_140 ),
    inference(forward_demodulation,[],[f1802,f113])).

fof(f113,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f1802,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_140 ),
    inference(trivial_inequality_removal,[],[f1801])).

fof(f1801,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_140 ),
    inference(superposition,[],[f55,f1243])).

fof(f1243,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_140 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f1804,plain,
    ( spl2_2
    | ~ spl2_140
    | ~ spl2_141 ),
    inference(avatar_split_clause,[],[f1803,f1269,f1241,f85])).

fof(f85,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1269,plain,
    ( spl2_141
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_141])])).

fof(f1803,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_140
    | ~ spl2_141 ),
    inference(forward_demodulation,[],[f1797,f510])).

fof(f510,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f143,f302])).

fof(f302,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f301,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f301,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f261,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f261,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f48,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f76])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f143,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1797,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_140
    | ~ spl2_141 ),
    inference(backward_demodulation,[],[f1271,f1243])).

fof(f1271,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_141 ),
    inference(avatar_component_clause,[],[f1269])).

% (21990)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f1284,plain,
    ( ~ spl2_4
    | spl2_140
    | ~ spl2_9
    | ~ spl2_6
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f1283,f475,f111,f131,f1241,f96])).

fof(f1283,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f1282,f113])).

fof(f1282,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_53 ),
    inference(resolution,[],[f476,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f476,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f475])).

fof(f1279,plain,
    ( ~ spl2_4
    | spl2_53
    | ~ spl2_8
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f1278,f111,f81,f125,f475,f96])).

fof(f125,plain,
    ( spl2_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f81,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1278,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f1277,f113])).

fof(f1277,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f1276,f113])).

fof(f1276,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f82,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f1273,plain,
    ( spl2_141
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f550,f125,f111,f96,f1269])).

fof(f550,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f127,f240])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f239,f113])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f232,f113])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f53,f98])).

fof(f98,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f127,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1253,plain,
    ( spl2_140
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f1252,f566,f131,f111,f96,f1241])).

fof(f566,plain,
    ( spl2_65
  <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f1252,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_65 ),
    inference(forward_demodulation,[],[f1251,f302])).

fof(f1251,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_65 ),
    inference(forward_demodulation,[],[f1176,f568])).

fof(f568,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f566])).

fof(f1176,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f207,f133])).

fof(f133,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f131])).

% (22003)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f172,f63])).

fof(f172,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f171,f113])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f164,f113])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f64,f98])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f631,plain,
    ( spl2_65
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f630,f125,f111,f96,f85,f566])).

fof(f630,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f563,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f563,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f240,f127])).

fof(f478,plain,
    ( ~ spl2_53
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f470,f125,f111,f96,f81,f475])).

fof(f470,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f83,f127,f230])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f229,f113])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f228,f113])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f57,f98])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f134,plain,
    ( spl2_9
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f129,f125,f131])).

fof(f129,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f127,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f128,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f123,f111,f91,f125])).

fof(f91,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f123,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f93,f113])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f115,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f109,f103,f111])).

fof(f103,plain,
    ( spl2_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f109,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f51,f105])).

fof(f105,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f107,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f101,f96,f103])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f52,f98])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f99,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f94,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f91])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f46,f85,f81])).

fof(f46,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f47,f85,f81])).

fof(f47,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:17:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (22004)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (21996)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.44  % (22000)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (21996)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f1814,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f88,f89,f94,f99,f107,f115,f128,f134,f478,f631,f1253,f1273,f1279,f1284,f1804,f1812])).
% 0.21/0.46  fof(f1812,plain,(
% 0.21/0.46    ~spl2_4 | spl2_53 | ~spl2_9 | ~spl2_6 | ~spl2_140),
% 0.21/0.46    inference(avatar_split_clause,[],[f1811,f1241,f111,f131,f475,f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl2_4 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f475,plain,(
% 0.21/0.46    spl2_53 <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    spl2_9 <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    spl2_6 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.46  fof(f1241,plain,(
% 0.21/0.46    spl2_140 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_140])])).
% 0.21/0.46  fof(f1811,plain,(
% 0.21/0.46    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_140)),
% 0.21/0.46    inference(forward_demodulation,[],[f1802,f113])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f111])).
% 0.21/0.46  fof(f1802,plain,(
% 0.21/0.46    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_140),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f1801])).
% 0.21/0.46  fof(f1801,plain,(
% 0.21/0.46    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_140),
% 0.21/0.46    inference(superposition,[],[f55,f1243])).
% 0.21/0.46  fof(f1243,plain,(
% 0.21/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl2_140),
% 0.21/0.46    inference(avatar_component_clause,[],[f1241])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.46  fof(f1804,plain,(
% 0.21/0.46    spl2_2 | ~spl2_140 | ~spl2_141),
% 0.21/0.46    inference(avatar_split_clause,[],[f1803,f1269,f1241,f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f1269,plain,(
% 0.21/0.46    spl2_141 <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_141])])).
% 0.21/0.46  fof(f1803,plain,(
% 0.21/0.46    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_140 | ~spl2_141)),
% 0.21/0.46    inference(forward_demodulation,[],[f1797,f510])).
% 0.21/0.46  fof(f510,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f143,f302])).
% 0.21/0.46  fof(f302,plain,(
% 0.21/0.46    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(forward_demodulation,[],[f301,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.46  fof(f301,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f261,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f49,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f58,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f59,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f65,f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f67,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f68,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f69,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f62,f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f60,f76])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.46  fof(f1797,plain,(
% 0.21/0.46    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_140 | ~spl2_141)),
% 0.21/0.46    inference(backward_demodulation,[],[f1271,f1243])).
% 0.21/0.46  fof(f1271,plain,(
% 0.21/0.46    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_141),
% 0.21/0.46    inference(avatar_component_clause,[],[f1269])).
% 0.21/0.46  % (21990)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  fof(f1284,plain,(
% 0.21/0.46    ~spl2_4 | spl2_140 | ~spl2_9 | ~spl2_6 | ~spl2_53),
% 0.21/0.46    inference(avatar_split_clause,[],[f1283,f475,f111,f131,f1241,f96])).
% 0.21/0.46  fof(f1283,plain,(
% 0.21/0.46    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_53)),
% 0.21/0.46    inference(forward_demodulation,[],[f1282,f113])).
% 0.21/0.46  fof(f1282,plain,(
% 0.21/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_53),
% 0.21/0.46    inference(resolution,[],[f476,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f476,plain,(
% 0.21/0.46    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~spl2_53),
% 0.21/0.46    inference(avatar_component_clause,[],[f475])).
% 0.21/0.46  fof(f1279,plain,(
% 0.21/0.46    ~spl2_4 | spl2_53 | ~spl2_8 | ~spl2_1 | ~spl2_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f1278,f111,f81,f125,f475,f96])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    spl2_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f1278,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6)),
% 0.21/0.46    inference(forward_demodulation,[],[f1277,f113])).
% 0.21/0.46  fof(f1277,plain,(
% 0.21/0.46    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6)),
% 0.21/0.46    inference(forward_demodulation,[],[f1276,f113])).
% 0.21/0.46  fof(f1276,plain,(
% 0.21/0.46    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.21/0.46    inference(resolution,[],[f82,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f1273,plain,(
% 0.21/0.47    spl2_141 | ~spl2_4 | ~spl2_6 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f550,f125,f111,f96,f1269])).
% 0.21/0.47  fof(f550,plain,(
% 0.21/0.47    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f127,f240])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(forward_demodulation,[],[f239,f113])).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(forward_demodulation,[],[f232,f113])).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl2_4),
% 0.21/0.47    inference(resolution,[],[f53,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f125])).
% 0.21/0.47  fof(f1253,plain,(
% 0.21/0.47    spl2_140 | ~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_65),
% 0.21/0.47    inference(avatar_split_clause,[],[f1252,f566,f131,f111,f96,f1241])).
% 0.21/0.47  fof(f566,plain,(
% 0.21/0.47    spl2_65 <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 0.21/0.47  fof(f1252,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_65)),
% 0.21/0.47    inference(forward_demodulation,[],[f1251,f302])).
% 0.21/0.47  fof(f1251,plain,(
% 0.21/0.47    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) | (~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_65)),
% 0.21/0.47    inference(forward_demodulation,[],[f1176,f568])).
% 0.21/0.47  fof(f568,plain,(
% 0.21/0.47    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_65),
% 0.21/0.47    inference(avatar_component_clause,[],[f566])).
% 0.21/0.47  fof(f1176,plain,(
% 0.21/0.47    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) | (~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.21/0.47    inference(resolution,[],[f207,f133])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f131])).
% 0.21/0.47  % (22003)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(resolution,[],[f172,f63])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(forward_demodulation,[],[f171,f113])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(forward_demodulation,[],[f164,f113])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 0.21/0.47    inference(resolution,[],[f64,f98])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.47  fof(f631,plain,(
% 0.21/0.47    spl2_65 | ~spl2_2 | ~spl2_4 | ~spl2_6 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f630,f125,f111,f96,f85,f566])).
% 0.21/0.47  fof(f630,plain,(
% 0.21/0.47    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.21/0.47    inference(forward_demodulation,[],[f563,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f563,plain,(
% 0.21/0.47    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.21/0.47    inference(resolution,[],[f240,f127])).
% 0.21/0.47  fof(f478,plain,(
% 0.21/0.47    ~spl2_53 | spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f470,f125,f111,f96,f81,f475])).
% 0.21/0.47  fof(f470,plain,(
% 0.21/0.47    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f83,f127,f230])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(forward_demodulation,[],[f229,f113])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(forward_demodulation,[],[f228,f113])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | ~spl2_4),
% 0.21/0.47    inference(resolution,[],[f57,f98])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f43])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~v2_tops_1(sK1,sK0) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    spl2_9 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f129,f125,f131])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_8),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f127,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl2_8 | ~spl2_3 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f123,f111,f91,f125])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_3 | ~spl2_6)),
% 0.21/0.47    inference(backward_demodulation,[],[f93,f113])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f91])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl2_6 | ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f109,f103,f111])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl2_5 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_5),
% 0.21/0.47    inference(resolution,[],[f51,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f103])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    spl2_5 | ~spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f101,f96,f103])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl2_4),
% 0.21/0.47    inference(resolution,[],[f52,f98])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f44,f96])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f22])).
% 0.21/0.47  fof(f22,conjecture,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f91])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl2_1 | spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f46,f85,f81])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f85,f81])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (21996)------------------------------
% 0.21/0.47  % (21996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21996)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (21996)Memory used [KB]: 7419
% 0.21/0.47  % (21996)Time elapsed: 0.039 s
% 0.21/0.47  % (21996)------------------------------
% 0.21/0.47  % (21996)------------------------------
% 0.21/0.47  % (21987)Success in time 0.113 s
%------------------------------------------------------------------------------
