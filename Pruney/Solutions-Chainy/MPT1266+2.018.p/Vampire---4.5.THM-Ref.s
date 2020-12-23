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
% DateTime   : Thu Dec  3 13:12:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 (1193 expanded)
%              Number of leaves         :   26 ( 351 expanded)
%              Depth                    :   21
%              Number of atoms          :  390 (4547 expanded)
%              Number of equality atoms :   86 (1372 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f91,f93,f422,f573,f966,f968,f985,f1006,f1276,f1297,f1306])).

fof(f1306,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1305])).

fof(f1305,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f68,f61])).

fof(f61,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f68,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f38,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f38,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f1297,plain,
    ( spl2_2
    | ~ spl2_55
    | ~ spl2_61 ),
    inference(avatar_contradiction_clause,[],[f1296])).

fof(f1296,plain,
    ( $false
    | spl2_2
    | ~ spl2_55
    | ~ spl2_61 ),
    inference(trivial_inequality_removal,[],[f1295])).

fof(f1295,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_2
    | ~ spl2_55
    | ~ spl2_61 ),
    inference(superposition,[],[f64,f1285])).

fof(f1285,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_55
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f1278,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f72,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f55,f41])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f72,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f42,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1278,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_55
    | ~ spl2_61 ),
    inference(backward_demodulation,[],[f1029,f1275])).

fof(f1275,plain,
    ( k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f1273,plain,
    ( spl2_61
  <=> k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f1029,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_55 ),
    inference(backward_demodulation,[],[f1017,f1018])).

fof(f1018,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_55 ),
    inference(resolution,[],[f1005,f52])).

fof(f1005,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1003,plain,
    ( spl2_55
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f1017,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_55 ),
    inference(resolution,[],[f1005,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f64,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f1276,plain,
    ( ~ spl2_54
    | ~ spl2_4
    | spl2_61
    | ~ spl2_4
    | ~ spl2_23
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f1271,f1003,f570,f88,f1273,f88,f963])).

fof(f963,plain,
    ( spl2_54
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f88,plain,
    ( spl2_4
  <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f570,plain,
    ( spl2_23
  <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1271,plain,
    ( k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_23
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f987,f1261])).

fof(f1261,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f1260,f1018])).

fof(f1260,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f201,f1257])).

fof(f1257,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f183,f890])).

fof(f890,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f864,f73])).

fof(f73,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f69])).

fof(f69,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f43,f56])).

fof(f56,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f864,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f844,f70])).

fof(f844,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ) ),
    inference(forward_demodulation,[],[f843,f69])).

fof(f843,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f842,f69])).

fof(f842,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f45,f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f183,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_4 ),
    inference(resolution,[],[f113,f90])).

fof(f90,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f113,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) ) ),
    inference(resolution,[],[f111,f52])).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f110,f69])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f109,f69])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f54,f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f201,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))))
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f116,f183])).

fof(f116,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))))
    | ~ spl2_4 ),
    inference(resolution,[],[f112,f90])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) ) ),
    inference(resolution,[],[f111,f53])).

fof(f987,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f986,f69])).

fof(f986,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_23 ),
    inference(resolution,[],[f571,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f571,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f570])).

fof(f1006,plain,
    ( ~ spl2_15
    | spl2_55 ),
    inference(avatar_split_clause,[],[f989,f1003,f412])).

fof(f412,plain,
    ( spl2_15
  <=> m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f989,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f51,f890])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f985,plain,
    ( ~ spl2_54
    | spl2_23
    | ~ spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f972,f59,f84,f570,f963])).

fof(f84,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f972,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f971,f69])).

fof(f971,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f970,f73])).

fof(f970,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f969,f69])).

fof(f969,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f61,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f968,plain,(
    spl2_54 ),
    inference(avatar_contradiction_clause,[],[f967])).

fof(f967,plain,
    ( $false
    | spl2_54 ),
    inference(resolution,[],[f965,f35])).

fof(f965,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_54 ),
    inference(avatar_component_clause,[],[f963])).

fof(f966,plain,
    ( ~ spl2_54
    | spl2_23
    | ~ spl2_4
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f916,f88,f63,f88,f570,f963])).

fof(f916,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f914,f69])).

fof(f914,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f913])).

fof(f913,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f47,f903])).

fof(f903,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f901,f81])).

fof(f81,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f79,f41])).

fof(f79,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f78,f52])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f76,f57])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f51,f75])).

fof(f901,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f201,f895])).

fof(f895,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f183,f891])).

fof(f891,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f890,f65])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f573,plain,
    ( spl2_1
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f550,f570,f59])).

fof(f550,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f532,f73])).

fof(f532,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f512,f70])).

fof(f512,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | v2_tops_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f511,f69])).

fof(f511,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f510,f69])).

fof(f510,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f422,plain,
    ( ~ spl2_4
    | spl2_15 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | ~ spl2_4
    | spl2_15 ),
    inference(resolution,[],[f420,f90])).

fof(f420,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_15 ),
    inference(resolution,[],[f414,f111])).

fof(f414,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f412])).

fof(f93,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f86,f70])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f91,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f77,f88,f84])).

fof(f77,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f51,f73])).

fof(f66,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f37,f63,f59])).

fof(f37,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:40:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22842)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (22843)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (22855)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (22844)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (22847)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (22841)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (22851)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (22850)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (22845)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (22840)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (22849)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (22848)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (22842)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f1307,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f66,f91,f93,f422,f573,f966,f968,f985,f1006,f1276,f1297,f1306])).
% 0.22/0.50  fof(f1306,plain,(
% 0.22/0.50    ~spl2_1 | ~spl2_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1305])).
% 0.22/0.50  fof(f1305,plain,(
% 0.22/0.50    $false | (~spl2_1 | ~spl2_2)),
% 0.22/0.50    inference(resolution,[],[f68,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ~v2_tops_1(sK1,sK0) | ~spl2_2),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | ~v2_tops_1(sK1,sK0) | ~spl2_2),
% 0.22/0.50    inference(forward_demodulation,[],[f38,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.50    inference(negated_conjecture,[],[f15])).
% 0.22/0.50  fof(f15,conjecture,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.22/0.50  fof(f1297,plain,(
% 0.22/0.50    spl2_2 | ~spl2_55 | ~spl2_61),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1296])).
% 0.22/0.50  fof(f1296,plain,(
% 0.22/0.50    $false | (spl2_2 | ~spl2_55 | ~spl2_61)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f1295])).
% 0.22/0.50  fof(f1295,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | (spl2_2 | ~spl2_55 | ~spl2_61)),
% 0.22/0.50    inference(superposition,[],[f64,f1285])).
% 0.22/0.50  fof(f1285,plain,(
% 0.22/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_55 | ~spl2_61)),
% 0.22/0.50    inference(forward_demodulation,[],[f1278,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f72,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f55,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f40,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f52,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f42,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.50  fof(f1278,plain,(
% 0.22/0.50    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_55 | ~spl2_61)),
% 0.22/0.50    inference(backward_demodulation,[],[f1029,f1275])).
% 0.22/0.50  fof(f1275,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_61),
% 0.22/0.50    inference(avatar_component_clause,[],[f1273])).
% 0.22/0.50  fof(f1273,plain,(
% 0.22/0.50    spl2_61 <=> k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 0.22/0.50  fof(f1029,plain,(
% 0.22/0.50    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_55),
% 0.22/0.50    inference(backward_demodulation,[],[f1017,f1018])).
% 0.22/0.50  fof(f1018,plain,(
% 0.22/0.50    k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_55),
% 0.22/0.50    inference(resolution,[],[f1005,f52])).
% 0.22/0.50  fof(f1005,plain,(
% 0.22/0.50    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_55),
% 0.22/0.50    inference(avatar_component_clause,[],[f1003])).
% 0.22/0.50  fof(f1003,plain,(
% 0.22/0.50    spl2_55 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.22/0.50  fof(f1017,plain,(
% 0.22/0.50    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_55),
% 0.22/0.50    inference(resolution,[],[f1005,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f1276,plain,(
% 0.22/0.50    ~spl2_54 | ~spl2_4 | spl2_61 | ~spl2_4 | ~spl2_23 | ~spl2_55),
% 0.22/0.50    inference(avatar_split_clause,[],[f1271,f1003,f570,f88,f1273,f88,f963])).
% 0.22/0.50  fof(f963,plain,(
% 0.22/0.50    spl2_54 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl2_4 <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f570,plain,(
% 0.22/0.50    spl2_23 <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.50  fof(f1271,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_23 | ~spl2_55)),
% 0.22/0.50    inference(forward_demodulation,[],[f987,f1261])).
% 0.22/0.50  fof(f1261,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_55)),
% 0.22/0.50    inference(forward_demodulation,[],[f1260,f1018])).
% 0.22/0.50  fof(f1260,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_4),
% 0.22/0.50    inference(forward_demodulation,[],[f201,f1257])).
% 0.22/0.50  fof(f1257,plain,(
% 0.22/0.50    k1_tops_1(sK0,sK1) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_4),
% 0.22/0.50    inference(forward_demodulation,[],[f183,f890])).
% 0.22/0.50  fof(f890,plain,(
% 0.22/0.50    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 0.22/0.50    inference(forward_demodulation,[],[f864,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)),
% 0.22/0.50    inference(resolution,[],[f52,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(backward_demodulation,[],[f36,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f43,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f44,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f864,plain,(
% 0.22/0.50    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.22/0.50    inference(resolution,[],[f844,f70])).
% 0.22/0.50  fof(f844,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f843,f69])).
% 0.22/0.50  fof(f843,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f842,f69])).
% 0.22/0.50  fof(f842,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 0.22/0.50    inference(resolution,[],[f45,f35])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f113,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X1))) )),
% 0.22/0.50    inference(resolution,[],[f111,f52])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f110,f69])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f109,f69])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.50    inference(resolution,[],[f54,f35])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) | ~spl2_4),
% 0.22/0.50    inference(backward_demodulation,[],[f116,f183])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f112,f90])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)))) )),
% 0.22/0.50    inference(resolution,[],[f111,f53])).
% 0.22/0.50  fof(f987,plain,(
% 0.22/0.50    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~spl2_23),
% 0.22/0.50    inference(forward_demodulation,[],[f986,f69])).
% 0.22/0.50  fof(f986,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_23),
% 0.22/0.50    inference(resolution,[],[f571,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.50  fof(f571,plain,(
% 0.22/0.50    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f570])).
% 0.22/0.50  fof(f1006,plain,(
% 0.22/0.50    ~spl2_15 | spl2_55),
% 0.22/0.50    inference(avatar_split_clause,[],[f989,f1003,f412])).
% 0.22/0.50  fof(f412,plain,(
% 0.22/0.50    spl2_15 <=> m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.50  fof(f989,plain,(
% 0.22/0.50    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(superposition,[],[f51,f890])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.50  fof(f985,plain,(
% 0.22/0.50    ~spl2_54 | spl2_23 | ~spl2_3 | ~spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f972,f59,f84,f570,f963])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f972,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.22/0.50    inference(forward_demodulation,[],[f971,f69])).
% 0.22/0.50  fof(f971,plain,(
% 0.22/0.50    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.22/0.50    inference(forward_demodulation,[],[f970,f73])).
% 0.22/0.50  fof(f970,plain,(
% 0.22/0.50    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.22/0.50    inference(forward_demodulation,[],[f969,f69])).
% 0.22/0.50  fof(f969,plain,(
% 0.22/0.50    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.22/0.50    inference(resolution,[],[f61,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 0.22/0.50  fof(f968,plain,(
% 0.22/0.50    spl2_54),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f967])).
% 0.22/0.50  fof(f967,plain,(
% 0.22/0.50    $false | spl2_54),
% 0.22/0.50    inference(resolution,[],[f965,f35])).
% 0.22/0.50  fof(f965,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | spl2_54),
% 0.22/0.50    inference(avatar_component_clause,[],[f963])).
% 0.22/0.50  fof(f966,plain,(
% 0.22/0.50    ~spl2_54 | spl2_23 | ~spl2_4 | ~spl2_2 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f916,f88,f63,f88,f570,f963])).
% 0.22/0.50  fof(f916,plain,(
% 0.22/0.50    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_4)),
% 0.22/0.50    inference(forward_demodulation,[],[f914,f69])).
% 0.22/0.50  fof(f914,plain,(
% 0.22/0.50    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_4)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f913])).
% 0.22/0.50  fof(f913,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_4)),
% 0.22/0.50    inference(superposition,[],[f47,f903])).
% 0.22/0.50  fof(f903,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_4)),
% 0.22/0.50    inference(forward_demodulation,[],[f901,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(forward_demodulation,[],[f79,f41])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f78,f52])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(resolution,[],[f76,f57])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(X0)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(superposition,[],[f51,f75])).
% 0.22/0.50  fof(f901,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) | (~spl2_2 | ~spl2_4)),
% 0.22/0.50    inference(backward_demodulation,[],[f201,f895])).
% 0.22/0.50  fof(f895,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_4)),
% 0.22/0.50    inference(backward_demodulation,[],[f183,f891])).
% 0.22/0.50  fof(f891,plain,(
% 0.22/0.50    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_2),
% 0.22/0.50    inference(forward_demodulation,[],[f890,f65])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f573,plain,(
% 0.22/0.50    spl2_1 | ~spl2_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f550,f570,f59])).
% 0.22/0.50  fof(f550,plain,(
% 0.22/0.50    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v2_tops_1(sK1,sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f532,f73])).
% 0.22/0.50  fof(f532,plain,(
% 0.22/0.50    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v2_tops_1(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f512,f70])).
% 0.22/0.50  fof(f512,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v2_tops_1(X0,sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f511,f69])).
% 0.22/0.50  fof(f511,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f510,f69])).
% 0.22/0.50  fof(f510,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 0.22/0.50    inference(resolution,[],[f49,f35])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f422,plain,(
% 0.22/0.50    ~spl2_4 | spl2_15),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f421])).
% 0.22/0.50  fof(f421,plain,(
% 0.22/0.50    $false | (~spl2_4 | spl2_15)),
% 0.22/0.50    inference(resolution,[],[f420,f90])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_15),
% 0.22/0.50    inference(resolution,[],[f414,f111])).
% 0.22/0.50  fof(f414,plain,(
% 0.22/0.50    ~m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f412])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl2_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    $false | spl2_3),
% 0.22/0.50    inference(resolution,[],[f86,f70])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f84])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~spl2_3 | spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f77,f88,f84])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(superposition,[],[f51,f73])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl2_1 | spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f63,f59])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (22842)------------------------------
% 0.22/0.50  % (22842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22842)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (22842)Memory used [KB]: 6652
% 0.22/0.50  % (22842)Time elapsed: 0.070 s
% 0.22/0.50  % (22842)------------------------------
% 0.22/0.50  % (22842)------------------------------
% 0.22/0.50  % (22846)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (22852)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (22853)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (22857)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (22839)Success in time 0.153 s
%------------------------------------------------------------------------------
