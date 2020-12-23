%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:12 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 245 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :    7
%              Number of atoms          :  324 ( 588 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1334,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f77,f82,f221,f664,f669,f717,f719,f1033,f1067,f1158,f1183,f1191,f1197,f1208,f1308,f1321,f1328,f1333])).

fof(f1333,plain,
    ( ~ spl3_47
    | ~ spl3_1
    | spl3_61 ),
    inference(avatar_split_clause,[],[f1330,f1325,f51,f1180])).

fof(f1180,plain,
    ( spl3_47
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f51,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1325,plain,
    ( spl3_61
  <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f1330,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_61 ),
    inference(resolution,[],[f1327,f183])).

fof(f183,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(k1_tops_1(X8,k4_xboole_0(X6,X7)),X7)
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(k4_xboole_0(X6,X7),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1327,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | spl3_61 ),
    inference(avatar_component_clause,[],[f1325])).

fof(f1328,plain,
    ( ~ spl3_61
    | spl3_60 ),
    inference(avatar_split_clause,[],[f1323,f1318,f1325])).

fof(f1318,plain,
    ( spl3_60
  <=> r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f1323,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | spl3_60 ),
    inference(resolution,[],[f1320,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1320,plain,
    ( ~ r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_60 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1321,plain,
    ( ~ spl3_60
    | ~ spl3_23
    | spl3_58 ),
    inference(avatar_split_clause,[],[f1310,f1305,f715,f1318])).

fof(f715,plain,
    ( spl3_23
  <=> ! [X0] :
        ( r1_xboole_0(k1_tops_1(sK0,sK2),X0)
        | ~ r1_xboole_0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1305,plain,
    ( spl3_58
  <=> r1_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f1310,plain,
    ( ~ r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_23
    | spl3_58 ),
    inference(resolution,[],[f1307,f716])).

fof(f716,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_tops_1(sK0,sK2),X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f715])).

fof(f1307,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_58 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f1308,plain,
    ( ~ spl3_58
    | spl3_44 ),
    inference(avatar_split_clause,[],[f1303,f1155,f1305])).

fof(f1155,plain,
    ( spl3_44
  <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1303,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_44 ),
    inference(resolution,[],[f1157,f35])).

fof(f1157,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f1155])).

fof(f1208,plain,
    ( ~ spl3_5
    | spl3_48 ),
    inference(avatar_split_clause,[],[f1206,f1194,f74])).

fof(f74,plain,
    ( spl3_5
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1194,plain,
    ( spl3_48
  <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f1206,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_48 ),
    inference(superposition,[],[f1202,f84])).

fof(f84,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(resolution,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1202,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK1,sK2),X0),u1_struct_0(sK0))
    | spl3_48 ),
    inference(resolution,[],[f1196,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1196,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f1194])).

fof(f1197,plain,
    ( ~ spl3_48
    | spl3_47 ),
    inference(avatar_split_clause,[],[f1192,f1180,f1194])).

fof(f1192,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_47 ),
    inference(resolution,[],[f1182,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1182,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f1191,plain,(
    spl3_46 ),
    inference(avatar_contradiction_clause,[],[f1185])).

fof(f1185,plain,
    ( $false
    | spl3_46 ),
    inference(unit_resulting_resolution,[],[f48,f1178,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1178,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl3_46 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f1176,plain,
    ( spl3_46
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1183,plain,
    ( ~ spl3_1
    | ~ spl3_46
    | ~ spl3_2
    | ~ spl3_47
    | spl3_43 ),
    inference(avatar_split_clause,[],[f1172,f1151,f1180,f56,f1176,f51])).

fof(f56,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1151,plain,
    ( spl3_43
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1172,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_43 ),
    inference(resolution,[],[f1153,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1153,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f1151])).

fof(f1158,plain,
    ( ~ spl3_43
    | ~ spl3_44
    | spl3_40 ),
    inference(avatar_split_clause,[],[f1147,f1064,f1155,f1151])).

fof(f1064,plain,
    ( spl3_40
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f1147,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_40 ),
    inference(resolution,[],[f1066,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f1066,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f1064])).

fof(f1067,plain,
    ( ~ spl3_40
    | spl3_13
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f1057,f1016,f218,f1064])).

fof(f218,plain,
    ( spl3_13
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1016,plain,
    ( spl3_36
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f1057,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_13
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f220,f1042])).

fof(f1042,plain,
    ( ! [X4] : k4_xboole_0(k1_tops_1(sK0,sK1),X4) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X4)
    | ~ spl3_36 ),
    inference(resolution,[],[f1017,f213])).

fof(f213,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3) ) ),
    inference(resolution,[],[f43,f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1017,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f1016])).

fof(f220,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f218])).

fof(f1033,plain,
    ( ~ spl3_5
    | ~ spl3_17
    | spl3_36 ),
    inference(avatar_split_clause,[],[f1031,f1016,f661,f74])).

fof(f661,plain,
    ( spl3_17
  <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1031,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_17
    | spl3_36 ),
    inference(superposition,[],[f1020,f663])).

fof(f663,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f661])).

fof(f1020,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))
    | spl3_36 ),
    inference(resolution,[],[f1018,f46])).

fof(f1018,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f1016])).

fof(f719,plain,
    ( ~ spl3_6
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f718])).

fof(f718,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f81,f713])).

fof(f713,plain,
    ( ! [X1] : ~ r1_tarski(sK2,X1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f712])).

fof(f712,plain,
    ( spl3_22
  <=> ! [X1] : ~ r1_tarski(sK2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f81,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_6
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f717,plain,
    ( spl3_22
    | spl3_23
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f708,f666,f715,f712])).

fof(f666,plain,
    ( spl3_18
  <=> sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f708,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tops_1(sK0,sK2),X0)
        | ~ r1_xboole_0(sK2,X0)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl3_18 ),
    inference(resolution,[],[f672,f47])).

fof(f672,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,k4_xboole_0(X0,X1))
        | r1_xboole_0(k1_tops_1(sK0,sK2),X1) )
    | ~ spl3_18 ),
    inference(superposition,[],[f104,f668])).

fof(f668,plain,
    ( sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f666])).

fof(f104,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),k4_xboole_0(X6,X7))
      | r1_xboole_0(X4,X7) ) ),
    inference(resolution,[],[f46,f45])).

fof(f669,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f658,f66,f51,f666])).

fof(f66,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f658,plain,
    ( sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f619,f68])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f619,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(k1_tops_1(sK0,X0),X0) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f182,f53])).

fof(f53,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f182,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | k2_xboole_0(k1_tops_1(X5,X4),X4) = X4 ) ),
    inference(resolution,[],[f32,f36])).

fof(f664,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f657,f56,f51,f661])).

fof(f657,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f619,f58])).

fof(f58,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f221,plain,
    ( ~ spl3_13
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f216,f61,f56,f218])).

fof(f61,plain,
    ( spl3_3
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f216,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ spl3_2
    | spl3_3 ),
    inference(backward_demodulation,[],[f63,f211])).

fof(f211,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_2 ),
    inference(resolution,[],[f43,f58])).

fof(f63,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f82,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f71,f66,f79])).

fof(f71,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f41,f68])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f70,f56,f74])).

fof(f70,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f58])).

fof(f69,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f64,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f51])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (5784)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.50  % (5777)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (5775)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (5797)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (5793)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (5776)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (5778)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (5798)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (5779)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (5782)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (5785)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (5780)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (5800)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (5790)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (5775)Refutation not found, incomplete strategy% (5775)------------------------------
% 0.22/0.53  % (5775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5775)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5775)Memory used [KB]: 10746
% 0.22/0.53  % (5775)Time elapsed: 0.117 s
% 0.22/0.53  % (5775)------------------------------
% 0.22/0.53  % (5775)------------------------------
% 0.22/0.53  % (5787)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (5781)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (5795)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (5788)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.35/0.54  % (5789)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.35/0.54  % (5799)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.35/0.54  % (5796)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.35/0.54  % (5794)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.35/0.55  % (5792)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.35/0.55  % (5786)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.35/0.55  % (5791)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.35/0.56  % (5788)Refutation not found, incomplete strategy% (5788)------------------------------
% 1.35/0.56  % (5788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (5788)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (5788)Memory used [KB]: 6268
% 1.35/0.56  % (5788)Time elapsed: 0.152 s
% 1.35/0.56  % (5788)------------------------------
% 1.35/0.56  % (5788)------------------------------
% 1.56/0.56  % (5784)Refutation not found, incomplete strategy% (5784)------------------------------
% 1.56/0.56  % (5784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (5784)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (5784)Memory used [KB]: 6140
% 1.56/0.56  % (5784)Time elapsed: 0.113 s
% 1.56/0.56  % (5784)------------------------------
% 1.56/0.56  % (5784)------------------------------
% 1.56/0.57  % (5783)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.56/0.61  % (5790)Refutation found. Thanks to Tanya!
% 1.56/0.61  % SZS status Theorem for theBenchmark
% 1.56/0.61  % SZS output start Proof for theBenchmark
% 1.56/0.61  fof(f1334,plain,(
% 1.56/0.61    $false),
% 1.56/0.61    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f77,f82,f221,f664,f669,f717,f719,f1033,f1067,f1158,f1183,f1191,f1197,f1208,f1308,f1321,f1328,f1333])).
% 1.56/0.61  fof(f1333,plain,(
% 1.56/0.61    ~spl3_47 | ~spl3_1 | spl3_61),
% 1.56/0.61    inference(avatar_split_clause,[],[f1330,f1325,f51,f1180])).
% 1.56/0.61  fof(f1180,plain,(
% 1.56/0.61    spl3_47 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.56/0.61  fof(f51,plain,(
% 1.56/0.61    spl3_1 <=> l1_pre_topc(sK0)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.56/0.61  fof(f1325,plain,(
% 1.56/0.61    spl3_61 <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 1.56/0.61  fof(f1330,plain,(
% 1.56/0.61    ~l1_pre_topc(sK0) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_61),
% 1.56/0.61    inference(resolution,[],[f1327,f183])).
% 1.56/0.61  fof(f183,plain,(
% 1.56/0.61    ( ! [X6,X8,X7] : (r1_xboole_0(k1_tops_1(X8,k4_xboole_0(X6,X7)),X7) | ~l1_pre_topc(X8) | ~m1_subset_1(k4_xboole_0(X6,X7),k1_zfmisc_1(u1_struct_0(X8)))) )),
% 1.56/0.61    inference(resolution,[],[f32,f45])).
% 1.56/0.61  fof(f45,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f24])).
% 1.56/0.61  fof(f24,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.56/0.61    inference(ennf_transformation,[],[f3])).
% 1.56/0.61  fof(f3,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.56/0.61  fof(f32,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f17])).
% 1.56/0.61  fof(f17,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.61    inference(ennf_transformation,[],[f11])).
% 1.56/0.61  fof(f11,axiom,(
% 1.56/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.56/0.61  fof(f1327,plain,(
% 1.56/0.61    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) | spl3_61),
% 1.56/0.61    inference(avatar_component_clause,[],[f1325])).
% 1.56/0.61  fof(f1328,plain,(
% 1.56/0.61    ~spl3_61 | spl3_60),
% 1.56/0.61    inference(avatar_split_clause,[],[f1323,f1318,f1325])).
% 1.56/0.61  fof(f1318,plain,(
% 1.56/0.61    spl3_60 <=> r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.56/0.61  fof(f1323,plain,(
% 1.56/0.61    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) | spl3_60),
% 1.56/0.61    inference(resolution,[],[f1320,f35])).
% 1.56/0.61  fof(f35,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f20])).
% 1.56/0.61  fof(f20,plain,(
% 1.56/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.56/0.61    inference(ennf_transformation,[],[f1])).
% 1.56/0.61  fof(f1,axiom,(
% 1.56/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.56/0.61  fof(f1320,plain,(
% 1.56/0.61    ~r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) | spl3_60),
% 1.56/0.61    inference(avatar_component_clause,[],[f1318])).
% 1.56/0.61  fof(f1321,plain,(
% 1.56/0.61    ~spl3_60 | ~spl3_23 | spl3_58),
% 1.56/0.61    inference(avatar_split_clause,[],[f1310,f1305,f715,f1318])).
% 1.56/0.61  fof(f715,plain,(
% 1.56/0.61    spl3_23 <=> ! [X0] : (r1_xboole_0(k1_tops_1(sK0,sK2),X0) | ~r1_xboole_0(sK2,X0))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.56/0.61  fof(f1305,plain,(
% 1.56/0.61    spl3_58 <=> r1_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_xboole_0(sK1,sK2)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 1.56/0.61  fof(f1310,plain,(
% 1.56/0.61    ~r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) | (~spl3_23 | spl3_58)),
% 1.56/0.61    inference(resolution,[],[f1307,f716])).
% 1.56/0.61  fof(f716,plain,(
% 1.56/0.61    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,sK2),X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl3_23),
% 1.56/0.61    inference(avatar_component_clause,[],[f715])).
% 1.56/0.61  fof(f1307,plain,(
% 1.56/0.61    ~r1_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) | spl3_58),
% 1.56/0.61    inference(avatar_component_clause,[],[f1305])).
% 1.56/0.61  fof(f1308,plain,(
% 1.56/0.61    ~spl3_58 | spl3_44),
% 1.56/0.61    inference(avatar_split_clause,[],[f1303,f1155,f1305])).
% 1.56/0.61  fof(f1155,plain,(
% 1.56/0.61    spl3_44 <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.56/0.61  fof(f1303,plain,(
% 1.56/0.61    ~r1_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) | spl3_44),
% 1.56/0.61    inference(resolution,[],[f1157,f35])).
% 1.56/0.61  fof(f1157,plain,(
% 1.56/0.61    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_44),
% 1.56/0.61    inference(avatar_component_clause,[],[f1155])).
% 1.56/0.61  fof(f1208,plain,(
% 1.56/0.61    ~spl3_5 | spl3_48),
% 1.56/0.61    inference(avatar_split_clause,[],[f1206,f1194,f74])).
% 1.56/0.61  fof(f74,plain,(
% 1.56/0.61    spl3_5 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.56/0.61  fof(f1194,plain,(
% 1.56/0.61    spl3_48 <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.56/0.61  fof(f1206,plain,(
% 1.56/0.61    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_48),
% 1.56/0.61    inference(superposition,[],[f1202,f84])).
% 1.56/0.61  fof(f84,plain,(
% 1.56/0.61    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1) )),
% 1.56/0.61    inference(resolution,[],[f36,f34])).
% 1.56/0.61  fof(f34,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f6])).
% 1.56/0.61  fof(f6,axiom,(
% 1.56/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.56/0.61  fof(f36,plain,(
% 1.56/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.56/0.61    inference(cnf_transformation,[],[f21])).
% 1.56/0.61  fof(f21,plain,(
% 1.56/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.56/0.61    inference(ennf_transformation,[],[f5])).
% 1.56/0.61  fof(f5,axiom,(
% 1.56/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.56/0.61  fof(f1202,plain,(
% 1.56/0.61    ( ! [X0] : (~r1_tarski(k2_xboole_0(k4_xboole_0(sK1,sK2),X0),u1_struct_0(sK0))) ) | spl3_48),
% 1.56/0.61    inference(resolution,[],[f1196,f46])).
% 1.56/0.61  fof(f46,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f25])).
% 1.56/0.61  fof(f25,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.56/0.61    inference(ennf_transformation,[],[f4])).
% 1.56/0.61  fof(f4,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.56/0.61  fof(f1196,plain,(
% 1.56/0.61    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_48),
% 1.56/0.61    inference(avatar_component_clause,[],[f1194])).
% 1.56/0.61  fof(f1197,plain,(
% 1.56/0.61    ~spl3_48 | spl3_47),
% 1.56/0.61    inference(avatar_split_clause,[],[f1192,f1180,f1194])).
% 1.56/0.61  fof(f1192,plain,(
% 1.56/0.61    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_47),
% 1.56/0.61    inference(resolution,[],[f1182,f40])).
% 1.56/0.61  fof(f40,plain,(
% 1.56/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f10])).
% 1.56/0.61  fof(f10,axiom,(
% 1.56/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.56/0.61  fof(f1182,plain,(
% 1.56/0.61    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_47),
% 1.56/0.61    inference(avatar_component_clause,[],[f1180])).
% 1.56/0.61  fof(f1191,plain,(
% 1.56/0.61    spl3_46),
% 1.56/0.61    inference(avatar_contradiction_clause,[],[f1185])).
% 1.56/0.61  fof(f1185,plain,(
% 1.56/0.61    $false | spl3_46),
% 1.56/0.61    inference(unit_resulting_resolution,[],[f48,f1178,f44])).
% 1.56/0.61  fof(f44,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f24])).
% 1.56/0.61  fof(f1178,plain,(
% 1.56/0.61    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | spl3_46),
% 1.56/0.61    inference(avatar_component_clause,[],[f1176])).
% 1.56/0.61  fof(f1176,plain,(
% 1.56/0.61    spl3_46 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.56/0.61  fof(f48,plain,(
% 1.56/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.61    inference(equality_resolution,[],[f38])).
% 1.56/0.61  fof(f38,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.61    inference(cnf_transformation,[],[f2])).
% 1.56/0.61  fof(f2,axiom,(
% 1.56/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.61  fof(f1183,plain,(
% 1.56/0.61    ~spl3_1 | ~spl3_46 | ~spl3_2 | ~spl3_47 | spl3_43),
% 1.56/0.61    inference(avatar_split_clause,[],[f1172,f1151,f1180,f56,f1176,f51])).
% 1.56/0.61  fof(f56,plain,(
% 1.56/0.61    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.56/0.61  fof(f1151,plain,(
% 1.56/0.61    spl3_43 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.56/0.61  fof(f1172,plain,(
% 1.56/0.61    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0) | spl3_43),
% 1.56/0.61    inference(resolution,[],[f1153,f33])).
% 1.56/0.61  fof(f33,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f19])).
% 1.56/0.61  fof(f19,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.61    inference(flattening,[],[f18])).
% 1.56/0.61  fof(f18,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.61    inference(ennf_transformation,[],[f12])).
% 1.56/0.61  fof(f12,axiom,(
% 1.56/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.56/0.61  fof(f1153,plain,(
% 1.56/0.61    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_43),
% 1.56/0.61    inference(avatar_component_clause,[],[f1151])).
% 1.56/0.61  fof(f1158,plain,(
% 1.56/0.61    ~spl3_43 | ~spl3_44 | spl3_40),
% 1.56/0.61    inference(avatar_split_clause,[],[f1147,f1064,f1155,f1151])).
% 1.56/0.61  fof(f1064,plain,(
% 1.56/0.61    spl3_40 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.56/0.61  fof(f1147,plain,(
% 1.56/0.61    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_40),
% 1.56/0.61    inference(resolution,[],[f1066,f47])).
% 1.56/0.61  fof(f47,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f27])).
% 1.56/0.61  fof(f27,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.56/0.61    inference(flattening,[],[f26])).
% 1.56/0.61  fof(f26,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.56/0.61    inference(ennf_transformation,[],[f8])).
% 1.56/0.61  fof(f8,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.56/0.61  fof(f1066,plain,(
% 1.56/0.61    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_40),
% 1.56/0.61    inference(avatar_component_clause,[],[f1064])).
% 1.56/0.61  fof(f1067,plain,(
% 1.56/0.61    ~spl3_40 | spl3_13 | ~spl3_36),
% 1.56/0.61    inference(avatar_split_clause,[],[f1057,f1016,f218,f1064])).
% 1.56/0.61  fof(f218,plain,(
% 1.56/0.61    spl3_13 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.56/0.61  fof(f1016,plain,(
% 1.56/0.61    spl3_36 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.56/0.61  fof(f1057,plain,(
% 1.56/0.61    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | (spl3_13 | ~spl3_36)),
% 1.56/0.61    inference(backward_demodulation,[],[f220,f1042])).
% 1.56/0.61  fof(f1042,plain,(
% 1.56/0.61    ( ! [X4] : (k4_xboole_0(k1_tops_1(sK0,sK1),X4) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X4)) ) | ~spl3_36),
% 1.56/0.61    inference(resolution,[],[f1017,f213])).
% 1.56/0.61  fof(f213,plain,(
% 1.56/0.61    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3)) )),
% 1.56/0.61    inference(resolution,[],[f43,f40])).
% 1.56/0.61  fof(f43,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f23])).
% 1.56/0.61  fof(f23,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.61    inference(ennf_transformation,[],[f9])).
% 1.56/0.61  fof(f9,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.56/0.61  fof(f1017,plain,(
% 1.56/0.61    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl3_36),
% 1.56/0.61    inference(avatar_component_clause,[],[f1016])).
% 1.56/0.61  fof(f220,plain,(
% 1.56/0.61    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_13),
% 1.56/0.61    inference(avatar_component_clause,[],[f218])).
% 1.56/0.61  fof(f1033,plain,(
% 1.56/0.61    ~spl3_5 | ~spl3_17 | spl3_36),
% 1.56/0.61    inference(avatar_split_clause,[],[f1031,f1016,f661,f74])).
% 1.56/0.61  fof(f661,plain,(
% 1.56/0.61    spl3_17 <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.56/0.61  fof(f1031,plain,(
% 1.56/0.61    ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl3_17 | spl3_36)),
% 1.56/0.61    inference(superposition,[],[f1020,f663])).
% 1.56/0.61  fof(f663,plain,(
% 1.56/0.61    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl3_17),
% 1.56/0.61    inference(avatar_component_clause,[],[f661])).
% 1.56/0.61  fof(f1020,plain,(
% 1.56/0.61    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))) ) | spl3_36),
% 1.56/0.61    inference(resolution,[],[f1018,f46])).
% 1.56/0.61  fof(f1018,plain,(
% 1.56/0.61    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_36),
% 1.56/0.61    inference(avatar_component_clause,[],[f1016])).
% 1.56/0.61  fof(f719,plain,(
% 1.56/0.61    ~spl3_6 | ~spl3_22),
% 1.56/0.61    inference(avatar_contradiction_clause,[],[f718])).
% 1.56/0.61  fof(f718,plain,(
% 1.56/0.61    $false | (~spl3_6 | ~spl3_22)),
% 1.56/0.61    inference(subsumption_resolution,[],[f81,f713])).
% 1.56/0.61  fof(f713,plain,(
% 1.56/0.61    ( ! [X1] : (~r1_tarski(sK2,X1)) ) | ~spl3_22),
% 1.56/0.61    inference(avatar_component_clause,[],[f712])).
% 1.56/0.61  fof(f712,plain,(
% 1.56/0.61    spl3_22 <=> ! [X1] : ~r1_tarski(sK2,X1)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.56/0.61  fof(f81,plain,(
% 1.56/0.61    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_6),
% 1.56/0.61    inference(avatar_component_clause,[],[f79])).
% 1.56/0.61  fof(f79,plain,(
% 1.56/0.61    spl3_6 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.56/0.61  fof(f717,plain,(
% 1.56/0.61    spl3_22 | spl3_23 | ~spl3_18),
% 1.56/0.61    inference(avatar_split_clause,[],[f708,f666,f715,f712])).
% 1.56/0.61  fof(f666,plain,(
% 1.56/0.61    spl3_18 <=> sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.56/0.61  fof(f708,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(sK0,sK2),X0) | ~r1_xboole_0(sK2,X0) | ~r1_tarski(sK2,X1)) ) | ~spl3_18),
% 1.56/0.61    inference(resolution,[],[f672,f47])).
% 1.56/0.61  fof(f672,plain,(
% 1.56/0.61    ( ! [X0,X1] : (~r1_tarski(sK2,k4_xboole_0(X0,X1)) | r1_xboole_0(k1_tops_1(sK0,sK2),X1)) ) | ~spl3_18),
% 1.56/0.61    inference(superposition,[],[f104,f668])).
% 1.56/0.61  fof(f668,plain,(
% 1.56/0.61    sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2) | ~spl3_18),
% 1.56/0.61    inference(avatar_component_clause,[],[f666])).
% 1.56/0.61  fof(f104,plain,(
% 1.56/0.61    ( ! [X6,X4,X7,X5] : (~r1_tarski(k2_xboole_0(X4,X5),k4_xboole_0(X6,X7)) | r1_xboole_0(X4,X7)) )),
% 1.56/0.61    inference(resolution,[],[f46,f45])).
% 1.56/0.61  fof(f669,plain,(
% 1.56/0.61    spl3_18 | ~spl3_1 | ~spl3_4),
% 1.56/0.61    inference(avatar_split_clause,[],[f658,f66,f51,f666])).
% 1.56/0.61  fof(f66,plain,(
% 1.56/0.61    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.56/0.61  fof(f658,plain,(
% 1.56/0.61    sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2) | (~spl3_1 | ~spl3_4)),
% 1.56/0.61    inference(resolution,[],[f619,f68])).
% 1.56/0.61  fof(f68,plain,(
% 1.56/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 1.56/0.61    inference(avatar_component_clause,[],[f66])).
% 1.56/0.61  fof(f619,plain,(
% 1.56/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(k1_tops_1(sK0,X0),X0) = X0) ) | ~spl3_1),
% 1.56/0.61    inference(resolution,[],[f182,f53])).
% 1.56/0.61  fof(f53,plain,(
% 1.56/0.61    l1_pre_topc(sK0) | ~spl3_1),
% 1.56/0.61    inference(avatar_component_clause,[],[f51])).
% 1.56/0.61  fof(f182,plain,(
% 1.56/0.61    ( ! [X4,X5] : (~l1_pre_topc(X5) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | k2_xboole_0(k1_tops_1(X5,X4),X4) = X4) )),
% 1.56/0.61    inference(resolution,[],[f32,f36])).
% 1.56/0.61  fof(f664,plain,(
% 1.56/0.61    spl3_17 | ~spl3_1 | ~spl3_2),
% 1.56/0.61    inference(avatar_split_clause,[],[f657,f56,f51,f661])).
% 1.56/0.61  fof(f657,plain,(
% 1.56/0.61    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | (~spl3_1 | ~spl3_2)),
% 1.56/0.61    inference(resolution,[],[f619,f58])).
% 1.56/0.61  fof(f58,plain,(
% 1.56/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 1.56/0.61    inference(avatar_component_clause,[],[f56])).
% 1.56/0.61  fof(f221,plain,(
% 1.56/0.61    ~spl3_13 | ~spl3_2 | spl3_3),
% 1.56/0.61    inference(avatar_split_clause,[],[f216,f61,f56,f218])).
% 1.56/0.61  fof(f61,plain,(
% 1.56/0.61    spl3_3 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.56/0.61  fof(f216,plain,(
% 1.56/0.61    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | (~spl3_2 | spl3_3)),
% 1.56/0.61    inference(backward_demodulation,[],[f63,f211])).
% 1.56/0.61  fof(f211,plain,(
% 1.56/0.61    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_2),
% 1.56/0.61    inference(resolution,[],[f43,f58])).
% 1.56/0.61  fof(f63,plain,(
% 1.56/0.61    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_3),
% 1.56/0.61    inference(avatar_component_clause,[],[f61])).
% 1.56/0.61  fof(f82,plain,(
% 1.56/0.61    spl3_6 | ~spl3_4),
% 1.56/0.61    inference(avatar_split_clause,[],[f71,f66,f79])).
% 1.56/0.61  fof(f71,plain,(
% 1.56/0.61    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_4),
% 1.56/0.61    inference(resolution,[],[f41,f68])).
% 1.56/0.61  fof(f41,plain,(
% 1.56/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f10])).
% 1.56/0.61  fof(f77,plain,(
% 1.56/0.61    spl3_5 | ~spl3_2),
% 1.56/0.61    inference(avatar_split_clause,[],[f70,f56,f74])).
% 1.56/0.61  fof(f70,plain,(
% 1.56/0.61    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 1.56/0.61    inference(resolution,[],[f41,f58])).
% 1.56/0.61  fof(f69,plain,(
% 1.56/0.61    spl3_4),
% 1.56/0.61    inference(avatar_split_clause,[],[f28,f66])).
% 1.56/0.61  fof(f28,plain,(
% 1.56/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.61    inference(cnf_transformation,[],[f16])).
% 1.56/0.61  fof(f16,plain,(
% 1.56/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.56/0.61    inference(ennf_transformation,[],[f15])).
% 1.56/0.61  fof(f15,plain,(
% 1.56/0.61    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.56/0.61    inference(pure_predicate_removal,[],[f14])).
% 1.56/0.61  fof(f14,negated_conjecture,(
% 1.56/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.56/0.61    inference(negated_conjecture,[],[f13])).
% 1.56/0.61  fof(f13,conjecture,(
% 1.56/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.56/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 1.56/0.61  fof(f64,plain,(
% 1.56/0.61    ~spl3_3),
% 1.56/0.61    inference(avatar_split_clause,[],[f29,f61])).
% 1.56/0.61  fof(f29,plain,(
% 1.56/0.61    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.56/0.61    inference(cnf_transformation,[],[f16])).
% 1.56/0.61  fof(f59,plain,(
% 1.56/0.61    spl3_2),
% 1.56/0.61    inference(avatar_split_clause,[],[f30,f56])).
% 1.56/0.61  fof(f30,plain,(
% 1.56/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.61    inference(cnf_transformation,[],[f16])).
% 1.56/0.61  fof(f54,plain,(
% 1.56/0.61    spl3_1),
% 1.56/0.61    inference(avatar_split_clause,[],[f31,f51])).
% 1.56/0.61  fof(f31,plain,(
% 1.56/0.61    l1_pre_topc(sK0)),
% 1.56/0.61    inference(cnf_transformation,[],[f16])).
% 1.56/0.61  % SZS output end Proof for theBenchmark
% 1.56/0.61  % (5790)------------------------------
% 1.56/0.61  % (5790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (5790)Termination reason: Refutation
% 1.56/0.61  
% 1.56/0.61  % (5790)Memory used [KB]: 7164
% 1.56/0.61  % (5790)Time elapsed: 0.212 s
% 1.56/0.61  % (5790)------------------------------
% 1.56/0.61  % (5790)------------------------------
% 1.56/0.61  % (5773)Success in time 0.252 s
%------------------------------------------------------------------------------
