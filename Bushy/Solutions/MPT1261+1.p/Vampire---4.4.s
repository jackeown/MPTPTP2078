%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t77_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:32 EDT 2019

% Result     : Theorem 2.77s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  382 (1025 expanded)
%              Number of leaves         :  100 ( 444 expanded)
%              Depth                    :    9
%              Number of atoms          : 1108 (2849 expanded)
%              Number of equality atoms :  237 ( 591 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f164,f165,f172,f179,f186,f229,f237,f245,f254,f262,f272,f279,f286,f289,f291,f355,f360,f393,f402,f411,f420,f432,f433,f441,f471,f479,f487,f501,f504,f512,f519,f588,f593,f626,f635,f644,f653,f682,f691,f698,f706,f775,f776,f875,f906,f914,f922,f930,f944,f947,f955,f962,f989,f1001,f1016,f1024,f1033,f1084,f1116,f1123,f1131,f1139,f1147,f1161,f1164,f1172,f1179,f1219,f1234,f1235,f1236,f1237])).

fof(f1237,plain,
    ( spl4_130
    | ~ spl4_128 ),
    inference(avatar_split_clause,[],[f1225,f1217,f1232])).

fof(f1232,plain,
    ( spl4_130
  <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f1217,plain,
    ( spl4_128
  <=> k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f1225,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ spl4_128 ),
    inference(superposition,[],[f141,f1218])).

fof(f1218,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1
    | ~ spl4_128 ),
    inference(avatar_component_clause,[],[f1217])).

fof(f141,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',commutativity_k2_xboole_0)).

fof(f1236,plain,
    ( spl4_130
    | ~ spl4_128 ),
    inference(avatar_split_clause,[],[f1224,f1217,f1232])).

fof(f1224,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ spl4_128 ),
    inference(superposition,[],[f141,f1218])).

fof(f1235,plain,
    ( spl4_130
    | ~ spl4_128 ),
    inference(avatar_split_clause,[],[f1223,f1217,f1232])).

fof(f1223,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ spl4_128 ),
    inference(superposition,[],[f1218,f141])).

fof(f1234,plain,
    ( spl4_130
    | ~ spl4_128 ),
    inference(avatar_split_clause,[],[f1222,f1217,f1232])).

fof(f1222,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ spl4_128 ),
    inference(superposition,[],[f1218,f141])).

fof(f1219,plain,
    ( spl4_128
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f1212,f430,f1217])).

fof(f430,plain,
    ( spl4_40
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1212,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f1197,f131])).

fof(f131,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',t3_boole)).

fof(f1197,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_40 ),
    inference(superposition,[],[f523,f145])).

fof(f145,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',t2_boole)).

fof(f523,plain,
    ( ! [X1] : k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,X1)) = k4_xboole_0(sK1,k3_xboole_0(k1_tops_1(sK0,sK1),X1))
    | ~ spl4_40 ),
    inference(superposition,[],[f129,f431])).

fof(f431,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f430])).

fof(f129,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',t54_xboole_1)).

fof(f1179,plain,
    ( spl4_126
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1107,f1082,f1177])).

fof(f1177,plain,
    ( spl4_126
  <=> k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f1082,plain,
    ( spl4_108
  <=> m1_subset_1(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f1107,plain,
    ( k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_subset_1(X1,X0,X0) = X0 ) ),
    inference(condensation,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',idempotence_k4_subset_1)).

fof(f1083,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1172,plain,
    ( spl4_124
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1165,f1082,f177,f1170])).

fof(f1170,plain,
    ( spl4_124
  <=> k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f177,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1165,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(subsumption_resolution,[],[f1095,f178])).

fof(f178,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1095,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',projectivity_k2_pre_topc)).

fof(f1164,plain,
    ( ~ spl4_123
    | spl4_120
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1163,f1082,f184,f177,f1150,f1156])).

fof(f1156,plain,
    ( spl4_123
  <=> k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) != k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).

fof(f1150,plain,
    ( spl4_120
  <=> v4_pre_topc(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f184,plain,
    ( spl4_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1163,plain,
    ( v4_pre_topc(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) != k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_108 ),
    inference(subsumption_resolution,[],[f1162,f178])).

fof(f1162,plain,
    ( v4_pre_topc(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) != k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_8
    | ~ spl4_108 ),
    inference(subsumption_resolution,[],[f1094,f185])).

fof(f185,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f1094,plain,
    ( v4_pre_topc(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) != k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',t52_pre_topc)).

fof(f1161,plain,
    ( ~ spl4_121
    | spl4_122
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1148,f1082,f177,f1159,f1153])).

fof(f1153,plain,
    ( spl4_121
  <=> ~ v4_pre_topc(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).

fof(f1159,plain,
    ( spl4_122
  <=> k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f1148,plain,
    ( k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v4_pre_topc(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(subsumption_resolution,[],[f1093,f178])).

fof(f1093,plain,
    ( k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ v4_pre_topc(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f1147,plain,
    ( spl4_118
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1140,f1082,f177,f1145])).

fof(f1145,plain,
    ( spl4_118
  <=> k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k2_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f1140,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k2_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(subsumption_resolution,[],[f1091,f178])).

fof(f1091,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k2_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',t65_tops_1)).

fof(f1139,plain,
    ( spl4_116
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1132,f1082,f177,f1137])).

fof(f1137,plain,
    ( spl4_116
  <=> k2_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f1132,plain,
    ( k2_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(subsumption_resolution,[],[f1090,f178])).

fof(f1090,plain,
    ( k2_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))),k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',l78_tops_1)).

fof(f1131,plain,
    ( spl4_114
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1124,f1082,f177,f1129])).

fof(f1129,plain,
    ( spl4_114
  <=> k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f1124,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl4_6
    | ~ spl4_108 ),
    inference(subsumption_resolution,[],[f1087,f178])).

fof(f1087,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',projectivity_k1_tops_1)).

fof(f1123,plain,
    ( spl4_112
    | ~ spl4_4
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1086,f1082,f170,f1121])).

fof(f1121,plain,
    ( spl4_112
  <=> k2_xboole_0(sK1,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f170,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1086,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_4
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f214])).

fof(f214,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(sK1,X4) = k4_subset_1(u1_struct_0(sK0),sK1,X4) )
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',redefinition_k4_subset_1)).

fof(f171,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f170])).

fof(f1116,plain,
    ( spl4_110
    | ~ spl4_4
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1109,f1082,f170,f1114])).

fof(f1114,plain,
    ( spl4_110
  <=> k2_xboole_0(sK1,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f1109,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK1)
    | ~ spl4_4
    | ~ spl4_108 ),
    inference(forward_demodulation,[],[f1085,f141])).

fof(f1085,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK1) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK1)
    | ~ spl4_4
    | ~ spl4_108 ),
    inference(resolution,[],[f1083,f215])).

fof(f215,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(X5,sK1) = k4_subset_1(u1_struct_0(sK0),X5,sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f135])).

fof(f1084,plain,
    ( spl4_108
    | ~ spl4_4
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f1077,f704,f170,f1082])).

fof(f704,plain,
    ( spl4_76
  <=> k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f1077,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_76 ),
    inference(subsumption_resolution,[],[f1076,f171])).

fof(f1076,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_76 ),
    inference(subsumption_resolution,[],[f1075,f127])).

fof(f127,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',existence_m1_subset_1)).

fof(f1075,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_76 ),
    inference(superposition,[],[f136,f705])).

fof(f705,plain,
    ( k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f704])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',dt_k4_subset_1)).

fof(f1033,plain,
    ( spl4_106
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1026,f170,f1031])).

fof(f1031,plain,
    ( spl4_106
  <=> k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f1026,plain,
    ( k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f978,f141])).

fof(f978,plain,
    ( k2_xboole_0(sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK1) = k4_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f215,f127])).

fof(f1024,plain,
    ( spl4_104
    | ~ spl4_4
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f1017,f577,f170,f1022])).

fof(f1022,plain,
    ( spl4_104
  <=> k2_xboole_0(sK1,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f577,plain,
    ( spl4_58
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f1017,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK1)
    | ~ spl4_4
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f976,f141])).

fof(f976,plain,
    ( k2_xboole_0(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK1) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK1)
    | ~ spl4_4
    | ~ spl4_58 ),
    inference(resolution,[],[f215,f578])).

fof(f578,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f577])).

fof(f1016,plain,
    ( spl4_102
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f1009,f344,f170,f1014])).

fof(f1014,plain,
    ( spl4_102
  <=> k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f344,plain,
    ( spl4_28
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1009,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f975,f141])).

fof(f975,plain,
    ( k2_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(resolution,[],[f215,f345])).

fof(f345,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f344])).

fof(f1001,plain,
    ( spl4_100
    | ~ spl4_4
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f994,f873,f170,f999])).

fof(f999,plain,
    ( spl4_100
  <=> k2_xboole_0(sK1,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f873,plain,
    ( spl4_80
  <=> m1_subset_1(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f994,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_4
    | ~ spl4_80 ),
    inference(forward_demodulation,[],[f968,f141])).

fof(f968,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK1) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_4
    | ~ spl4_80 ),
    inference(resolution,[],[f215,f874])).

fof(f874,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f873])).

fof(f989,plain,
    ( spl4_98
    | ~ spl4_4
    | ~ spl4_42
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f982,f680,f439,f170,f987])).

fof(f987,plain,
    ( spl4_98
  <=> k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f439,plain,
    ( spl4_42
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f680,plain,
    ( spl4_70
  <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f982,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_42
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f981,f681])).

fof(f681,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f680])).

fof(f981,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl4_4
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f964,f141])).

fof(f964,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl4_4
    | ~ spl4_42 ),
    inference(resolution,[],[f215,f440])).

fof(f440,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f439])).

fof(f962,plain,
    ( spl4_96
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f897,f873,f960])).

fof(f960,plain,
    ( spl4_96
  <=> k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f897,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl4_80 ),
    inference(resolution,[],[f874,f151])).

fof(f955,plain,
    ( spl4_94
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f948,f873,f177,f953])).

fof(f953,plain,
    ( spl4_94
  <=> k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f948,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f885,f178])).

fof(f885,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_80 ),
    inference(resolution,[],[f874,f132])).

fof(f947,plain,
    ( ~ spl4_93
    | spl4_90
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f946,f873,f184,f177,f933,f939])).

fof(f939,plain,
    ( spl4_93
  <=> k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) != k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f933,plain,
    ( spl4_90
  <=> v4_pre_topc(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f946,plain,
    ( v4_pre_topc(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK0)
    | k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) != k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f945,f178])).

fof(f945,plain,
    ( v4_pre_topc(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK0)
    | k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) != k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_8
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f884,f185])).

fof(f884,plain,
    ( v4_pre_topc(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK0)
    | k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) != k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_80 ),
    inference(resolution,[],[f874,f126])).

fof(f944,plain,
    ( ~ spl4_91
    | spl4_92
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f931,f873,f177,f942,f936])).

fof(f936,plain,
    ( spl4_91
  <=> ~ v4_pre_topc(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f942,plain,
    ( spl4_92
  <=> k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f931,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ v4_pre_topc(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK0)
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f883,f178])).

fof(f883,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ v4_pre_topc(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_80 ),
    inference(resolution,[],[f874,f125])).

fof(f930,plain,
    ( spl4_88
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f923,f873,f177,f928])).

fof(f928,plain,
    ( spl4_88
  <=> k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))) = k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f923,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))) = k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f881,f178])).

fof(f881,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))) = k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_80 ),
    inference(resolution,[],[f874,f123])).

fof(f922,plain,
    ( spl4_86
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f915,f873,f177,f920])).

fof(f920,plain,
    ( spl4_86
  <=> k2_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f915,plain,
    ( k2_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f880,f178])).

fof(f880,plain,
    ( k2_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_80 ),
    inference(resolution,[],[f874,f122])).

fof(f914,plain,
    ( spl4_84
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f907,f873,f177,f912])).

fof(f912,plain,
    ( spl4_84
  <=> k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f907,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f877,f178])).

fof(f877,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_80 ),
    inference(resolution,[],[f874,f119])).

fof(f906,plain,
    ( spl4_82
    | ~ spl4_4
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f876,f873,f170,f904])).

fof(f904,plain,
    ( spl4_82
  <=> k2_xboole_0(sK1,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f876,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_80 ),
    inference(resolution,[],[f874,f214])).

fof(f875,plain,
    ( spl4_80
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f868,f689,f344,f170,f873])).

fof(f689,plain,
    ( spl4_72
  <=> k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f868,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f867,f171])).

fof(f867,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28
    | ~ spl4_72 ),
    inference(subsumption_resolution,[],[f866,f345])).

fof(f866,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_72 ),
    inference(superposition,[],[f136,f690])).

fof(f690,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f689])).

fof(f776,plain,
    ( spl4_78
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f766,f344,f235,f773])).

fof(f773,plain,
    ( spl4_78
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f235,plain,
    ( spl4_12
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f766,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(superposition,[],[f236,f373])).

fof(f373,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)
    | ~ spl4_28 ),
    inference(resolution,[],[f345,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',redefinition_k7_subset_1)).

fof(f236,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f235])).

fof(f775,plain,
    ( spl4_78
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f764,f344,f235,f773])).

fof(f764,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(superposition,[],[f373,f236])).

fof(f706,plain,
    ( spl4_76
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f673,f170,f704])).

fof(f673,plain,
    ( k2_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_subset_1(u1_struct_0(sK0),sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_4 ),
    inference(resolution,[],[f214,f127])).

fof(f698,plain,
    ( spl4_74
    | ~ spl4_4
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f671,f577,f170,f696])).

fof(f696,plain,
    ( spl4_74
  <=> k2_xboole_0(sK1,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f671,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_58 ),
    inference(resolution,[],[f214,f578])).

fof(f691,plain,
    ( spl4_72
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f670,f344,f170,f689])).

fof(f670,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(resolution,[],[f214,f345])).

fof(f682,plain,
    ( spl4_70
    | ~ spl4_4
    | ~ spl4_14
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f675,f439,f243,f170,f680])).

fof(f243,plain,
    ( spl4_14
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f675,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_14
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f663,f244])).

fof(f244,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f243])).

fof(f663,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_42 ),
    inference(resolution,[],[f214,f440])).

fof(f653,plain,
    ( spl4_68
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f616,f577,f651])).

fof(f651,plain,
    ( spl4_68
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f616,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ spl4_58 ),
    inference(resolution,[],[f578,f151])).

fof(f644,plain,
    ( spl4_66
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f637,f577,f510,f177,f642])).

fof(f642,plain,
    ( spl4_66
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f510,plain,
    ( spl4_54
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f637,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f636,f511])).

fof(f511,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f510])).

fof(f636,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f600,f178])).

fof(f600,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_58 ),
    inference(resolution,[],[f578,f123])).

fof(f635,plain,
    ( spl4_64
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f628,f577,f510,f177,f633])).

fof(f633,plain,
    ( spl4_64
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f628,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f627,f511])).

fof(f627,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f599,f178])).

fof(f599,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_58 ),
    inference(resolution,[],[f578,f122])).

fof(f626,plain,
    ( spl4_62
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f619,f577,f177,f624])).

fof(f624,plain,
    ( spl4_62
  <=> k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f619,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f596,f178])).

fof(f596,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_58 ),
    inference(resolution,[],[f578,f119])).

fof(f593,plain,
    ( ~ spl4_6
    | ~ spl4_42
    | spl4_59 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_42
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f591,f178])).

fof(f591,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_42
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f589,f440])).

fof(f589,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_59 ),
    inference(resolution,[],[f581,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
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
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',dt_k2_pre_topc)).

fof(f581,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl4_59
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f588,plain,
    ( ~ spl4_59
    | spl4_60
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f575,f510,f184,f177,f586,f580])).

fof(f586,plain,
    ( spl4_60
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f575,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f574,f185])).

fof(f574,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_6
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f572,f178])).

fof(f572,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_54 ),
    inference(superposition,[],[f124,f511])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',fc1_tops_1)).

fof(f519,plain,
    ( spl4_56
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f462,f439,f517])).

fof(f517,plain,
    ( spl4_56
  <=> k2_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f462,plain,
    ( k2_tops_1(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_42 ),
    inference(resolution,[],[f440,f151])).

fof(f512,plain,
    ( spl4_54
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f505,f439,f177,f510])).

fof(f505,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f450,f178])).

fof(f450,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_42 ),
    inference(resolution,[],[f440,f132])).

fof(f504,plain,
    ( ~ spl4_53
    | spl4_50
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f503,f439,f184,f177,f490,f496])).

fof(f496,plain,
    ( spl4_53
  <=> k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f490,plain,
    ( spl4_50
  <=> v4_pre_topc(k2_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f503,plain,
    ( v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f502,f178])).

fof(f502,plain,
    ( v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_8
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f449,f185])).

fof(f449,plain,
    ( v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_42 ),
    inference(resolution,[],[f440,f126])).

fof(f501,plain,
    ( ~ spl4_51
    | spl4_52
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f488,f439,f177,f499,f493])).

fof(f493,plain,
    ( spl4_51
  <=> ~ v4_pre_topc(k2_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f499,plain,
    ( spl4_52
  <=> k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f488,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f448,f178])).

fof(f448,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_42 ),
    inference(resolution,[],[f440,f125])).

fof(f487,plain,
    ( spl4_48
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f480,f439,f177,f485])).

fof(f485,plain,
    ( spl4_48
  <=> k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f480,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f446,f178])).

fof(f446,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_42 ),
    inference(resolution,[],[f440,f123])).

fof(f479,plain,
    ( spl4_46
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f472,f439,f177,f477])).

fof(f477,plain,
    ( spl4_46
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f472,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f445,f178])).

fof(f445,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_42 ),
    inference(resolution,[],[f440,f122])).

fof(f471,plain,
    ( spl4_44
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f464,f439,f177,f469])).

fof(f469,plain,
    ( spl4_44
  <=> k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f464,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f442,f178])).

fof(f442,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_42 ),
    inference(resolution,[],[f440,f119])).

fof(f441,plain,
    ( spl4_42
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f434,f170,f159,f439])).

fof(f159,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f434,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f424,f171])).

fof(f424,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(superposition,[],[f118,f160])).

fof(f160,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f159])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',dt_k7_subset_1)).

fof(f433,plain,
    ( spl4_40
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f423,f170,f159,f430])).

fof(f423,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f210,f160])).

fof(f210,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f117])).

fof(f432,plain,
    ( spl4_40
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f421,f170,f159,f430])).

fof(f421,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f160,f210])).

fof(f420,plain,
    ( spl4_38
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f383,f344,f418])).

fof(f418,plain,
    ( spl4_38
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f383,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl4_28 ),
    inference(resolution,[],[f345,f151])).

fof(f411,plain,
    ( spl4_36
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f404,f344,f260,f177,f409])).

fof(f409,plain,
    ( spl4_36
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f260,plain,
    ( spl4_18
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f404,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f403,f261])).

fof(f261,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f260])).

fof(f403,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f367,f178])).

fof(f367,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28 ),
    inference(resolution,[],[f345,f123])).

fof(f402,plain,
    ( spl4_34
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f395,f344,f260,f177,f400])).

fof(f400,plain,
    ( spl4_34
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f395,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f394,f261])).

fof(f394,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f366,f178])).

fof(f366,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28 ),
    inference(resolution,[],[f345,f122])).

fof(f393,plain,
    ( spl4_32
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f386,f344,f177,f391])).

fof(f391,plain,
    ( spl4_32
  <=> k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f386,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f363,f178])).

fof(f363,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28 ),
    inference(resolution,[],[f345,f119])).

fof(f360,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f358,f178])).

fof(f358,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_4
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f356,f171])).

fof(f356,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_29 ),
    inference(resolution,[],[f348,f133])).

fof(f348,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl4_29
  <=> ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f355,plain,
    ( ~ spl4_29
    | spl4_30
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f342,f260,f184,f177,f353,f347])).

fof(f353,plain,
    ( spl4_30
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f342,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f341,f185])).

fof(f341,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f339,f178])).

fof(f339,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_18 ),
    inference(superposition,[],[f124,f261])).

fof(f291,plain,
    ( ~ spl4_1
    | spl4_16
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f290,f177,f170,f252,f156])).

fof(f156,plain,
    ( spl4_1
  <=> ~ v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f252,plain,
    ( spl4_16
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f290,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f206,f178])).

fof(f206,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f125])).

fof(f289,plain,
    ( ~ spl4_17
    | spl4_0
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f288,f184,f177,f170,f153,f249])).

fof(f249,plain,
    ( spl4_17
  <=> k2_pre_topc(sK0,sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f153,plain,
    ( spl4_0
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f288,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) != sK1
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f287,f178])).

fof(f287,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) != sK1
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f207,f185])).

fof(f207,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) != sK1
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f126])).

fof(f286,plain,
    ( spl4_26
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f220,f170,f284])).

fof(f284,plain,
    ( spl4_26
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f220,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f151])).

fof(f279,plain,
    ( ~ spl4_23
    | spl4_24
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f219,f170,f277,f270])).

fof(f270,plain,
    ( spl4_23
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f277,plain,
    ( spl4_24
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f219,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f64])).

fof(f64,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',cc1_subset_1)).

fof(f272,plain,
    ( spl4_20
    | ~ spl4_23
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f218,f170,f270,f264])).

fof(f264,plain,
    ( spl4_20
  <=> ! [X8] : ~ r2_hidden(X8,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f218,plain,
    ( ! [X8] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(X8,sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',t5_subset)).

fof(f262,plain,
    ( spl4_18
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f255,f177,f170,f260])).

fof(f255,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f208,f178])).

fof(f208,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f132])).

fof(f254,plain,
    ( spl4_16
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f247,f177,f170,f153,f252])).

fof(f247,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f246,f178])).

fof(f246,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ l1_pre_topc(sK0)
    | ~ spl4_0
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f206,f154])).

fof(f154,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f153])).

fof(f245,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f238,f177,f170,f243])).

fof(f238,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f204,f178])).

fof(f204,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f123])).

fof(f237,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f230,f177,f170,f235])).

fof(f230,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f203,f178])).

fof(f203,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f122])).

fof(f229,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f222,f177,f170,f227])).

fof(f227,plain,
    ( spl4_10
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f222,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f200,f178])).

fof(f200,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f119])).

fof(f186,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f112,f184])).

fof(f112,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f104,f106,f105])).

fof(f105,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k2_tops_1(X0,sK1) != k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1))
          | ~ v4_pre_topc(sK1,X0) )
        & ( k2_tops_1(X0,sK1) = k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1))
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t77_tops_1.p',t77_tops_1)).

fof(f179,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f113,f177])).

fof(f113,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f107])).

fof(f172,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f114,f170])).

fof(f114,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f107])).

fof(f165,plain,
    ( spl4_0
    | spl4_2 ),
    inference(avatar_split_clause,[],[f115,f159,f153])).

fof(f115,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f107])).

fof(f164,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f116,f162,f156])).

fof(f162,plain,
    ( spl4_3
  <=> k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f107])).
%------------------------------------------------------------------------------
