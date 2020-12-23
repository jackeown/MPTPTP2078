%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t51_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:44 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  479 (1746 expanded)
%              Number of leaves         :  120 ( 635 expanded)
%              Depth                    :   14
%              Number of atoms          : 1122 (4063 expanded)
%              Number of equality atoms :   46 ( 187 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f110,f117,f124,f142,f149,f226,f248,f294,f338,f373,f414,f421,f475,f488,f495,f516,f523,f549,f561,f593,f602,f610,f697,f715,f763,f770,f777,f851,f853,f856,f859,f884,f1034,f1065,f1073,f1080,f1096,f1105,f1195,f1240,f1401,f1408,f1428,f1441,f1469,f1476,f1498,f1524,f1533,f1550,f1707,f1709,f1736,f1909,f1926,f1935,f1949,f2088,f2097,f2106,f2127,f2328,f2335,f2407,f2436,f2443,f2489,f2564,f2571,f2610,f2631,f2684,f2691,f2728,f2936,f2943,f2950,f2969,f3001,f3008,f3012,f3320,f3323,f3329,f3459,f3693,f3715,f4039,f4067,f4074,f4146,f4165,f4186,f4193,f4200,f4207,f4215,f4234,f4251,f4259])).

fof(f4259,plain,
    ( ~ spl5_0
    | ~ spl5_4
    | ~ spl5_6
    | spl5_167 ),
    inference(avatar_contradiction_clause,[],[f4258])).

fof(f4258,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_167 ),
    inference(subsumption_resolution,[],[f4257,f725])).

fof(f725,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f102,f78,f116,f322,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t49_pre_topc)).

fof(f322,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f314,f214])).

fof(f214,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f123,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',dt_k9_subset_1)).

fof(f123,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f314,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f123,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',redefinition_k9_subset_1)).

fof(f116,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t17_xboole_1)).

fof(f102,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f4257,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_167 ),
    inference(subsumption_resolution,[],[f4255,f727])).

fof(f727,plain,
    ( ! [X0] : r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ spl5_0
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f102,f130,f123,f322,f75])).

fof(f130,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',commutativity_k3_xboole_0)).

fof(f4255,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
    | ~ spl5_167 ),
    inference(resolution,[],[f4214,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t19_xboole_1)).

fof(f4214,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | ~ spl5_167 ),
    inference(avatar_component_clause,[],[f4213])).

fof(f4213,plain,
    ( spl5_167
  <=> ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f4251,plain,
    ( ~ spl5_171
    | spl5_169 ),
    inference(avatar_split_clause,[],[f4235,f4232,f4249])).

fof(f4249,plain,
    ( spl5_171
  <=> ~ r1_tarski(sK3(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f4232,plain,
    ( spl5_169
  <=> ~ m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f4235,plain,
    ( ~ r1_tarski(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl5_169 ),
    inference(unit_resulting_resolution,[],[f4233,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t3_subset)).

fof(f4233,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_169 ),
    inference(avatar_component_clause,[],[f4232])).

fof(f4234,plain,
    ( ~ spl5_169
    | ~ spl5_12
    | ~ spl5_160 ),
    inference(avatar_split_clause,[],[f4221,f4191,f224,f4232])).

fof(f224,plain,
    ( spl5_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f4191,plain,
    ( spl5_160
  <=> r2_hidden(sK3(sK3(k1_xboole_0)),sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f4221,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_160 ),
    inference(unit_resulting_resolution,[],[f225,f4192,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t5_subset)).

fof(f4192,plain,
    ( r2_hidden(sK3(sK3(k1_xboole_0)),sK3(k1_xboole_0))
    | ~ spl5_160 ),
    inference(avatar_component_clause,[],[f4191])).

fof(f225,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f224])).

fof(f4215,plain,
    ( ~ spl5_167
    | ~ spl5_0
    | ~ spl5_6
    | spl5_33 ),
    inference(avatar_split_clause,[],[f528,f493,f122,f101,f4213])).

fof(f493,plain,
    ( spl5_33
  <=> ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f528,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f527,f453])).

fof(f453,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f102,f123,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',dt_k2_pre_topc)).

fof(f527,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_33 ),
    inference(superposition,[],[f494,f91])).

fof(f494,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f493])).

fof(f4207,plain,
    ( ~ spl5_165
    | spl5_153 ),
    inference(avatar_split_clause,[],[f4156,f4072,f4205])).

fof(f4205,plain,
    ( spl5_165
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f4072,plain,
    ( spl5_153
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f4156,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK2)))
    | ~ spl5_153 ),
    inference(unit_resulting_resolution,[],[f4073,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t1_subset)).

fof(f4073,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK2)))
    | ~ spl5_153 ),
    inference(avatar_component_clause,[],[f4072])).

fof(f4200,plain,
    ( ~ spl5_163
    | spl5_151 ),
    inference(avatar_split_clause,[],[f4082,f4065,f4198])).

fof(f4198,plain,
    ( spl5_163
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f4065,plain,
    ( spl5_151
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f4082,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK1)))
    | ~ spl5_151 ),
    inference(unit_resulting_resolution,[],[f4066,f81])).

fof(f4066,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK1)))
    | ~ spl5_151 ),
    inference(avatar_component_clause,[],[f4065])).

fof(f4193,plain,
    ( spl5_160
    | spl5_123 ),
    inference(avatar_split_clause,[],[f3696,f2562,f4191])).

fof(f2562,plain,
    ( spl5_123
  <=> ~ v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f3696,plain,
    ( r2_hidden(sK3(sK3(k1_xboole_0)),sK3(k1_xboole_0))
    | ~ spl5_123 ),
    inference(unit_resulting_resolution,[],[f76,f2563,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t2_subset)).

fof(f2563,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_123 ),
    inference(avatar_component_clause,[],[f2562])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',existence_m1_subset_1)).

fof(f4186,plain,
    ( ~ spl5_159
    | spl5_123 ),
    inference(avatar_split_clause,[],[f3695,f2562,f4184])).

fof(f4184,plain,
    ( spl5_159
  <=> ~ r2_hidden(sK3(k1_xboole_0),sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f3695,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0),sK3(sK3(k1_xboole_0)))
    | ~ spl5_123 ),
    inference(unit_resulting_resolution,[],[f76,f2563,f182])).

fof(f182,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f82,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',antisymmetry_r2_hidden)).

fof(f4165,plain,
    ( ~ spl5_157
    | spl5_153 ),
    inference(avatar_split_clause,[],[f4149,f4072,f4163])).

fof(f4163,plain,
    ( spl5_157
  <=> ~ r1_tarski(u1_struct_0(sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f4149,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK3(sK2))
    | ~ spl5_153 ),
    inference(unit_resulting_resolution,[],[f4073,f86])).

fof(f4146,plain,
    ( ~ spl5_155
    | spl5_151 ),
    inference(avatar_split_clause,[],[f4075,f4065,f4144])).

fof(f4144,plain,
    ( spl5_155
  <=> ~ r1_tarski(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f4075,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK3(sK1))
    | ~ spl5_151 ),
    inference(unit_resulting_resolution,[],[f4066,f86])).

fof(f4074,plain,
    ( ~ spl5_153
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2648,f1947,f4072])).

fof(f1947,plain,
    ( spl5_106
  <=> r2_hidden(sK3(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f2648,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK2)))
    | ~ spl5_106 ),
    inference(unit_resulting_resolution,[],[f1948,f199])).

fof(f199,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f198,f95])).

fof(f198,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f196,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t4_subset)).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f182,f82])).

fof(f1948,plain,
    ( r2_hidden(sK3(sK2),u1_struct_0(sK0))
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f1947])).

fof(f4067,plain,
    ( ~ spl5_151
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f1054,f775,f4065])).

fof(f775,plain,
    ( spl5_56
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1054,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3(sK1)))
    | ~ spl5_56 ),
    inference(unit_resulting_resolution,[],[f776,f199])).

fof(f776,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f775])).

fof(f4039,plain,
    ( ~ spl5_149
    | spl5_41 ),
    inference(avatar_split_clause,[],[f3586,f559,f4037])).

fof(f4037,plain,
    ( spl5_149
  <=> ~ r2_hidden(sK1,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f559,plain,
    ( spl5_41
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f3586,plain,
    ( ~ r2_hidden(sK1,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f76,f560,f93])).

fof(f560,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f559])).

fof(f3715,plain,
    ( ~ spl5_113
    | spl5_131 ),
    inference(avatar_split_clause,[],[f2700,f2682,f2326])).

fof(f2326,plain,
    ( spl5_113
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f2682,plain,
    ( spl5_131
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f2700,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_131 ),
    inference(resolution,[],[f2683,f86])).

fof(f2683,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f2682])).

fof(f3693,plain,
    ( spl5_109
    | ~ spl5_120 ),
    inference(avatar_contradiction_clause,[],[f3692])).

fof(f3692,plain,
    ( $false
    | ~ spl5_109
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f3691,f2096])).

fof(f2096,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_109 ),
    inference(avatar_component_clause,[],[f2095])).

fof(f2095,plain,
    ( spl5_109
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f3691,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_120 ),
    inference(superposition,[],[f76,f2488])).

fof(f2488,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f2487])).

fof(f2487,plain,
    ( spl5_120
  <=> k1_xboole_0 = sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f3459,plain,
    ( ~ spl5_39
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2644,f1947,f547])).

fof(f547,plain,
    ( spl5_39
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f2644,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_106 ),
    inference(unit_resulting_resolution,[],[f1948,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t7_boole)).

fof(f3329,plain,
    ( ~ spl5_38
    | ~ spl5_106 ),
    inference(avatar_contradiction_clause,[],[f3328])).

fof(f3328,plain,
    ( $false
    | ~ spl5_38
    | ~ spl5_106 ),
    inference(subsumption_resolution,[],[f545,f2644])).

fof(f545,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl5_38
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f3323,plain,
    ( spl5_33
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_98 ),
    inference(avatar_contradiction_clause,[],[f3322])).

fof(f3322,plain,
    ( $false
    | ~ spl5_33
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f3321,f157])).

fof(f157,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f126,f86])).

fof(f126,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(superposition,[],[f78,f77])).

fof(f77,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',idempotence_k3_xboole_0)).

fof(f3321,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(k2_pre_topc(sK0,k1_xboole_0)))
    | ~ spl5_33
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f3256,f77])).

fof(f3256,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(k3_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,k1_xboole_0))))
    | ~ spl5_33
    | ~ spl5_58
    | ~ spl5_60
    | ~ spl5_98 ),
    inference(backward_demodulation,[],[f883,f3131])).

fof(f3131,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(k3_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,sK1))))
    | ~ spl5_33
    | ~ spl5_60
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f3130,f73])).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t2_boole)).

fof(f3130,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_xboole_0(sK1,k1_xboole_0)),k1_zfmisc_1(k3_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,sK1))))
    | ~ spl5_33
    | ~ spl5_60
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f3046,f79])).

fof(f3046,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_xboole_0(sK1,k1_xboole_0)),k1_zfmisc_1(k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_xboole_0))))
    | ~ spl5_33
    | ~ spl5_60
    | ~ spl5_98 ),
    inference(backward_demodulation,[],[f1735,f1126])).

fof(f1126,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k1_zfmisc_1(k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | ~ spl5_33
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f1124,f79])).

fof(f1124,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k1_zfmisc_1(k3_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))))
    | ~ spl5_33
    | ~ spl5_60 ),
    inference(backward_demodulation,[],[f1122,f525])).

fof(f525,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k1_zfmisc_1(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f494,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f1122,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k3_xboole_0(X0,k2_pre_topc(sK0,sK1))
    | ~ spl5_60 ),
    inference(backward_demodulation,[],[f1117,f1118])).

fof(f1118,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f1033,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',commutativity_k9_subset_1)).

fof(f1033,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl5_60
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1117,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(X0,k2_pre_topc(sK0,sK1))
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f1033,f91])).

fof(f1735,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f1734])).

fof(f1734,plain,
    ( spl5_98
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f883,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl5_58
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f3320,plain,
    ( ~ spl5_0
    | ~ spl5_6
    | spl5_33
    | ~ spl5_58
    | ~ spl5_98 ),
    inference(avatar_contradiction_clause,[],[f3319])).

fof(f3319,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_33
    | ~ spl5_58
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f3318,f126])).

fof(f3318,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_33
    | ~ spl5_58
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f3255,f77])).

fof(f3255,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k3_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,k1_xboole_0)))
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_33
    | ~ spl5_58
    | ~ spl5_98 ),
    inference(backward_demodulation,[],[f883,f3105])).

fof(f3105,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k3_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,sK1)))
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_33
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f3104,f73])).

fof(f3104,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,k1_xboole_0)),k3_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k2_pre_topc(sK0,sK1)))
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_33
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f3023,f79])).

fof(f3023,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,k1_xboole_0)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_xboole_0)))
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_33
    | ~ spl5_98 ),
    inference(backward_demodulation,[],[f1735,f528])).

fof(f3012,plain,
    ( ~ spl5_112
    | spl5_131 ),
    inference(avatar_contradiction_clause,[],[f3011])).

fof(f3011,plain,
    ( $false
    | ~ spl5_112
    | ~ spl5_131 ),
    inference(subsumption_resolution,[],[f2324,f2700])).

fof(f2324,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f2323])).

fof(f2323,plain,
    ( spl5_112
  <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f3008,plain,
    ( spl5_146
    | spl5_39 ),
    inference(avatar_split_clause,[],[f2118,f547,f3006])).

fof(f3006,plain,
    ( spl5_146
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f2118,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f76,f548,f82])).

fof(f548,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f547])).

fof(f3001,plain,
    ( ~ spl5_145
    | spl5_39 ),
    inference(avatar_split_clause,[],[f2116,f547,f2999])).

fof(f2999,plain,
    ( spl5_145
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f2116,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f76,f548,f182])).

fof(f2969,plain,
    ( ~ spl5_143
    | spl5_91 ),
    inference(avatar_split_clause,[],[f1866,f1496,f2967])).

fof(f2967,plain,
    ( spl5_143
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f1496,plain,
    ( spl5_91
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f1866,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_91 ),
    inference(unit_resulting_resolution,[],[f76,f1497,f93])).

fof(f1497,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_91 ),
    inference(avatar_component_clause,[],[f1496])).

fof(f2950,plain,
    ( spl5_140
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f455,f108,f2948])).

fof(f2948,plain,
    ( spl5_140
  <=> m1_subset_1(k2_pre_topc(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f108,plain,
    ( spl5_2
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f455,plain,
    ( m1_subset_1(k2_pre_topc(sK4,sK3(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f109,f76,f83])).

fof(f109,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f2943,plain,
    ( ~ spl5_139
    | spl5_81 ),
    inference(avatar_split_clause,[],[f1455,f1420,f2941])).

fof(f2941,plain,
    ( spl5_139
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f1420,plain,
    ( spl5_81
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f1455,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ spl5_81 ),
    inference(unit_resulting_resolution,[],[f76,f1421,f93])).

fof(f1421,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2)
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f2936,plain,
    ( ~ spl5_137
    | spl5_27 ),
    inference(avatar_split_clause,[],[f507,f467,f2934])).

fof(f2934,plain,
    ( spl5_137
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f467,plain,
    ( spl5_27
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f507,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(k1_zfmisc_1(sK1)))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f76,f468,f93])).

fof(f468,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f467])).

fof(f2728,plain,
    ( spl5_134
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f454,f101,f2726])).

fof(f2726,plain,
    ( spl5_134
  <=> m1_subset_1(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f454,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK3(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f102,f76,f83])).

fof(f2691,plain,
    ( ~ spl5_133
    | spl5_123 ),
    inference(avatar_split_clause,[],[f2575,f2562,f2689])).

fof(f2689,plain,
    ( spl5_133
  <=> ~ m1_subset_1(sK3(k1_xboole_0),sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f2575,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),sK3(k1_xboole_0))
    | ~ spl5_123 ),
    inference(unit_resulting_resolution,[],[f201,f2563,f82])).

fof(f201,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(unit_resulting_resolution,[],[f157,f199])).

fof(f2684,plain,
    ( ~ spl5_131
    | spl5_111 ),
    inference(avatar_split_clause,[],[f2510,f2122,f2682])).

fof(f2122,plain,
    ( spl5_111
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f2510,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_111 ),
    inference(unit_resulting_resolution,[],[f201,f2123,f82])).

fof(f2123,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f2122])).

fof(f2631,plain,
    ( ~ spl5_129
    | spl5_101 ),
    inference(avatar_split_clause,[],[f1917,f1907,f2629])).

fof(f2629,plain,
    ( spl5_129
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f1907,plain,
    ( spl5_101
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f1917,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK3(sK2)))
    | ~ spl5_101 ),
    inference(unit_resulting_resolution,[],[f1908,f81])).

fof(f1908,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3(sK2)))
    | ~ spl5_101 ),
    inference(avatar_component_clause,[],[f1907])).

fof(f2610,plain,
    ( spl5_126
    | ~ spl5_0
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f580,f122,f101,f2608])).

fof(f2608,plain,
    ( spl5_126
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f580,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl5_0
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f102,f123,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',projectivity_k2_pre_topc)).

fof(f2571,plain,
    ( spl5_124
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f579,f115,f101,f2569])).

fof(f2569,plain,
    ( spl5_124
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f579,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f102,f116,f84])).

fof(f2564,plain,
    ( ~ spl5_123
    | ~ spl5_12
    | spl5_121 ),
    inference(avatar_split_clause,[],[f2557,f2484,f224,f2562])).

fof(f2484,plain,
    ( spl5_121
  <=> k1_xboole_0 != sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f2557,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f225,f2485,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t8_boole)).

fof(f2485,plain,
    ( k1_xboole_0 != sK3(k1_xboole_0)
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f2484])).

fof(f2489,plain,
    ( spl5_120
    | ~ spl5_20
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f2355,f2125,f371,f2487])).

fof(f371,plain,
    ( spl5_20
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f2125,plain,
    ( spl5_110
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f2355,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_110 ),
    inference(backward_demodulation,[],[f2349,f372])).

fof(f372,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f371])).

fof(f2349,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl5_110 ),
    inference(unit_resulting_resolution,[],[f2126,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t6_boole)).

fof(f2126,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f2125])).

fof(f2443,plain,
    ( ~ spl5_119
    | spl5_91
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f2366,f2125,f1496,f2441])).

fof(f2441,plain,
    ( spl5_119
  <=> ~ m1_subset_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f2366,plain,
    ( ~ m1_subset_1(sK2,k1_xboole_0)
    | ~ spl5_91
    | ~ spl5_110 ),
    inference(backward_demodulation,[],[f2349,f1497])).

fof(f2436,plain,
    ( ~ spl5_117
    | spl5_41
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f2356,f2125,f559,f2434])).

fof(f2434,plain,
    ( spl5_117
  <=> ~ m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f2356,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl5_41
    | ~ spl5_110 ),
    inference(backward_demodulation,[],[f2349,f560])).

fof(f2407,plain,
    ( ~ spl5_110
    | spl5_113 ),
    inference(avatar_contradiction_clause,[],[f2406])).

fof(f2406,plain,
    ( $false
    | ~ spl5_110
    | ~ spl5_113 ),
    inference(subsumption_resolution,[],[f2380,f125])).

fof(f125,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f78,f73])).

fof(f2380,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_110
    | ~ spl5_113 ),
    inference(backward_demodulation,[],[f2349,f2327])).

fof(f2327,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f2326])).

fof(f2335,plain,
    ( spl5_114
    | ~ spl5_20
    | spl5_111 ),
    inference(avatar_split_clause,[],[f2183,f2122,f371,f2333])).

fof(f2333,plain,
    ( spl5_114
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f2183,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_111 ),
    inference(forward_demodulation,[],[f2178,f372])).

fof(f2178,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_111 ),
    inference(unit_resulting_resolution,[],[f76,f2123,f82])).

fof(f2328,plain,
    ( ~ spl5_113
    | spl5_111 ),
    inference(avatar_split_clause,[],[f2165,f2122,f2326])).

fof(f2165,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_111 ),
    inference(unit_resulting_resolution,[],[f2123,f197])).

fof(f197,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_zfmisc_1(X0),X0)
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f196,f86])).

fof(f2127,plain,
    ( spl5_110
    | spl5_45
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f2036,f882,f600,f2125])).

fof(f600,plain,
    ( spl5_45
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f2036,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_45
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f1971,f156])).

fof(f156,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f125,f86])).

fof(f1971,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_45
    | ~ spl5_58 ),
    inference(backward_demodulation,[],[f883,f603])).

fof(f603,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_45 ),
    inference(resolution,[],[f601,f82])).

fof(f601,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f600])).

fof(f2106,plain,
    ( ~ spl5_39
    | ~ spl5_6
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f1853,f1474,f122,f547])).

fof(f1474,plain,
    ( spl5_88
  <=> r2_hidden(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f1853,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_6
    | ~ spl5_88 ),
    inference(unit_resulting_resolution,[],[f123,f1475,f95])).

fof(f1475,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f1474])).

fof(f2097,plain,
    ( ~ spl5_109
    | spl5_31
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f1961,f882,f486,f2095])).

fof(f486,plain,
    ( spl5_31
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1961,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_31
    | ~ spl5_58 ),
    inference(backward_demodulation,[],[f883,f487])).

fof(f487,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f486])).

fof(f2088,plain,
    ( ~ spl5_6
    | ~ spl5_38
    | ~ spl5_88 ),
    inference(avatar_contradiction_clause,[],[f2087])).

fof(f2087,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_38
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f545,f1853])).

fof(f1949,plain,
    ( spl5_106
    | spl5_39
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1872,f1548,f547,f1947])).

fof(f1548,plain,
    ( spl5_96
  <=> m1_subset_1(sK3(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f1872,plain,
    ( r2_hidden(sK3(sK2),u1_struct_0(sK0))
    | ~ spl5_39
    | ~ spl5_96 ),
    inference(unit_resulting_resolution,[],[f548,f1549,f82])).

fof(f1549,plain,
    ( m1_subset_1(sK3(sK2),u1_struct_0(sK0))
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f1548])).

fof(f1935,plain,
    ( ~ spl5_105
    | spl5_39
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1871,f1548,f547,f1933])).

fof(f1933,plain,
    ( spl5_105
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f1871,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(sK2))
    | ~ spl5_39
    | ~ spl5_96 ),
    inference(unit_resulting_resolution,[],[f548,f1549,f182])).

fof(f1926,plain,
    ( ~ spl5_103
    | spl5_101 ),
    inference(avatar_split_clause,[],[f1910,f1907,f1924])).

fof(f1924,plain,
    ( spl5_103
  <=> ~ r1_tarski(sK2,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f1910,plain,
    ( ~ r1_tarski(sK2,sK3(sK2))
    | ~ spl5_101 ),
    inference(unit_resulting_resolution,[],[f1908,f86])).

fof(f1909,plain,
    ( ~ spl5_101
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f1855,f1474,f1907])).

fof(f1855,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3(sK2)))
    | ~ spl5_88 ),
    inference(unit_resulting_resolution,[],[f1475,f199])).

fof(f1736,plain,
    ( spl5_98
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f1564,f1426,f1734])).

fof(f1426,plain,
    ( spl5_82
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f1564,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_82 ),
    inference(unit_resulting_resolution,[],[f1427,f74])).

fof(f1427,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f1426])).

fof(f1709,plain,
    ( ~ spl5_82
    | spl5_93 ),
    inference(avatar_contradiction_clause,[],[f1708])).

fof(f1708,plain,
    ( $false
    | ~ spl5_82
    | ~ spl5_93 ),
    inference(subsumption_resolution,[],[f1647,f125])).

fof(f1647,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_82
    | ~ spl5_93 ),
    inference(backward_demodulation,[],[f1564,f1523])).

fof(f1523,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1522,plain,
    ( spl5_93
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f1707,plain,
    ( ~ spl5_82
    | spl5_91 ),
    inference(avatar_contradiction_clause,[],[f1706])).

fof(f1706,plain,
    ( $false
    | ~ spl5_82
    | ~ spl5_91 ),
    inference(subsumption_resolution,[],[f1641,f156])).

fof(f1641,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_82
    | ~ spl5_91 ),
    inference(backward_demodulation,[],[f1564,f1497])).

fof(f1550,plain,
    ( spl5_96
    | ~ spl5_6
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f1482,f1474,f122,f1548])).

fof(f1482,plain,
    ( m1_subset_1(sK3(sK2),u1_struct_0(sK0))
    | ~ spl5_6
    | ~ spl5_88 ),
    inference(unit_resulting_resolution,[],[f123,f1475,f93])).

fof(f1533,plain,
    ( ~ spl5_95
    | spl5_91 ),
    inference(avatar_split_clause,[],[f1515,f1496,f1531])).

fof(f1531,plain,
    ( spl5_95
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f1515,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_91 ),
    inference(unit_resulting_resolution,[],[f1497,f81])).

fof(f1524,plain,
    ( ~ spl5_93
    | spl5_91 ),
    inference(avatar_split_clause,[],[f1508,f1496,f1522])).

fof(f1508,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_91 ),
    inference(unit_resulting_resolution,[],[f1497,f86])).

fof(f1498,plain,
    ( ~ spl5_91
    | ~ spl5_12
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f1484,f1474,f224,f1496])).

fof(f1484,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_88 ),
    inference(unit_resulting_resolution,[],[f225,f1475,f95])).

fof(f1476,plain,
    ( spl5_88
    | spl5_83 ),
    inference(avatar_split_clause,[],[f1431,f1423,f1474])).

fof(f1423,plain,
    ( spl5_83
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f1431,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f76,f1424,f82])).

fof(f1424,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f1469,plain,
    ( ~ spl5_87
    | spl5_83 ),
    inference(avatar_split_clause,[],[f1430,f1423,f1467])).

fof(f1467,plain,
    ( spl5_87
  <=> ~ r2_hidden(sK2,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f1430,plain,
    ( ~ r2_hidden(sK2,sK3(sK2))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f76,f1424,f182])).

fof(f1441,plain,
    ( ~ spl5_85
    | spl5_83 ),
    inference(avatar_split_clause,[],[f1432,f1423,f1439])).

fof(f1439,plain,
    ( spl5_85
  <=> ~ m1_subset_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f1432,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f201,f1424,f82])).

fof(f1428,plain,
    ( ~ spl5_81
    | spl5_82
    | spl5_17 ),
    inference(avatar_split_clause,[],[f296,f292,f1426,f1420])).

fof(f292,plain,
    ( spl5_17
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f296,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),sK2)
    | ~ spl5_17 ),
    inference(resolution,[],[f293,f82])).

fof(f293,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f292])).

fof(f1408,plain,
    ( ~ spl5_79
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f1210,f1071,f1406])).

fof(f1406,plain,
    ( spl5_79
  <=> ~ r2_hidden(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f1071,plain,
    ( spl5_64
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f1210,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f1072,f199])).

fof(f1072,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f1401,plain,
    ( ~ spl5_77
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f1120,f1032,f1399])).

fof(f1399,plain,
    ( spl5_77
  <=> ~ r2_hidden(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f1120,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f1033,f199])).

fof(f1240,plain,
    ( spl5_74
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f1205,f1071,f1238])).

fof(f1238,plain,
    ( spl5_74
  <=> r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f1205,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f1072,f85])).

fof(f1195,plain,
    ( spl5_72
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f1115,f1032,f1193])).

fof(f1193,plain,
    ( spl5_72
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f1115,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f1033,f85])).

fof(f1105,plain,
    ( ~ spl5_71
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1087,f1078,f1103])).

fof(f1103,plain,
    ( spl5_71
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f1078,plain,
    ( spl5_67
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f1087,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f1079,f81])).

fof(f1079,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f1078])).

fof(f1096,plain,
    ( ~ spl5_69
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1081,f1078,f1094])).

fof(f1094,plain,
    ( spl5_69
  <=> ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f1081,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f1079,f86])).

fof(f1080,plain,
    ( ~ spl5_67
    | ~ spl5_12
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f1052,f775,f224,f1078])).

fof(f1052,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_56 ),
    inference(unit_resulting_resolution,[],[f225,f776,f95])).

fof(f1073,plain,
    ( spl5_64
    | ~ spl5_0
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f453,f122,f101,f1071])).

fof(f1065,plain,
    ( ~ spl5_63
    | spl5_49 ),
    inference(avatar_split_clause,[],[f1025,f695,f1063])).

fof(f1063,plain,
    ( spl5_63
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f695,plain,
    ( spl5_49
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f1025,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK3(sK1)))
    | ~ spl5_49 ),
    inference(unit_resulting_resolution,[],[f696,f81])).

fof(f696,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(sK1)))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f695])).

fof(f1034,plain,
    ( spl5_60
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f452,f115,f101,f1032])).

fof(f452,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f102,f116,f83])).

fof(f884,plain,
    ( spl5_58
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f788,f473,f882])).

fof(f473,plain,
    ( spl5_28
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f788,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_28 ),
    inference(unit_resulting_resolution,[],[f474,f74])).

fof(f474,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f473])).

fof(f859,plain,
    ( ~ spl5_28
    | spl5_51 ),
    inference(avatar_contradiction_clause,[],[f858])).

fof(f858,plain,
    ( $false
    | ~ spl5_28
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f836,f125])).

fof(f836,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0))
    | ~ spl5_28
    | ~ spl5_51 ),
    inference(backward_demodulation,[],[f788,f714])).

fof(f714,plain,
    ( ~ r1_tarski(sK1,sK3(sK1))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f713])).

fof(f713,plain,
    ( spl5_51
  <=> ~ r1_tarski(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f856,plain,
    ( ~ spl5_28
    | spl5_49 ),
    inference(avatar_contradiction_clause,[],[f855])).

fof(f855,plain,
    ( $false
    | ~ spl5_28
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f830,f156])).

fof(f830,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3(k1_xboole_0)))
    | ~ spl5_28
    | ~ spl5_49 ),
    inference(backward_demodulation,[],[f788,f696])).

fof(f853,plain,
    ( ~ spl5_28
    | spl5_43 ),
    inference(avatar_contradiction_clause,[],[f852])).

fof(f852,plain,
    ( $false
    | ~ spl5_28
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f823,f125])).

fof(f823,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_28
    | ~ spl5_43 ),
    inference(backward_demodulation,[],[f788,f592])).

fof(f592,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl5_43
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f851,plain,
    ( ~ spl5_28
    | spl5_41 ),
    inference(avatar_contradiction_clause,[],[f850])).

fof(f850,plain,
    ( $false
    | ~ spl5_28
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f817,f156])).

fof(f817,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_28
    | ~ spl5_41 ),
    inference(backward_demodulation,[],[f788,f560])).

fof(f777,plain,
    ( spl5_56
    | spl5_39
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f699,f608,f547,f775])).

fof(f608,plain,
    ( spl5_46
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f699,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_39
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f548,f609,f82])).

fof(f609,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f608])).

fof(f770,plain,
    ( ~ spl5_55
    | spl5_39
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f698,f608,f547,f768])).

fof(f768,plain,
    ( spl5_55
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f698,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(sK1))
    | ~ spl5_39
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f548,f609,f182])).

fof(f763,plain,
    ( ~ spl5_53
    | spl5_39 ),
    inference(avatar_split_clause,[],[f553,f547,f761])).

fof(f761,plain,
    ( spl5_53
  <=> ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f553,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f201,f548,f82])).

fof(f715,plain,
    ( ~ spl5_51
    | spl5_49 ),
    inference(avatar_split_clause,[],[f700,f695,f713])).

fof(f700,plain,
    ( ~ r1_tarski(sK1,sK3(sK1))
    | ~ spl5_49 ),
    inference(unit_resulting_resolution,[],[f696,f86])).

fof(f697,plain,
    ( ~ spl5_49
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f538,f521,f695])).

fof(f521,plain,
    ( spl5_36
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f538,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(sK1)))
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f522,f199])).

fof(f522,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f521])).

fof(f610,plain,
    ( spl5_46
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f533,f521,f115,f608])).

fof(f533,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f116,f522,f93])).

fof(f602,plain,
    ( ~ spl5_45
    | spl5_41 ),
    inference(avatar_split_clause,[],[f568,f559,f600])).

fof(f568,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f560,f81])).

fof(f593,plain,
    ( ~ spl5_43
    | spl5_41 ),
    inference(avatar_split_clause,[],[f562,f559,f591])).

fof(f562,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f560,f86])).

fof(f561,plain,
    ( ~ spl5_41
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f535,f521,f224,f559])).

fof(f535,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f225,f522,f95])).

fof(f549,plain,
    ( ~ spl5_39
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f536,f521,f115,f547])).

fof(f536,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f116,f522,f95])).

fof(f523,plain,
    ( spl5_36
    | spl5_29 ),
    inference(avatar_split_clause,[],[f478,f470,f521])).

fof(f470,plain,
    ( spl5_29
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f478,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f76,f471,f82])).

fof(f471,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f470])).

fof(f516,plain,
    ( ~ spl5_35
    | spl5_29 ),
    inference(avatar_split_clause,[],[f477,f470,f514])).

fof(f514,plain,
    ( spl5_35
  <=> ~ r2_hidden(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f477,plain,
    ( ~ r2_hidden(sK1,sK3(sK1))
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f76,f471,f182])).

fof(f495,plain,
    ( ~ spl5_33
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f321,f122,f493])).

fof(f321,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f314,f72])).

fof(f72,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f62,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',t51_pre_topc)).

fof(f488,plain,
    ( ~ spl5_31
    | spl5_29 ),
    inference(avatar_split_clause,[],[f479,f470,f486])).

fof(f479,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f201,f471,f82])).

fof(f475,plain,
    ( ~ spl5_27
    | spl5_28
    | spl5_15 ),
    inference(avatar_split_clause,[],[f295,f246,f473,f467])).

fof(f246,plain,
    ( spl5_15
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f295,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl5_15 ),
    inference(resolution,[],[f247,f82])).

fof(f247,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f246])).

fof(f421,plain,
    ( spl5_24
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f265,f147,f419])).

fof(f419,plain,
    ( spl5_24
  <=> r1_tarski(sK2,k3_xboole_0(sK2,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f147,plain,
    ( spl5_10
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f265,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f126,f148,f94])).

fof(f148,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f414,plain,
    ( spl5_22
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f263,f140,f412])).

fof(f412,plain,
    ( spl5_22
  <=> r1_tarski(sK1,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f140,plain,
    ( spl5_8
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f263,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f126,f141,f94])).

fof(f141,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f373,plain,
    ( spl5_20
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f349,f336,f371])).

fof(f336,plain,
    ( spl5_18
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f349,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f337,f74])).

fof(f337,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f336])).

fof(f338,plain,
    ( spl5_18
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f330,f224,f336])).

fof(f330,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f76,f231,f82])).

fof(f231,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f76,f225,f95])).

fof(f294,plain,
    ( ~ spl5_17
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f206,f122,f292])).

fof(f206,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f123,f199])).

fof(f248,plain,
    ( ~ spl5_15
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f205,f115,f246])).

fof(f205,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f116,f199])).

fof(f226,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f218,f224])).

fof(f218,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f76,f204,f82])).

fof(f204,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f156,f199])).

fof(f149,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f135,f122,f147])).

fof(f135,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f123,f85])).

fof(f142,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f134,f115,f140])).

fof(f134,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f116,f85])).

fof(f124,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f71,f122])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f117,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f70,f115])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f110,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f96,f108])).

fof(f96,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f67])).

fof(f67,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t51_pre_topc.p',existence_l1_pre_topc)).

fof(f103,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f69,f101])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
