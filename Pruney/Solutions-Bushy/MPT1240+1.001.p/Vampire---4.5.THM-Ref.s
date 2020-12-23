%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1240+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:32 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 368 expanded)
%              Number of leaves         :   46 ( 169 expanded)
%              Depth                    :   10
%              Number of atoms          :  618 (1845 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1871,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f118,f123,f128,f206,f211,f239,f254,f270,f318,f440,f484,f508,f549,f582,f845,f1051,f1228,f1236,f1468,f1829,f1830,f1866])).

fof(f1866,plain,
    ( ~ spl6_64
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f1834,f172,f95,f546])).

fof(f546,plain,
    ( spl6_64
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f95,plain,
    ( spl6_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f172,plain,
    ( spl6_17
  <=> v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1834,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f97,f174,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f84,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ sP5(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f72,f84_D])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f84,plain,(
    ! [X2,X1] :
      ( sP5(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f84_D])).

fof(f84_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f174,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f97,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1830,plain,
    ( ~ spl6_16
    | spl6_17
    | spl6_1 ),
    inference(avatar_split_clause,[],[f494,f87,f172,f168])).

fof(f168,plain,
    ( spl6_16
  <=> m1_subset_1(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f87,plain,
    ( spl6_1
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f494,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | spl6_1 ),
    inference(resolution,[],[f89,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f89,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f1829,plain,
    ( ~ spl6_167
    | ~ spl6_6
    | ~ spl6_30
    | spl6_195 ),
    inference(avatar_split_clause,[],[f1819,f1464,f267,f110,f1233])).

fof(f1233,plain,
    ( spl6_167
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).

fof(f110,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f267,plain,
    ( spl6_30
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1464,plain,
    ( spl6_195
  <=> r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_195])])).

fof(f1819,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_6
    | ~ spl6_30
    | spl6_195 ),
    inference(unit_resulting_resolution,[],[f112,f269,f1466,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f1466,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | spl6_195 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f269,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f267])).

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1468,plain,
    ( ~ spl6_195
    | spl6_64 ),
    inference(avatar_split_clause,[],[f1451,f546,f1464])).

fof(f1451,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | spl6_64 ),
    inference(resolution,[],[f548,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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

fof(f548,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | spl6_64 ),
    inference(avatar_component_clause,[],[f546])).

fof(f1236,plain,
    ( spl6_167
    | ~ spl6_141
    | ~ spl6_166 ),
    inference(avatar_split_clause,[],[f1229,f1225,f1048,f1233])).

fof(f1048,plain,
    ( spl6_141
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).

fof(f1225,plain,
    ( spl6_166
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).

fof(f1229,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_141
    | ~ spl6_166 ),
    inference(backward_demodulation,[],[f1050,f1227])).

fof(f1227,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2))
    | ~ spl6_166 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f1050,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_141 ),
    inference(avatar_component_clause,[],[f1048])).

fof(f1228,plain,
    ( ~ spl6_110
    | spl6_166
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f1214,f315,f1225,f842])).

fof(f842,plain,
    ( spl6_110
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f315,plain,
    ( spl6_37
  <=> k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f1214,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_37 ),
    inference(superposition,[],[f81,f317])).

fof(f317,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f315])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1051,plain,
    ( spl6_141
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_49
    | ~ spl6_69 ),
    inference(avatar_split_clause,[],[f1046,f579,f417,f208,f203,f120,f1048])).

fof(f120,plain,
    ( spl6_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f203,plain,
    ( spl6_21
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f208,plain,
    ( spl6_22
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f417,plain,
    ( spl6_49
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f579,plain,
    ( spl6_69
  <=> k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f1046,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_49
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f1036,f581])).

fof(f581,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f579])).

fof(f1036,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_49 ),
    inference(unit_resulting_resolution,[],[f122,f205,f210,f418,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f418,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f417])).

fof(f210,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f205,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f203])).

fof(f122,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f845,plain,
    ( spl6_110
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f831,f203,f120,f842])).

fof(f831,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f122,f205,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f582,plain,
    ( ~ spl6_8
    | ~ spl6_22
    | spl6_69
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f577,f437,f579,f208,f120])).

fof(f437,plain,
    ( spl6_53
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f577,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_53 ),
    inference(resolution,[],[f439,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f439,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f437])).

fof(f549,plain,
    ( ~ spl6_64
    | ~ spl6_3
    | spl6_16 ),
    inference(avatar_split_clause,[],[f537,f168,f95,f546])).

fof(f537,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_3
    | spl6_16 ),
    inference(unit_resulting_resolution,[],[f97,f170,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f170,plain,
    ( ~ m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f508,plain,
    ( spl6_49
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f503,f115,f110,f100,f417])).

fof(f100,plain,
    ( spl6_4
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f115,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f503,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f102,f117,f112,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f102,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f484,plain,
    ( ~ spl6_25
    | ~ spl6_1
    | ~ spl6_30
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f482,f251,f91,f267,f87,f236])).

fof(f236,plain,
    ( spl6_25
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f91,plain,
    ( spl6_2
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f251,plain,
    ( spl6_27
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f482,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(resolution,[],[f253,f92])).

fof(f92,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f253,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f251])).

fof(f440,plain,
    ( spl6_53
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f391,f125,f120,f110,f105,f437])).

fof(f105,plain,
    ( spl6_5
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f125,plain,
    ( spl6_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f391,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f127,f122,f107,f112,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_tops_1)).

fof(f107,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f127,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f318,plain,
    ( spl6_37
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f312,f120,f115,f315])).

fof(f312,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f122,f117,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f270,plain,
    ( spl6_30
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f265,f120,f115,f267])).

fof(f265,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f122,f117,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f254,plain,
    ( spl6_27
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f248,f125,f120,f115,f251])).

fof(f248,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f127,f122,f117,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f239,plain,
    ( spl6_25
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f234,f120,f115,f236])).

fof(f234,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f122,f117,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f211,plain,
    ( spl6_22
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f200,f110,f208])).

fof(f200,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f112,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f206,plain,
    ( spl6_21
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f201,f115,f203])).

fof(f201,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f117,f79])).

fof(f128,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f56,f125])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X1,k1_tops_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X2,X1] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2,X1] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X1,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X1,k1_tops_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK1,X3)
            | ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
      & ( ? [X4] :
            ( r2_hidden(sK1,X4)
            & r1_tarski(X4,sK2)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( r2_hidden(sK1,X4)
        & r1_tarski(X4,sK2)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,sK3)
      & r1_tarski(sK3,sK2)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,k1_tops_1(X0,X2))
            <=> ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f123,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f57,f120])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f118,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f58,f115])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f113,plain,
    ( spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f59,f110,f87])).

fof(f59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f108,plain,
    ( spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f60,f105,f87])).

fof(f60,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f61,f100,f87])).

fof(f61,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f62,f95,f87])).

fof(f62,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f63,f91,f87])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
