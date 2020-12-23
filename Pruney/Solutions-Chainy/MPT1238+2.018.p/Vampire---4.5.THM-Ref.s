%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:06 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 714 expanded)
%              Number of leaves         :   50 ( 274 expanded)
%              Depth                    :   10
%              Number of atoms          :  546 (1682 expanded)
%              Number of equality atoms :   68 ( 242 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1434,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f92,f105,f110,f136,f141,f242,f247,f252,f257,f822,f1229,f1234,f1239,f1244,f1249,f1261,f1266,f1271,f1276,f1281,f1290,f1308,f1329,f1334,f1339,f1344,f1404,f1409,f1414,f1419,f1424,f1429,f1433])).

fof(f1433,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_14
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f1432])).

fof(f1432,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_14
    | spl3_30 ),
    inference(subsumption_resolution,[],[f1431,f543])).

fof(f543,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f56,f40,f66,f251,f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f251,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl3_11
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1431,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_14
    | spl3_30 ),
    inference(subsumption_resolution,[],[f1430,f1250])).

fof(f1250,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f56,f61,f251,f1228,f39])).

fof(f1228,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f1226])).

fof(f1226,plain,
    ( spl3_14
  <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1430,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_30 ),
    inference(resolution,[],[f1403,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1403,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f1401,plain,
    ( spl3_30
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f1429,plain,
    ( spl3_35
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f158,f59,f1426])).

fof(f1426,plain,
    ( spl3_35
  <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f158,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK2)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f143,f70])).

fof(f70,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f143,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK2)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f61,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(f1424,plain,
    ( spl3_34
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f157,f64,f59,f1421])).

fof(f1421,plain,
    ( spl3_34
  <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f157,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f144,f71])).

fof(f71,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f42])).

fof(f144,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f61,f44])).

fof(f1419,plain,
    ( spl3_33
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f979,f89,f64,f59,f1416])).

fof(f1416,plain,
    ( spl3_33
  <=> r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f89,plain,
    ( spl3_4
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f979,plain,
    ( r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f978,f81])).

fof(f81,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f77,f71])).

fof(f77,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f978,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f977,f171])).

fof(f171,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f170,f94])).

fof(f94,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f170,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f161,f71])).

fof(f161,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f61,f66,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f977,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f835,f96])).

fof(f96,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f835,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2)))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f61,f91,f44])).

fof(f91,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f1414,plain,
    ( spl3_32
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f156,f64,f59,f1411])).

fof(f1411,plain,
    ( spl3_32
  <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f156,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f155,f70])).

fof(f155,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f145,f97])).

fof(f97,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f49])).

fof(f145,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f61,f66,f44])).

fof(f1409,plain,
    ( spl3_31
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f154,f64,f1406])).

fof(f1406,plain,
    ( spl3_31
  <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f154,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK1)))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f146,f71])).

fof(f146,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK1)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f66,f44])).

fof(f1404,plain,
    ( ~ spl3_30
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f131,f107,f102,f64,f59,f54,f1401])).

fof(f102,plain,
    ( spl3_5
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,
    ( spl3_6
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f131,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_6 ),
    inference(forward_demodulation,[],[f130,f117])).

fof(f117,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f61,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f130,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_6 ),
    inference(subsumption_resolution,[],[f129,f99])).

fof(f99,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f56,f66,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f129,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | spl3_6 ),
    inference(subsumption_resolution,[],[f120,f104])).

fof(f104,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f120,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(superposition,[],[f109,f52])).

fof(f109,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f1344,plain,
    ( spl3_29
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f175,f59,f1341])).

fof(f1341,plain,
    ( spl3_29
  <=> k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f175,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(sK2,sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f174,f94])).

fof(f174,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f159,f70])).

fof(f159,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f61,f45])).

fof(f1339,plain,
    ( spl3_28
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f173,f64,f59,f1336])).

fof(f1336,plain,
    ( spl3_28
  <=> k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f173,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f172,f95])).

fof(f95,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f48])).

fof(f172,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f160,f70])).

fof(f160,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f61,f45])).

fof(f1334,plain,
    ( spl3_27
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f171,f64,f59,f1331])).

fof(f1331,plain,
    ( spl3_27
  <=> k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f1329,plain,
    ( spl3_26
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f169,f64,f1326])).

fof(f1326,plain,
    ( spl3_26
  <=> k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f169,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f168,f95])).

fof(f168,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f162,f71])).

fof(f162,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f66,f45])).

fof(f1308,plain,
    ( spl3_25
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1255,f1226,f1305])).

fof(f1305,plain,
    ( spl3_25
  <=> r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f1255,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f40,f1228,f50])).

fof(f1290,plain,
    ( spl3_24
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1254,f1226,f1287])).

fof(f1287,plain,
    ( spl3_24
  <=> r1_tarski(k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1254,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f1228,f1228,f50])).

fof(f1281,plain,
    ( spl3_23
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f119,f64,f1278])).

fof(f1278,plain,
    ( spl3_23
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f119,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f66,f52])).

fof(f1276,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f118,f64,f59,f1273])).

fof(f1273,plain,
    ( spl3_22
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f118,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f61,f66,f52])).

fof(f1271,plain,
    ( spl3_21
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1252,f1226,f1268])).

fof(f1268,plain,
    ( spl3_21
  <=> r1_tarski(k2_xboole_0(sK2,sK1),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1252,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK1),k2_xboole_0(sK1,sK2))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f40,f1228,f50])).

fof(f1266,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f117,f64,f59,f1263])).

fof(f1263,plain,
    ( spl3_20
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f1261,plain,
    ( spl3_19
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f116,f59,f1258])).

fof(f1258,plain,
    ( spl3_19
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f116,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f61,f52])).

fof(f1249,plain,
    ( spl3_18
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f59,f1246])).

fof(f1246,plain,
    ( spl3_18
  <=> sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f82,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f76,f70])).

fof(f76,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f43])).

fof(f1244,plain,
    ( spl3_17
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f81,f64,f1241])).

fof(f1241,plain,
    ( spl3_17
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1239,plain,
    ( spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f71,f64,f1236])).

fof(f1236,plain,
    ( spl3_16
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1234,plain,
    ( spl3_15
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f70,f59,f1231])).

fof(f1231,plain,
    ( spl3_15
  <=> k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1229,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f1211,f819,f249,f89,f59,f1226])).

fof(f819,plain,
    ( spl3_13
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1211,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1210,f82])).

fof(f1210,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1209,f654])).

fof(f654,plain,
    ( k2_xboole_0(sK1,sK2) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f547,f546])).

fof(f546,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f251,f42])).

fof(f547,plain,
    ( k2_xboole_0(sK1,sK2) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f251,f43])).

fof(f1209,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1208,f941])).

fof(f941,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f940,f921])).

fof(f921,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X0))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f863,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f863,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f91,f48])).

fof(f940,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f853,f70])).

fof(f853,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f61,f91,f45])).

fof(f1208,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1013,f864])).

fof(f864,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f91,f49])).

fof(f1013,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f91,f821,f44])).

fof(f821,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f819])).

fof(f822,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f59,f819])).

fof(f75,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f68,f70])).

fof(f68,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f257,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f128,f59,f254])).

fof(f254,plain,
    ( spl3_12
  <=> m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f128,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f111,f116])).

fof(f111,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f61,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f252,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f126,f64,f59,f249])).

fof(f126,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f112,f117])).

fof(f112,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f61,f51])).

fof(f247,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f125,f64,f59,f244])).

fof(f244,plain,
    ( spl3_10
  <=> m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f125,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f113,f118])).

fof(f113,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f61,f66,f51])).

fof(f242,plain,
    ( spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f124,f64,f239])).

fof(f239,plain,
    ( spl3_9
  <=> m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f124,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f114,f119])).

fof(f114,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f66,f51])).

fof(f141,plain,
    ( ~ spl3_8
    | ~ spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(avatar_split_clause,[],[f127,f107,f64,f59,f138])).

fof(f138,plain,
    ( spl3_8
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f127,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(backward_demodulation,[],[f109,f117])).

fof(f136,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f99,f64,f54,f133])).

fof(f133,plain,
    ( spl3_7
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f36,f107])).

fof(f36,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f105,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f98,f59,f54,f102])).

fof(f98,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f56,f61,f46])).

fof(f92,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f74,f64,f89])).

fof(f74,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f69,f71])).

fof(f69,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f66,f41])).

fof(f67,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f64])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f54])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:20:38 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.22/0.47  % (25680)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.49  % (25682)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.49  % (25674)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.49  % (25687)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.49  % (25693)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.49  % (25674)Refutation not found, incomplete strategy% (25674)------------------------------
% 0.22/0.49  % (25674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25674)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25674)Memory used [KB]: 10490
% 0.22/0.49  % (25674)Time elapsed: 0.085 s
% 0.22/0.49  % (25674)------------------------------
% 0.22/0.49  % (25674)------------------------------
% 0.22/0.49  % (25685)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.50  % (25672)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (25673)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (25675)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (25683)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (25691)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.50  % (25681)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (25677)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (25692)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (25678)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (25690)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (25689)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (25676)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  % (25671)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (25694)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (25695)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (25695)Refutation not found, incomplete strategy% (25695)------------------------------
% 0.22/0.52  % (25695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25695)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25695)Memory used [KB]: 10618
% 0.22/0.52  % (25695)Time elapsed: 0.116 s
% 0.22/0.52  % (25695)------------------------------
% 0.22/0.52  % (25695)------------------------------
% 0.22/0.52  % (25684)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (25688)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.54  % (25686)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 2.33/0.66  % (25694)Refutation not found, incomplete strategy% (25694)------------------------------
% 2.33/0.66  % (25694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.66  % (25694)Termination reason: Refutation not found, incomplete strategy
% 2.33/0.66  
% 2.33/0.66  % (25694)Memory used [KB]: 1663
% 2.33/0.66  % (25694)Time elapsed: 0.237 s
% 2.33/0.66  % (25694)------------------------------
% 2.33/0.66  % (25694)------------------------------
% 2.82/0.75  % (25687)Refutation found. Thanks to Tanya!
% 2.82/0.75  % SZS status Theorem for theBenchmark
% 2.82/0.75  % SZS output start Proof for theBenchmark
% 2.82/0.75  fof(f1434,plain,(
% 2.82/0.75    $false),
% 2.82/0.75    inference(avatar_sat_refutation,[],[f57,f62,f67,f92,f105,f110,f136,f141,f242,f247,f252,f257,f822,f1229,f1234,f1239,f1244,f1249,f1261,f1266,f1271,f1276,f1281,f1290,f1308,f1329,f1334,f1339,f1344,f1404,f1409,f1414,f1419,f1424,f1429,f1433])).
% 2.82/0.75  fof(f1433,plain,(
% 2.82/0.75    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_11 | ~spl3_14 | spl3_30),
% 2.82/0.75    inference(avatar_contradiction_clause,[],[f1432])).
% 2.82/0.75  fof(f1432,plain,(
% 2.82/0.75    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_11 | ~spl3_14 | spl3_30)),
% 2.82/0.75    inference(subsumption_resolution,[],[f1431,f543])).
% 2.82/0.75  fof(f543,plain,(
% 2.82/0.75    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_3 | ~spl3_11)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f56,f40,f66,f251,f39])).
% 2.82/0.75  fof(f39,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f19])).
% 2.82/0.75  fof(f19,plain,(
% 2.82/0.75    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.82/0.75    inference(flattening,[],[f18])).
% 2.82/0.75  fof(f18,plain,(
% 2.82/0.75    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f14])).
% 2.82/0.75  fof(f14,axiom,(
% 2.82/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 2.82/0.75  fof(f251,plain,(
% 2.82/0.75    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_11),
% 2.82/0.75    inference(avatar_component_clause,[],[f249])).
% 2.82/0.75  fof(f249,plain,(
% 2.82/0.75    spl3_11 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.82/0.75  fof(f66,plain,(
% 2.82/0.75    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.82/0.75    inference(avatar_component_clause,[],[f64])).
% 2.82/0.75  fof(f64,plain,(
% 2.82/0.75    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.82/0.75  fof(f40,plain,(
% 2.82/0.75    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f2])).
% 2.82/0.75  fof(f2,axiom,(
% 2.82/0.75    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.82/0.75  fof(f56,plain,(
% 2.82/0.75    l1_pre_topc(sK0) | ~spl3_1),
% 2.82/0.75    inference(avatar_component_clause,[],[f54])).
% 2.82/0.75  fof(f54,plain,(
% 2.82/0.75    spl3_1 <=> l1_pre_topc(sK0)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.82/0.75  fof(f1431,plain,(
% 2.82/0.75    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_14 | spl3_30)),
% 2.82/0.75    inference(subsumption_resolution,[],[f1430,f1250])).
% 2.82/0.75  fof(f1250,plain,(
% 2.82/0.75    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_14)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f56,f61,f251,f1228,f39])).
% 2.82/0.75  fof(f1228,plain,(
% 2.82/0.75    r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~spl3_14),
% 2.82/0.75    inference(avatar_component_clause,[],[f1226])).
% 2.82/0.75  fof(f1226,plain,(
% 2.82/0.75    spl3_14 <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.82/0.75  fof(f61,plain,(
% 2.82/0.75    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.82/0.75    inference(avatar_component_clause,[],[f59])).
% 2.82/0.75  fof(f59,plain,(
% 2.82/0.75    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.82/0.75  fof(f1430,plain,(
% 2.82/0.75    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_30),
% 2.82/0.75    inference(resolution,[],[f1403,f50])).
% 2.82/0.75  fof(f50,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f30])).
% 2.82/0.75  fof(f30,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.82/0.75    inference(flattening,[],[f29])).
% 2.82/0.75  fof(f29,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.82/0.75    inference(ennf_transformation,[],[f3])).
% 2.82/0.75  fof(f3,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.82/0.75  fof(f1403,plain,(
% 2.82/0.75    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_30),
% 2.82/0.75    inference(avatar_component_clause,[],[f1401])).
% 2.82/0.75  fof(f1401,plain,(
% 2.82/0.75    spl3_30 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.82/0.75  fof(f1429,plain,(
% 2.82/0.75    spl3_35 | ~spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f158,f59,f1426])).
% 2.82/0.75  fof(f1426,plain,(
% 2.82/0.75    spl3_35 <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK2)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 2.82/0.75  fof(f158,plain,(
% 2.82/0.75    r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK2))) | ~spl3_2),
% 2.82/0.75    inference(forward_demodulation,[],[f143,f70])).
% 2.82/0.75  fof(f70,plain,(
% 2.82/0.75    k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f42])).
% 2.82/0.75  fof(f42,plain,(
% 2.82/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f21])).
% 2.82/0.75  fof(f21,plain,(
% 2.82/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f5])).
% 2.82/0.75  fof(f5,axiom,(
% 2.82/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.82/0.75  fof(f143,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK2))) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f61,f44])).
% 2.82/0.75  fof(f44,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f23])).
% 2.82/0.75  fof(f23,plain,(
% 2.82/0.75    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f12])).
% 2.82/0.75  fof(f12,axiom,(
% 2.82/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).
% 2.82/0.75  fof(f1424,plain,(
% 2.82/0.75    spl3_34 | ~spl3_2 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f157,f64,f59,f1421])).
% 2.82/0.75  fof(f1421,plain,(
% 2.82/0.75    spl3_34 <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.82/0.75  fof(f157,plain,(
% 2.82/0.75    r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(forward_demodulation,[],[f144,f71])).
% 2.82/0.75  fof(f71,plain,(
% 2.82/0.75    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f42])).
% 2.82/0.75  fof(f144,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f61,f44])).
% 2.82/0.75  fof(f1419,plain,(
% 2.82/0.75    spl3_33 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 2.82/0.75    inference(avatar_split_clause,[],[f979,f89,f64,f59,f1416])).
% 2.82/0.75  fof(f1416,plain,(
% 2.82/0.75    spl3_33 <=> r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK2,sK1)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.82/0.75  fof(f89,plain,(
% 2.82/0.75    spl3_4 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.82/0.75  fof(f979,plain,(
% 2.82/0.75    r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK2,sK1))) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.82/0.75    inference(forward_demodulation,[],[f978,f81])).
% 2.82/0.75  fof(f81,plain,(
% 2.82/0.75    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl3_3),
% 2.82/0.75    inference(forward_demodulation,[],[f77,f71])).
% 2.82/0.75  fof(f77,plain,(
% 2.82/0.75    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f43])).
% 2.82/0.75  fof(f43,plain,(
% 2.82/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.82/0.75    inference(cnf_transformation,[],[f22])).
% 2.82/0.75  fof(f22,plain,(
% 2.82/0.75    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f8])).
% 2.82/0.75  fof(f8,axiom,(
% 2.82/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.82/0.75  fof(f978,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK2,sK1))) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.82/0.75    inference(forward_demodulation,[],[f977,f171])).
% 2.82/0.75  fof(f171,plain,(
% 2.82/0.75    k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(forward_demodulation,[],[f170,f94])).
% 2.82/0.75  fof(f94,plain,(
% 2.82/0.75    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)) ) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f48])).
% 2.82/0.75  fof(f48,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f27])).
% 2.82/0.75  fof(f27,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f10])).
% 2.82/0.75  fof(f10,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.82/0.75  fof(f170,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(forward_demodulation,[],[f161,f71])).
% 2.82/0.75  fof(f161,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f66,f45])).
% 2.82/0.75  fof(f45,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f24])).
% 2.82/0.75  fof(f24,plain,(
% 2.82/0.75    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f11])).
% 2.82/0.75  fof(f11,axiom,(
% 2.82/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 2.82/0.75  fof(f977,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl3_2 | ~spl3_4)),
% 2.82/0.75    inference(forward_demodulation,[],[f835,f96])).
% 2.82/0.75  fof(f96,plain,(
% 2.82/0.75    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)) ) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f49])).
% 2.82/0.75  fof(f49,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f28])).
% 2.82/0.75  fof(f28,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f4])).
% 2.82/0.75  fof(f4,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 2.82/0.75  fof(f835,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2))) | (~spl3_2 | ~spl3_4)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f91,f44])).
% 2.82/0.75  fof(f91,plain,(
% 2.82/0.75    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 2.82/0.75    inference(avatar_component_clause,[],[f89])).
% 2.82/0.75  fof(f1414,plain,(
% 2.82/0.75    spl3_32 | ~spl3_2 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f156,f64,f59,f1411])).
% 2.82/0.75  fof(f1411,plain,(
% 2.82/0.75    spl3_32 <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.82/0.75  fof(f156,plain,(
% 2.82/0.75    r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(forward_demodulation,[],[f155,f70])).
% 2.82/0.75  fof(f155,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(forward_demodulation,[],[f145,f97])).
% 2.82/0.75  fof(f97,plain,(
% 2.82/0.75    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f49])).
% 2.82/0.75  fof(f145,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK1))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f66,f44])).
% 2.82/0.75  fof(f1409,plain,(
% 2.82/0.75    spl3_31 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f154,f64,f1406])).
% 2.82/0.75  fof(f1406,plain,(
% 2.82/0.75    spl3_31 <=> r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK1)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.82/0.75  fof(f154,plain,(
% 2.82/0.75    r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK1))) | ~spl3_3),
% 2.82/0.75    inference(forward_demodulation,[],[f146,f71])).
% 2.82/0.75  fof(f146,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK1))) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f66,f44])).
% 2.82/0.75  fof(f1404,plain,(
% 2.82/0.75    ~spl3_30 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | spl3_6),
% 2.82/0.75    inference(avatar_split_clause,[],[f131,f107,f102,f64,f59,f54,f1401])).
% 2.82/0.75  fof(f102,plain,(
% 2.82/0.75    spl3_5 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.82/0.75  fof(f107,plain,(
% 2.82/0.75    spl3_6 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.82/0.75  fof(f131,plain,(
% 2.82/0.75    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | spl3_6)),
% 2.82/0.75    inference(forward_demodulation,[],[f130,f117])).
% 2.82/0.75  fof(f117,plain,(
% 2.82/0.75    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f61,f52])).
% 2.82/0.75  fof(f52,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f34])).
% 2.82/0.75  fof(f34,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(flattening,[],[f33])).
% 2.82/0.75  fof(f33,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.82/0.75    inference(ennf_transformation,[],[f9])).
% 2.82/0.75  fof(f9,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.82/0.75  fof(f130,plain,(
% 2.82/0.75    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_6)),
% 2.82/0.75    inference(subsumption_resolution,[],[f129,f99])).
% 2.82/0.75  fof(f99,plain,(
% 2.82/0.75    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f56,f66,f46])).
% 2.82/0.75  fof(f46,plain,(
% 2.82/0.75    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f26])).
% 2.82/0.75  fof(f26,plain,(
% 2.82/0.75    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.82/0.75    inference(flattening,[],[f25])).
% 2.82/0.75  fof(f25,plain,(
% 2.82/0.75    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f13])).
% 2.82/0.75  fof(f13,axiom,(
% 2.82/0.75    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 2.82/0.75  fof(f129,plain,(
% 2.82/0.75    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_5 | spl3_6)),
% 2.82/0.75    inference(subsumption_resolution,[],[f120,f104])).
% 2.82/0.75  fof(f104,plain,(
% 2.82/0.75    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 2.82/0.75    inference(avatar_component_clause,[],[f102])).
% 2.82/0.75  fof(f120,plain,(
% 2.82/0.75    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_6),
% 2.82/0.75    inference(superposition,[],[f109,f52])).
% 2.82/0.75  fof(f109,plain,(
% 2.82/0.75    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_6),
% 2.82/0.75    inference(avatar_component_clause,[],[f107])).
% 2.82/0.75  fof(f1344,plain,(
% 2.82/0.75    spl3_29 | ~spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f175,f59,f1341])).
% 2.82/0.75  fof(f1341,plain,(
% 2.82/0.75    spl3_29 <=> k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(sK2,sK2)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.82/0.75  fof(f175,plain,(
% 2.82/0.75    k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(sK2,sK2) | ~spl3_2),
% 2.82/0.75    inference(forward_demodulation,[],[f174,f94])).
% 2.82/0.75  fof(f174,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) | ~spl3_2),
% 2.82/0.75    inference(forward_demodulation,[],[f159,f70])).
% 2.82/0.75  fof(f159,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f61,f45])).
% 2.82/0.75  fof(f1339,plain,(
% 2.82/0.75    spl3_28 | ~spl3_2 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f173,f64,f59,f1336])).
% 2.82/0.75  fof(f1336,plain,(
% 2.82/0.75    spl3_28 <=> k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(sK1,sK2)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.82/0.75  fof(f173,plain,(
% 2.82/0.75    k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(forward_demodulation,[],[f172,f95])).
% 2.82/0.75  fof(f95,plain,(
% 2.82/0.75    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f48])).
% 2.82/0.75  fof(f172,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(forward_demodulation,[],[f160,f70])).
% 2.82/0.75  fof(f160,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f61,f45])).
% 2.82/0.75  fof(f1334,plain,(
% 2.82/0.75    spl3_27 | ~spl3_2 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f171,f64,f59,f1331])).
% 2.82/0.75  fof(f1331,plain,(
% 2.82/0.75    spl3_27 <=> k9_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK2,sK1)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.82/0.75  fof(f1329,plain,(
% 2.82/0.75    spl3_26 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f169,f64,f1326])).
% 2.82/0.75  fof(f1326,plain,(
% 2.82/0.75    spl3_26 <=> k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.82/0.75  fof(f169,plain,(
% 2.82/0.75    k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1) | ~spl3_3),
% 2.82/0.75    inference(forward_demodulation,[],[f168,f95])).
% 2.82/0.75  fof(f168,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl3_3),
% 2.82/0.75    inference(forward_demodulation,[],[f162,f71])).
% 2.82/0.75  fof(f162,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f66,f45])).
% 2.82/0.75  fof(f1308,plain,(
% 2.82/0.75    spl3_25 | ~spl3_14),
% 2.82/0.75    inference(avatar_split_clause,[],[f1255,f1226,f1305])).
% 2.82/0.75  fof(f1305,plain,(
% 2.82/0.75    spl3_25 <=> r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.82/0.75  fof(f1255,plain,(
% 2.82/0.75    r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) | ~spl3_14),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f40,f1228,f50])).
% 2.82/0.75  fof(f1290,plain,(
% 2.82/0.75    spl3_24 | ~spl3_14),
% 2.82/0.75    inference(avatar_split_clause,[],[f1254,f1226,f1287])).
% 2.82/0.75  fof(f1287,plain,(
% 2.82/0.75    spl3_24 <=> r1_tarski(k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.82/0.75  fof(f1254,plain,(
% 2.82/0.75    r1_tarski(k2_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) | ~spl3_14),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f1228,f1228,f50])).
% 2.82/0.75  fof(f1281,plain,(
% 2.82/0.75    spl3_23 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f119,f64,f1278])).
% 2.82/0.75  fof(f1278,plain,(
% 2.82/0.75    spl3_23 <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.82/0.75  fof(f119,plain,(
% 2.82/0.75    k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f66,f52])).
% 2.82/0.75  fof(f1276,plain,(
% 2.82/0.75    spl3_22 | ~spl3_2 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f118,f64,f59,f1273])).
% 2.82/0.75  fof(f1273,plain,(
% 2.82/0.75    spl3_22 <=> k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.82/0.75  fof(f118,plain,(
% 2.82/0.75    k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f66,f52])).
% 2.82/0.75  fof(f1271,plain,(
% 2.82/0.75    spl3_21 | ~spl3_14),
% 2.82/0.75    inference(avatar_split_clause,[],[f1252,f1226,f1268])).
% 2.82/0.75  fof(f1268,plain,(
% 2.82/0.75    spl3_21 <=> r1_tarski(k2_xboole_0(sK2,sK1),k2_xboole_0(sK1,sK2))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.82/0.75  fof(f1252,plain,(
% 2.82/0.75    r1_tarski(k2_xboole_0(sK2,sK1),k2_xboole_0(sK1,sK2)) | ~spl3_14),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f40,f1228,f50])).
% 2.82/0.75  fof(f1266,plain,(
% 2.82/0.75    spl3_20 | ~spl3_2 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f117,f64,f59,f1263])).
% 2.82/0.75  fof(f1263,plain,(
% 2.82/0.75    spl3_20 <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.82/0.75  fof(f1261,plain,(
% 2.82/0.75    spl3_19 | ~spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f116,f59,f1258])).
% 2.82/0.75  fof(f1258,plain,(
% 2.82/0.75    spl3_19 <=> k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.82/0.75  fof(f116,plain,(
% 2.82/0.75    k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f61,f52])).
% 2.82/0.75  fof(f1249,plain,(
% 2.82/0.75    spl3_18 | ~spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f82,f59,f1246])).
% 2.82/0.75  fof(f1246,plain,(
% 2.82/0.75    spl3_18 <=> sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.82/0.75  fof(f82,plain,(
% 2.82/0.75    sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) | ~spl3_2),
% 2.82/0.75    inference(forward_demodulation,[],[f76,f70])).
% 2.82/0.75  fof(f76,plain,(
% 2.82/0.75    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f43])).
% 2.82/0.75  fof(f1244,plain,(
% 2.82/0.75    spl3_17 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f81,f64,f1241])).
% 2.82/0.75  fof(f1241,plain,(
% 2.82/0.75    spl3_17 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.82/0.75  fof(f1239,plain,(
% 2.82/0.75    spl3_16 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f71,f64,f1236])).
% 2.82/0.75  fof(f1236,plain,(
% 2.82/0.75    spl3_16 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.82/0.75  fof(f1234,plain,(
% 2.82/0.75    spl3_15 | ~spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f70,f59,f1231])).
% 2.82/0.75  fof(f1231,plain,(
% 2.82/0.75    spl3_15 <=> k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.82/0.75  fof(f1229,plain,(
% 2.82/0.75    spl3_14 | ~spl3_2 | ~spl3_4 | ~spl3_11 | ~spl3_13),
% 2.82/0.75    inference(avatar_split_clause,[],[f1211,f819,f249,f89,f59,f1226])).
% 2.82/0.75  fof(f819,plain,(
% 2.82/0.75    spl3_13 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.82/0.75  fof(f1211,plain,(
% 2.82/0.75    r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_11 | ~spl3_13)),
% 2.82/0.75    inference(forward_demodulation,[],[f1210,f82])).
% 2.82/0.75  fof(f1210,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_11 | ~spl3_13)),
% 2.82/0.75    inference(forward_demodulation,[],[f1209,f654])).
% 2.82/0.75  fof(f654,plain,(
% 2.82/0.75    k2_xboole_0(sK1,sK2) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) | ~spl3_11),
% 2.82/0.75    inference(backward_demodulation,[],[f547,f546])).
% 2.82/0.75  fof(f546,plain,(
% 2.82/0.75    k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) | ~spl3_11),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f251,f42])).
% 2.82/0.75  fof(f547,plain,(
% 2.82/0.75    k2_xboole_0(sK1,sK2) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) | ~spl3_11),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f251,f43])).
% 2.82/0.75  fof(f1209,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)))) | (~spl3_2 | ~spl3_4 | ~spl3_13)),
% 2.82/0.75    inference(forward_demodulation,[],[f1208,f941])).
% 2.82/0.75  fof(f941,plain,(
% 2.82/0.75    k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) | (~spl3_2 | ~spl3_4)),
% 2.82/0.75    inference(forward_demodulation,[],[f940,f921])).
% 2.82/0.75  fof(f921,plain,(
% 2.82/0.75    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X0))) ) | ~spl3_4),
% 2.82/0.75    inference(forward_demodulation,[],[f863,f47])).
% 2.82/0.75  fof(f47,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f1])).
% 2.82/0.75  fof(f1,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.82/0.75  fof(f863,plain,(
% 2.82/0.75    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0)) ) | ~spl3_4),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f91,f48])).
% 2.82/0.75  fof(f940,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) | (~spl3_2 | ~spl3_4)),
% 2.82/0.75    inference(forward_demodulation,[],[f853,f70])).
% 2.82/0.75  fof(f853,plain,(
% 2.82/0.75    k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) | (~spl3_2 | ~spl3_4)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f91,f45])).
% 2.82/0.75  fof(f1208,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)))) | (~spl3_4 | ~spl3_13)),
% 2.82/0.75    inference(forward_demodulation,[],[f1013,f864])).
% 2.82/0.75  fof(f864,plain,(
% 2.82/0.75    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)) ) | ~spl3_4),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f91,f49])).
% 2.82/0.75  fof(f1013,plain,(
% 2.82/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl3_4 | ~spl3_13)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f91,f821,f44])).
% 2.82/0.75  fof(f821,plain,(
% 2.82/0.75    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_13),
% 2.82/0.75    inference(avatar_component_clause,[],[f819])).
% 2.82/0.75  fof(f822,plain,(
% 2.82/0.75    spl3_13 | ~spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f75,f59,f819])).
% 2.82/0.75  fof(f75,plain,(
% 2.82/0.75    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.82/0.75    inference(backward_demodulation,[],[f68,f70])).
% 2.82/0.75  fof(f68,plain,(
% 2.82/0.75    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f41])).
% 2.82/0.75  fof(f41,plain,(
% 2.82/0.75    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f20])).
% 2.82/0.75  fof(f20,plain,(
% 2.82/0.75    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f6])).
% 2.82/0.75  fof(f6,axiom,(
% 2.82/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.82/0.75  fof(f257,plain,(
% 2.82/0.75    spl3_12 | ~spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f128,f59,f254])).
% 2.82/0.75  fof(f254,plain,(
% 2.82/0.75    spl3_12 <=> m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.82/0.75  fof(f128,plain,(
% 2.82/0.75    m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.82/0.75    inference(backward_demodulation,[],[f111,f116])).
% 2.82/0.75  fof(f111,plain,(
% 2.82/0.75    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f61,f51])).
% 2.82/0.75  fof(f51,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f32])).
% 2.82/0.75  fof(f32,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.82/0.75    inference(flattening,[],[f31])).
% 2.82/0.75  fof(f31,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.82/0.75    inference(ennf_transformation,[],[f7])).
% 2.82/0.75  fof(f7,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.82/0.75  fof(f252,plain,(
% 2.82/0.75    spl3_11 | ~spl3_2 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f126,f64,f59,f249])).
% 2.82/0.75  fof(f126,plain,(
% 2.82/0.75    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(backward_demodulation,[],[f112,f117])).
% 2.82/0.75  fof(f112,plain,(
% 2.82/0.75    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f61,f51])).
% 2.82/0.75  fof(f247,plain,(
% 2.82/0.75    spl3_10 | ~spl3_2 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f125,f64,f59,f244])).
% 2.82/0.75  fof(f244,plain,(
% 2.82/0.75    spl3_10 <=> m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.82/0.75  fof(f125,plain,(
% 2.82/0.75    m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(backward_demodulation,[],[f113,f118])).
% 2.82/0.75  fof(f113,plain,(
% 2.82/0.75    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f61,f66,f51])).
% 2.82/0.75  fof(f242,plain,(
% 2.82/0.75    spl3_9 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f124,f64,f239])).
% 2.82/0.75  fof(f239,plain,(
% 2.82/0.75    spl3_9 <=> m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.82/0.75  fof(f124,plain,(
% 2.82/0.75    m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.82/0.75    inference(backward_demodulation,[],[f114,f119])).
% 2.82/0.75  fof(f114,plain,(
% 2.82/0.75    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f66,f51])).
% 2.82/0.75  fof(f141,plain,(
% 2.82/0.75    ~spl3_8 | ~spl3_2 | ~spl3_3 | spl3_6),
% 2.82/0.75    inference(avatar_split_clause,[],[f127,f107,f64,f59,f138])).
% 2.82/0.75  fof(f138,plain,(
% 2.82/0.75    spl3_8 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.82/0.75  fof(f127,plain,(
% 2.82/0.75    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3 | spl3_6)),
% 2.82/0.75    inference(backward_demodulation,[],[f109,f117])).
% 2.82/0.75  fof(f136,plain,(
% 2.82/0.75    spl3_7 | ~spl3_1 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f99,f64,f54,f133])).
% 2.82/0.75  fof(f133,plain,(
% 2.82/0.75    spl3_7 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.82/0.75  fof(f110,plain,(
% 2.82/0.75    ~spl3_6),
% 2.82/0.75    inference(avatar_split_clause,[],[f36,f107])).
% 2.82/0.75  fof(f36,plain,(
% 2.82/0.75    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.82/0.75    inference(cnf_transformation,[],[f17])).
% 2.82/0.75  fof(f17,plain,(
% 2.82/0.75    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f16])).
% 2.82/0.75  fof(f16,negated_conjecture,(
% 2.82/0.75    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.82/0.75    inference(negated_conjecture,[],[f15])).
% 2.82/0.75  fof(f15,conjecture,(
% 2.82/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 2.82/0.75  fof(f105,plain,(
% 2.82/0.75    spl3_5 | ~spl3_1 | ~spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f98,f59,f54,f102])).
% 2.82/0.75  fof(f98,plain,(
% 2.82/0.75    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f56,f61,f46])).
% 2.82/0.75  fof(f92,plain,(
% 2.82/0.75    spl3_4 | ~spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f74,f64,f89])).
% 2.82/0.75  fof(f74,plain,(
% 2.82/0.75    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.82/0.75    inference(backward_demodulation,[],[f69,f71])).
% 2.82/0.75  fof(f69,plain,(
% 2.82/0.75    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f66,f41])).
% 2.82/0.75  fof(f67,plain,(
% 2.82/0.75    spl3_3),
% 2.82/0.75    inference(avatar_split_clause,[],[f37,f64])).
% 2.82/0.75  fof(f37,plain,(
% 2.82/0.75    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    inference(cnf_transformation,[],[f17])).
% 2.82/0.75  fof(f62,plain,(
% 2.82/0.75    spl3_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f35,f59])).
% 2.82/0.75  fof(f35,plain,(
% 2.82/0.75    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.82/0.75    inference(cnf_transformation,[],[f17])).
% 2.82/0.75  fof(f57,plain,(
% 2.82/0.75    spl3_1),
% 2.82/0.75    inference(avatar_split_clause,[],[f38,f54])).
% 2.82/0.75  fof(f38,plain,(
% 2.82/0.75    l1_pre_topc(sK0)),
% 2.82/0.75    inference(cnf_transformation,[],[f17])).
% 2.82/0.75  % SZS output end Proof for theBenchmark
% 2.82/0.75  % (25687)------------------------------
% 2.82/0.75  % (25687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.75  % (25687)Termination reason: Refutation
% 2.82/0.75  
% 2.82/0.75  % (25687)Memory used [KB]: 2558
% 2.82/0.75  % (25687)Time elapsed: 0.324 s
% 2.82/0.75  % (25687)------------------------------
% 2.82/0.75  % (25687)------------------------------
% 2.82/0.76  % (25670)Success in time 0.398 s
%------------------------------------------------------------------------------
