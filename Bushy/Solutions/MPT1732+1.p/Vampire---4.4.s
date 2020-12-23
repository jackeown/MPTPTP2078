%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t41_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:14 EDT 2019

% Result     : Theorem 7.03s
% Output     : Refutation 7.03s
% Verified   : 
% Statistics : Number of formulae       :  284 ( 635 expanded)
%              Number of leaves         :   65 ( 271 expanded)
%              Depth                    :   14
%              Number of atoms          : 1106 (3740 expanded)
%              Number of equality atoms :   93 ( 168 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116868,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f163,f177,f184,f191,f198,f226,f233,f240,f247,f272,f290,f297,f305,f392,f436,f538,f543,f559,f579,f597,f604,f695,f1146,f1163,f1223,f1230,f1536,f1841,f1875,f1950,f30277,f30300,f60763,f60869,f60889,f60954,f60961,f66682,f113280,f113285,f114575,f116525,f116867])).

fof(f116867,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k1_xboole_0 ),
    introduced(theory_axiom,[])).

fof(f116525,plain,
    ( ~ spl10_190
    | ~ spl10_460
    | spl10_1027 ),
    inference(avatar_contradiction_clause,[],[f116524])).

fof(f116524,plain,
    ( $false
    | ~ spl10_190
    | ~ spl10_460
    | ~ spl10_1027 ),
    inference(subsumption_resolution,[],[f116177,f113279])).

fof(f113279,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ spl10_1027 ),
    inference(avatar_component_clause,[],[f113278])).

fof(f113278,plain,
    ( spl10_1027
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1027])])).

fof(f116177,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl10_190
    | ~ spl10_460 ),
    inference(superposition,[],[f30205,f1949])).

fof(f1949,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_190 ),
    inference(avatar_component_clause,[],[f1948])).

fof(f1948,plain,
    ( spl10_190
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_190])])).

fof(f30205,plain,
    ( ! [X4] : k3_xboole_0(u1_struct_0(sK3),k3_xboole_0(u1_struct_0(sK1),X4)) = k1_xboole_0
    | ~ spl10_460 ),
    inference(avatar_component_clause,[],[f30204])).

fof(f30204,plain,
    ( spl10_460
  <=> ! [X4] : k3_xboole_0(u1_struct_0(sK3),k3_xboole_0(u1_struct_0(sK1),X4)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_460])])).

fof(f114575,plain,
    ( ~ spl10_178
    | ~ spl10_978
    | spl10_1027 ),
    inference(avatar_contradiction_clause,[],[f114574])).

fof(f114574,plain,
    ( $false
    | ~ spl10_178
    | ~ spl10_978
    | ~ spl10_1027 ),
    inference(subsumption_resolution,[],[f114573,f110])).

fof(f110,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t2_boole)).

fof(f114573,plain,
    ( k3_xboole_0(u1_struct_0(sK1),k1_xboole_0) != k1_xboole_0
    | ~ spl10_178
    | ~ spl10_978
    | ~ spl10_1027 ),
    inference(forward_demodulation,[],[f114185,f1874])).

fof(f1874,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_178 ),
    inference(avatar_component_clause,[],[f1873])).

fof(f1873,plain,
    ( spl10_178
  <=> k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_178])])).

fof(f114185,plain,
    ( k3_xboole_0(u1_struct_0(sK1),k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) != k1_xboole_0
    | ~ spl10_978
    | ~ spl10_1027 ),
    inference(superposition,[],[f113279,f111033])).

fof(f111033,plain,
    ( ! [X2] : k3_xboole_0(X2,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK1),k3_xboole_0(u1_struct_0(sK2),X2))
    | ~ spl10_978 ),
    inference(avatar_component_clause,[],[f111032])).

fof(f111032,plain,
    ( spl10_978
  <=> ! [X2] : k3_xboole_0(X2,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK1),k3_xboole_0(u1_struct_0(sK2),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_978])])).

fof(f113285,plain,
    ( spl10_978
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f62276,f1948,f111032])).

fof(f62276,plain,
    ( ! [X3] : k3_xboole_0(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK1),k3_xboole_0(u1_struct_0(sK2),X3))
    | ~ spl10_190 ),
    inference(superposition,[],[f359,f1949])).

fof(f359,plain,(
    ! [X8,X7,X9] : k3_xboole_0(X7,k3_xboole_0(X8,X9)) = k3_xboole_0(X9,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f140,f124])).

fof(f124,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',commutativity_k3_xboole_0)).

fof(f140,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t16_xboole_1)).

fof(f113280,plain,
    ( ~ spl10_1027
    | spl10_47
    | ~ spl10_74
    | ~ spl10_728 ),
    inference(avatar_split_clause,[],[f113273,f60930,f528,f384,f113278])).

fof(f384,plain,
    ( spl10_47
  <=> ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f528,plain,
    ( spl10_74
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f60930,plain,
    ( spl10_728
  <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_728])])).

fof(f113273,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ spl10_47
    | ~ spl10_74
    | ~ spl10_728 ),
    inference(subsumption_resolution,[],[f60905,f60931])).

fof(f60931,plain,
    ( l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_728 ),
    inference(avatar_component_clause,[],[f60930])).

fof(f60905,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_47
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f60899,f529])).

fof(f529,plain,
    ( l1_struct_0(sK3)
    | ~ spl10_74 ),
    inference(avatar_component_clause,[],[f528])).

fof(f60899,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_47 ),
    inference(resolution,[],[f385,f622])).

fof(f622,plain,(
    ! [X4,X5] :
      ( r1_tsep_1(X5,X4)
      | k3_xboole_0(u1_struct_0(X4),u1_struct_0(X5)) != k1_xboole_0
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X5) ) ),
    inference(resolution,[],[f311,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',d3_tsep_1)).

fof(f311,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k3_xboole_0(X2,X3) != k1_xboole_0 ) ),
    inference(resolution,[],[f135,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',symmetry_r1_xboole_0)).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',d7_xboole_0)).

fof(f385,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f384])).

fof(f66682,plain,
    ( ~ spl10_823
    | spl10_49
    | ~ spl10_74
    | ~ spl10_716
    | ~ spl10_728 ),
    inference(avatar_split_clause,[],[f63033,f60930,f60749,f528,f390,f66679])).

fof(f66679,plain,
    ( spl10_823
  <=> u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_823])])).

fof(f390,plain,
    ( spl10_49
  <=> ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f60749,plain,
    ( spl10_716
  <=> u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_716])])).

fof(f63033,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ spl10_49
    | ~ spl10_74
    | ~ spl10_716
    | ~ spl10_728 ),
    inference(subsumption_resolution,[],[f63032,f391])).

fof(f391,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f390])).

fof(f63032,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_74
    | ~ spl10_716
    | ~ spl10_728 ),
    inference(subsumption_resolution,[],[f63031,f529])).

fof(f63031,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_716
    | ~ spl10_728 ),
    inference(subsumption_resolution,[],[f62935,f60931])).

fof(f62935,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_716 ),
    inference(superposition,[],[f441,f60750])).

fof(f60750,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl10_716 ),
    inference(avatar_component_clause,[],[f60749])).

fof(f441,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != k1_xboole_0
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(resolution,[],[f112,f135])).

fof(f60961,plain,
    ( spl10_9
    | ~ spl10_20
    | ~ spl10_144
    | spl10_733 ),
    inference(avatar_contradiction_clause,[],[f60960])).

fof(f60960,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_144
    | ~ spl10_733 ),
    inference(subsumption_resolution,[],[f60959,f190])).

fof(f190,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl10_9
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f60959,plain,
    ( v2_struct_0(sK2)
    | ~ spl10_20
    | ~ spl10_144
    | ~ spl10_733 ),
    inference(subsumption_resolution,[],[f60957,f232])).

fof(f232,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl10_20
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f60957,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ spl10_144
    | ~ spl10_733 ),
    inference(resolution,[],[f60953,f1535])).

fof(f1535,plain,
    ( ! [X0] :
        ( l1_pre_topc(k2_tsep_1(sK0,sK1,X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl10_144 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f1534,plain,
    ( spl10_144
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(k2_tsep_1(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_144])])).

fof(f60953,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_733 ),
    inference(avatar_component_clause,[],[f60952])).

fof(f60952,plain,
    ( spl10_733
  <=> ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_733])])).

fof(f60954,plain,
    ( ~ spl10_733
    | spl10_729 ),
    inference(avatar_split_clause,[],[f60943,f60933,f60952])).

fof(f60933,plain,
    ( spl10_729
  <=> ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_729])])).

fof(f60943,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_729 ),
    inference(resolution,[],[f60934,f114])).

fof(f114,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',dt_l1_pre_topc)).

fof(f60934,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_729 ),
    inference(avatar_component_clause,[],[f60933])).

fof(f60889,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_7
    | spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_718 ),
    inference(avatar_contradiction_clause,[],[f60888])).

fof(f60888,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_718 ),
    inference(subsumption_resolution,[],[f60887,f162])).

fof(f162,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f60887,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_718 ),
    inference(subsumption_resolution,[],[f60886,f176])).

fof(f176,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl10_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f60886,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_718 ),
    inference(subsumption_resolution,[],[f60885,f183])).

fof(f183,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl10_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f60885,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_718 ),
    inference(subsumption_resolution,[],[f60884,f225])).

fof(f225,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl10_18
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f60884,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_718 ),
    inference(subsumption_resolution,[],[f60883,f190])).

fof(f60883,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_718 ),
    inference(subsumption_resolution,[],[f60881,f232])).

fof(f60881,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_718 ),
    inference(resolution,[],[f60756,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',dt_k2_tsep_1)).

fof(f60756,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_718 ),
    inference(avatar_component_clause,[],[f60755])).

fof(f60755,plain,
    ( spl10_718
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_718])])).

fof(f60869,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_7
    | spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | spl10_721 ),
    inference(avatar_contradiction_clause,[],[f60866])).

fof(f60866,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_721 ),
    inference(unit_resulting_resolution,[],[f162,f176,f183,f190,f225,f232,f60762,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f60762,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl10_721 ),
    inference(avatar_component_clause,[],[f60761])).

fof(f60761,plain,
    ( spl10_721
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_721])])).

fof(f60763,plain,
    ( spl10_716
    | spl10_718
    | ~ spl10_721
    | spl10_49
    | ~ spl10_128 ),
    inference(avatar_split_clause,[],[f59704,f1161,f390,f60761,f60755,f60749])).

fof(f1161,plain,
    ( spl10_128
  <=> ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f59704,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl10_49
    | ~ spl10_128 ),
    inference(resolution,[],[f391,f1162])).

fof(f1162,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) )
    | ~ spl10_128 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f30300,plain,
    ( spl10_460
    | ~ spl10_134 ),
    inference(avatar_split_clause,[],[f29763,f1228,f30204])).

fof(f1228,plain,
    ( spl10_134
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f29763,plain,
    ( ! [X13] : k3_xboole_0(u1_struct_0(sK3),k3_xboole_0(u1_struct_0(sK1),X13)) = k1_xboole_0
    | ~ spl10_134 ),
    inference(forward_demodulation,[],[f29704,f273])).

fof(f273,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f124,f110])).

fof(f29704,plain,
    ( ! [X13] : k3_xboole_0(u1_struct_0(sK3),k3_xboole_0(u1_struct_0(sK1),X13)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0(sK3),k3_xboole_0(u1_struct_0(sK1),X13)))
    | ~ spl10_134 ),
    inference(superposition,[],[f764,f1229])).

fof(f1229,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_134 ),
    inference(avatar_component_clause,[],[f1228])).

fof(f764,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X6,k3_xboole_0(X5,X7)) = k3_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X6,k3_xboole_0(X5,X7))) ),
    inference(superposition,[],[f352,f353])).

fof(f353,plain,(
    ! [X6,X4,X5] : k3_xboole_0(X4,k3_xboole_0(X5,X6)) = k3_xboole_0(k3_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f140,f124])).

fof(f352,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f140,f123])).

fof(f123,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',idempotence_k3_xboole_0)).

fof(f30277,plain,
    ( spl10_460
    | ~ spl10_132 ),
    inference(avatar_split_clause,[],[f29618,f1221,f30204])).

fof(f1221,plain,
    ( spl10_132
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f29618,plain,
    ( ! [X24] : k3_xboole_0(u1_struct_0(sK3),k3_xboole_0(u1_struct_0(sK1),X24)) = k1_xboole_0
    | ~ spl10_132 ),
    inference(forward_demodulation,[],[f29554,f110])).

fof(f29554,plain,
    ( ! [X24] : k3_xboole_0(k3_xboole_0(u1_struct_0(sK1),X24),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK3),k3_xboole_0(u1_struct_0(sK1),X24))
    | ~ spl10_132 ),
    inference(superposition,[],[f837,f1222])).

fof(f1222,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0
    | ~ spl10_132 ),
    inference(avatar_component_clause,[],[f1221])).

fof(f837,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X10,k3_xboole_0(X8,X9)) = k3_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X8)) ),
    inference(superposition,[],[f359,f352])).

fof(f1950,plain,
    ( spl10_190
    | spl10_9
    | ~ spl10_20
    | spl10_25
    | ~ spl10_122 ),
    inference(avatar_split_clause,[],[f1171,f1144,f245,f231,f189,f1948])).

fof(f245,plain,
    ( spl10_25
  <=> ~ r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f1144,plain,
    ( spl10_122
  <=> ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f1171,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_25
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f1170,f190])).

fof(f1170,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_20
    | ~ spl10_25
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f1167,f232])).

fof(f1167,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_25
    | ~ spl10_122 ),
    inference(resolution,[],[f1145,f246])).

fof(f246,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f245])).

fof(f1145,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl10_122 ),
    inference(avatar_component_clause,[],[f1144])).

fof(f1875,plain,
    ( spl10_178
    | ~ spl10_172 ),
    inference(avatar_split_clause,[],[f1850,f1839,f1873])).

fof(f1839,plain,
    ( spl10_172
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_172])])).

fof(f1850,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_172 ),
    inference(resolution,[],[f1840,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f89])).

fof(f1840,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_172 ),
    inference(avatar_component_clause,[],[f1839])).

fof(f1841,plain,
    ( spl10_172
    | ~ spl10_56
    | ~ spl10_74
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f1816,f549,f528,f411,f1839])).

fof(f411,plain,
    ( spl10_56
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f549,plain,
    ( spl10_76
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f1816,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_56
    | ~ spl10_74
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f1815,f550])).

fof(f550,plain,
    ( l1_struct_0(sK2)
    | ~ spl10_76 ),
    inference(avatar_component_clause,[],[f549])).

fof(f1815,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK2)
    | ~ spl10_56
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f1813,f529])).

fof(f1813,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl10_56 ),
    inference(resolution,[],[f412,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f412,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f411])).

fof(f1536,plain,
    ( spl10_144
    | ~ spl10_30
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f719,f693,f270,f1534])).

fof(f270,plain,
    ( spl10_30
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f693,plain,
    ( spl10_92
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f719,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(k2_tsep_1(sK0,sK1,X0)) )
    | ~ spl10_30
    | ~ spl10_92 ),
    inference(resolution,[],[f694,f271])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f270])).

fof(f694,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl10_92 ),
    inference(avatar_component_clause,[],[f693])).

fof(f1230,plain,
    ( spl10_134
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f609,f602,f1228])).

fof(f602,plain,
    ( spl10_80
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f609,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_80 ),
    inference(resolution,[],[f603,f134])).

fof(f603,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f602])).

fof(f1223,plain,
    ( spl10_132
    | ~ spl10_78 ),
    inference(avatar_split_clause,[],[f606,f595,f1221])).

fof(f595,plain,
    ( spl10_78
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f606,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) = k1_xboole_0
    | ~ spl10_78 ),
    inference(resolution,[],[f596,f134])).

fof(f596,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_78 ),
    inference(avatar_component_clause,[],[f595])).

fof(f1163,plain,
    ( spl10_128
    | spl10_1
    | ~ spl10_4
    | spl10_11
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f519,f238,f196,f175,f161,f1161])).

fof(f196,plain,
    ( spl10_11
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f238,plain,
    ( spl10_22
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f519,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f518,f162])).

fof(f518,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f517,f176])).

fof(f517,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f508,f197])).

fof(f197,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f196])).

fof(f508,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_22 ),
    inference(resolution,[],[f498,f239])).

fof(f239,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f238])).

fof(f498,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f497,f145])).

fof(f497,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f496,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f496,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f152,f147])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',d5_tsep_1)).

fof(f1146,plain,
    ( spl10_122
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f513,f224,f182,f175,f161,f1144])).

fof(f513,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f512,f162])).

fof(f512,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f511,f176])).

fof(f511,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f506,f183])).

fof(f506,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_18 ),
    inference(resolution,[],[f498,f225])).

fof(f695,plain,
    ( spl10_92
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f481,f224,f182,f175,f161,f693])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f480,f162])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f479,f176])).

fof(f479,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f474,f183])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_18 ),
    inference(resolution,[],[f147,f225])).

fof(f604,plain,
    ( spl10_80
    | ~ spl10_54
    | ~ spl10_72
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f590,f528,f522,f405,f602])).

fof(f405,plain,
    ( spl10_54
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f522,plain,
    ( spl10_72
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f590,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl10_54
    | ~ spl10_72
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f589,f523])).

fof(f523,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f522])).

fof(f589,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_struct_0(sK1)
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f587,f529])).

fof(f587,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl10_54 ),
    inference(resolution,[],[f406,f111])).

fof(f406,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f405])).

fof(f597,plain,
    ( spl10_78
    | ~ spl10_60
    | ~ spl10_72
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f583,f528,f522,f428,f595])).

fof(f428,plain,
    ( spl10_60
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f583,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_60
    | ~ spl10_72
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f582,f529])).

fof(f582,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | ~ spl10_60
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f580,f523])).

fof(f580,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl10_60 ),
    inference(resolution,[],[f429,f111])).

fof(f429,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f428])).

fof(f579,plain,
    ( spl10_57
    | ~ spl10_62
    | ~ spl10_74
    | ~ spl10_76 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | ~ spl10_57
    | ~ spl10_62
    | ~ spl10_74
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f577,f529])).

fof(f577,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl10_57
    | ~ spl10_62
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f576,f550])).

fof(f576,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl10_57
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f572,f409])).

fof(f409,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl10_57
  <=> ~ r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f572,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl10_62 ),
    inference(resolution,[],[f435,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',symmetry_r1_tsep_1)).

fof(f435,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl10_62
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f559,plain,
    ( ~ spl10_34
    | spl10_77 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | ~ spl10_34
    | ~ spl10_77 ),
    inference(subsumption_resolution,[],[f556,f296])).

fof(f296,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl10_34
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f556,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl10_77 ),
    inference(resolution,[],[f553,f114])).

fof(f553,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl10_77 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl10_77
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f543,plain,
    ( ~ spl10_36
    | spl10_75 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl10_36
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f540,f304])).

fof(f304,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl10_36
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f540,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl10_75 ),
    inference(resolution,[],[f532,f114])).

fof(f532,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl10_75 ),
    inference(avatar_component_clause,[],[f531])).

fof(f531,plain,
    ( spl10_75
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f538,plain,
    ( ~ spl10_32
    | spl10_73 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | ~ spl10_32
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f535,f289])).

fof(f289,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl10_32
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f535,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl10_73 ),
    inference(resolution,[],[f526,f114])).

fof(f526,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f525])).

fof(f525,plain,
    ( spl10_73
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f436,plain,
    ( spl10_54
    | spl10_56
    | spl10_60
    | spl10_62 ),
    inference(avatar_split_clause,[],[f108,f434,f428,f411,f405])).

fof(f108,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,
    ( ( ( ( r1_tsep_1(sK3,sK2)
          | r1_tsep_1(sK3,sK1) )
        & ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) )
      | ( ( r1_tsep_1(sK2,sK3)
          | r1_tsep_1(sK1,sK3) )
        & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f81,f80,f79,f78])).

fof(f78,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                        & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      | ( ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) )
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,sK1) )
                    & ~ r1_tsep_1(X3,k2_tsep_1(X0,sK1,X2)) )
                  | ( ( r1_tsep_1(X2,X3)
                      | r1_tsep_1(sK1,X3) )
                    & ~ r1_tsep_1(k2_tsep_1(X0,sK1,X2),X3) ) )
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,X1) )
                  & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                | ( ( r1_tsep_1(X2,X3)
                    | r1_tsep_1(X1,X3) )
                  & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( ( r1_tsep_1(X3,sK2)
                  | r1_tsep_1(X3,X1) )
                & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,sK2)) )
              | ( ( r1_tsep_1(sK2,X3)
                  | r1_tsep_1(X1,X3) )
                & ~ r1_tsep_1(k2_tsep_1(X0,X1,sK2),X3) ) )
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X3,X1) )
              & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
            | ( ( r1_tsep_1(X2,X3)
                | r1_tsep_1(X1,X3) )
              & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( ( r1_tsep_1(sK3,X2)
              | r1_tsep_1(sK3,X1) )
            & ~ r1_tsep_1(sK3,k2_tsep_1(X0,X1,X2)) )
          | ( ( r1_tsep_1(X2,sK3)
              | r1_tsep_1(X1,sK3) )
            & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),sK3) ) )
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                         => ( ~ r1_tsep_1(X3,X2)
                            & ~ r1_tsep_1(X3,X1) ) )
                        & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                         => ( ~ r1_tsep_1(X2,X3)
                            & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t41_tmap_1)).

fof(f392,plain,
    ( ~ spl10_47
    | ~ spl10_49 ),
    inference(avatar_split_clause,[],[f105,f390,f384])).

fof(f105,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f305,plain,
    ( spl10_36
    | ~ spl10_22
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f279,f270,f238,f303])).

fof(f279,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_22
    | ~ spl10_30 ),
    inference(resolution,[],[f271,f239])).

fof(f297,plain,
    ( spl10_34
    | ~ spl10_20
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f278,f270,f231,f295])).

fof(f278,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_20
    | ~ spl10_30 ),
    inference(resolution,[],[f271,f232])).

fof(f290,plain,
    ( spl10_32
    | ~ spl10_18
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f277,f270,f224,f288])).

fof(f277,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_18
    | ~ spl10_30 ),
    inference(resolution,[],[f271,f225])).

fof(f272,plain,
    ( spl10_30
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f267,f175,f270])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f117,f176])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',dt_m1_pre_topc)).

fof(f247,plain,(
    ~ spl10_25 ),
    inference(avatar_split_clause,[],[f104,f245])).

fof(f104,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f240,plain,(
    spl10_22 ),
    inference(avatar_split_clause,[],[f103,f238])).

fof(f103,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f233,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f101,f231])).

fof(f101,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f226,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f99,f224])).

fof(f99,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f198,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f102,f196])).

fof(f102,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f191,plain,(
    ~ spl10_9 ),
    inference(avatar_split_clause,[],[f100,f189])).

fof(f100,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f184,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f98,f182])).

fof(f98,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f177,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f97,f175])).

fof(f97,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f163,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f95,f161])).

fof(f95,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).
%------------------------------------------------------------------------------
