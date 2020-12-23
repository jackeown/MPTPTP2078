%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t42_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:15 EDT 2019

% Result     : Theorem 7.59s
% Output     : Refutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 560 expanded)
%              Number of leaves         :   58 ( 243 expanded)
%              Depth                    :   14
%              Number of atoms          : 1010 (3534 expanded)
%              Number of equality atoms :   74 ( 128 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f163,f177,f184,f191,f198,f226,f233,f240,f247,f272,f290,f297,f305,f404,f530,f535,f559,f571,f598,f612,f1153,f1171,f1235,f1822,f1824,f3027,f3055,f16566,f16571,f16620,f24316,f24337,f24342,f24455,f111217,f111222,f113373,f131442])).

fof(f131442,plain,
    ( ~ spl10_236
    | ~ spl10_362
    | spl10_447
    | ~ spl10_926 ),
    inference(avatar_contradiction_clause,[],[f131441])).

fof(f131441,plain,
    ( $false
    | ~ spl10_236
    | ~ spl10_362
    | ~ spl10_447
    | ~ spl10_926 ),
    inference(subsumption_resolution,[],[f131440,f24454])).

fof(f24454,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ spl10_447 ),
    inference(avatar_component_clause,[],[f24453])).

fof(f24453,plain,
    ( spl10_447
  <=> u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_447])])).

fof(f131440,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl10_236
    | ~ spl10_362
    | ~ spl10_926 ),
    inference(forward_demodulation,[],[f131439,f110])).

fof(f110,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',t2_boole)).

fof(f131439,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK2),k1_xboole_0)
    | ~ spl10_236
    | ~ spl10_362
    | ~ spl10_926 ),
    inference(forward_demodulation,[],[f131438,f3054])).

fof(f3054,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_236 ),
    inference(avatar_component_clause,[],[f3053])).

fof(f3053,plain,
    ( spl10_236
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_236])])).

fof(f131438,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)))
    | ~ spl10_362
    | ~ spl10_926 ),
    inference(forward_demodulation,[],[f130905,f124])).

fof(f124,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',commutativity_k3_xboole_0)).

fof(f130905,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)))
    | ~ spl10_362
    | ~ spl10_926 ),
    inference(superposition,[],[f16553,f111221])).

fof(f111221,plain,
    ( ! [X3] : k3_xboole_0(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(X3,u1_struct_0(sK1)))
    | ~ spl10_926 ),
    inference(avatar_component_clause,[],[f111220])).

fof(f111220,plain,
    ( spl10_926
  <=> ! [X3] : k3_xboole_0(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(X3,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_926])])).

fof(f16553,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl10_362 ),
    inference(avatar_component_clause,[],[f16552])).

fof(f16552,plain,
    ( spl10_362
  <=> u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_362])])).

fof(f113373,plain,
    ( ~ spl10_134
    | ~ spl10_362
    | spl10_447
    | ~ spl10_924 ),
    inference(avatar_contradiction_clause,[],[f113372])).

fof(f113372,plain,
    ( $false
    | ~ spl10_134
    | ~ spl10_362
    | ~ spl10_447
    | ~ spl10_924 ),
    inference(subsumption_resolution,[],[f113371,f24454])).

fof(f113371,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k1_xboole_0
    | ~ spl10_134
    | ~ spl10_362
    | ~ spl10_924 ),
    inference(forward_demodulation,[],[f113370,f110])).

fof(f113370,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK1),k1_xboole_0)
    | ~ spl10_134
    | ~ spl10_362
    | ~ spl10_924 ),
    inference(forward_demodulation,[],[f112981,f1234])).

fof(f1234,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_134 ),
    inference(avatar_component_clause,[],[f1233])).

fof(f1233,plain,
    ( spl10_134
  <=> k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f112981,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK1),k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_362
    | ~ spl10_924 ),
    inference(superposition,[],[f16553,f111216])).

fof(f111216,plain,
    ( ! [X2] : k3_xboole_0(X2,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK1),k3_xboole_0(u1_struct_0(sK2),X2))
    | ~ spl10_924 ),
    inference(avatar_component_clause,[],[f111215])).

fof(f111215,plain,
    ( spl10_924
  <=> ! [X2] : k3_xboole_0(X2,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK1),k3_xboole_0(u1_struct_0(sK2),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_924])])).

fof(f111222,plain,
    ( spl10_926
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1880,f1820,f111220])).

fof(f1820,plain,
    ( spl10_182
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_182])])).

fof(f1880,plain,
    ( ! [X3] : k3_xboole_0(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(X3,u1_struct_0(sK1)))
    | ~ spl10_182 ),
    inference(superposition,[],[f359,f1821])).

fof(f1821,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_182 ),
    inference(avatar_component_clause,[],[f1820])).

fof(f359,plain,(
    ! [X8,X7,X9] : k3_xboole_0(X7,k3_xboole_0(X8,X9)) = k3_xboole_0(X9,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f140,f124])).

fof(f140,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',t16_xboole_1)).

fof(f111217,plain,
    ( spl10_924
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1879,f1820,f111215])).

fof(f1879,plain,
    ( ! [X2] : k3_xboole_0(X2,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK1),k3_xboole_0(u1_struct_0(sK2),X2))
    | ~ spl10_182 ),
    inference(superposition,[],[f359,f1821])).

fof(f24455,plain,
    ( ~ spl10_447
    | ~ spl10_72
    | spl10_79
    | ~ spl10_362
    | ~ spl10_442 ),
    inference(avatar_split_clause,[],[f24414,f24332,f16552,f564,f520,f24453])).

fof(f520,plain,
    ( spl10_72
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f564,plain,
    ( spl10_79
  <=> ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f24332,plain,
    ( spl10_442
  <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_442])])).

fof(f24414,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ spl10_72
    | ~ spl10_79
    | ~ spl10_362
    | ~ spl10_442 ),
    inference(subsumption_resolution,[],[f24413,f565])).

fof(f565,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f564])).

fof(f24413,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_72
    | ~ spl10_362
    | ~ spl10_442 ),
    inference(subsumption_resolution,[],[f24412,f521])).

fof(f521,plain,
    ( l1_struct_0(sK3)
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f520])).

fof(f24412,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_362
    | ~ spl10_442 ),
    inference(subsumption_resolution,[],[f24347,f24333])).

fof(f24333,plain,
    ( l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_442 ),
    inference(avatar_component_clause,[],[f24332])).

fof(f24347,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) != k1_xboole_0
    | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_362 ),
    inference(superposition,[],[f432,f16553])).

fof(f432,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != k1_xboole_0
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(resolution,[],[f112,f135])).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',d7_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',d3_tsep_1)).

fof(f24342,plain,
    ( ~ spl10_368
    | spl10_443 ),
    inference(avatar_contradiction_clause,[],[f24341])).

fof(f24341,plain,
    ( $false
    | ~ spl10_368
    | ~ spl10_443 ),
    inference(subsumption_resolution,[],[f24339,f16619])).

fof(f16619,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_368 ),
    inference(avatar_component_clause,[],[f16618])).

fof(f16618,plain,
    ( spl10_368
  <=> l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_368])])).

fof(f24339,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_443 ),
    inference(resolution,[],[f24336,f114])).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',dt_l1_pre_topc)).

fof(f24336,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_443 ),
    inference(avatar_component_clause,[],[f24335])).

fof(f24335,plain,
    ( spl10_443
  <=> ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_443])])).

fof(f24337,plain,
    ( ~ spl10_443
    | spl10_55
    | ~ spl10_72
    | ~ spl10_78 ),
    inference(avatar_split_clause,[],[f24330,f561,f520,f410,f24335])).

fof(f410,plain,
    ( spl10_55
  <=> ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f561,plain,
    ( spl10_78
  <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f24330,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_55
    | ~ spl10_72
    | ~ spl10_78 ),
    inference(subsumption_resolution,[],[f24329,f521])).

fof(f24329,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl10_55
    | ~ spl10_78 ),
    inference(subsumption_resolution,[],[f24327,f411])).

fof(f411,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f410])).

fof(f24327,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl10_78 ),
    inference(resolution,[],[f562,f133])).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',symmetry_r1_tsep_1)).

fof(f562,plain,
    ( r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_78 ),
    inference(avatar_component_clause,[],[f561])).

fof(f24316,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_7
    | spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_364 ),
    inference(avatar_contradiction_clause,[],[f24315])).

fof(f24315,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_364 ),
    inference(subsumption_resolution,[],[f24314,f162])).

fof(f162,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f24314,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_364 ),
    inference(subsumption_resolution,[],[f24313,f176])).

fof(f176,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl10_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f24313,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_364 ),
    inference(subsumption_resolution,[],[f24312,f183])).

fof(f183,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl10_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f24312,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_364 ),
    inference(subsumption_resolution,[],[f24311,f225])).

fof(f225,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl10_18
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f24311,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_364 ),
    inference(subsumption_resolution,[],[f24310,f190])).

fof(f190,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl10_9
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f24310,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_364 ),
    inference(subsumption_resolution,[],[f24308,f232])).

fof(f232,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl10_20
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f24308,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_364 ),
    inference(resolution,[],[f16559,f145])).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',dt_k2_tsep_1)).

fof(f16559,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_364 ),
    inference(avatar_component_clause,[],[f16558])).

fof(f16558,plain,
    ( spl10_364
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_364])])).

fof(f16620,plain,
    ( spl10_368
    | ~ spl10_30
    | ~ spl10_366 ),
    inference(avatar_split_clause,[],[f16576,f16561,f270,f16618])).

fof(f270,plain,
    ( spl10_30
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f16561,plain,
    ( spl10_366
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_366])])).

fof(f16576,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl10_30
    | ~ spl10_366 ),
    inference(resolution,[],[f16562,f271])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f270])).

fof(f16562,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl10_366 ),
    inference(avatar_component_clause,[],[f16561])).

fof(f16571,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_7
    | spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | spl10_367 ),
    inference(avatar_contradiction_clause,[],[f16568])).

fof(f16568,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_367 ),
    inference(unit_resulting_resolution,[],[f162,f176,f183,f190,f225,f232,f16565,f147])).

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

fof(f16565,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl10_367 ),
    inference(avatar_component_clause,[],[f16564])).

fof(f16564,plain,
    ( spl10_367
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_367])])).

fof(f16566,plain,
    ( spl10_362
    | spl10_364
    | ~ spl10_367
    | spl10_79
    | ~ spl10_128 ),
    inference(avatar_split_clause,[],[f10384,f1169,f564,f16564,f16558,f16552])).

fof(f1169,plain,
    ( spl10_128
  <=> ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f10384,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK3,k2_tsep_1(sK0,sK1,sK2))) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl10_79
    | ~ spl10_128 ),
    inference(resolution,[],[f565,f1170])).

fof(f1170,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) )
    | ~ spl10_128 ),
    inference(avatar_component_clause,[],[f1169])).

fof(f3055,plain,
    ( spl10_236
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f3036,f3025,f3053])).

fof(f3025,plain,
    ( spl10_232
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_232])])).

fof(f3036,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_232 ),
    inference(resolution,[],[f3026,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f89])).

fof(f3026,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl10_232 ),
    inference(avatar_component_clause,[],[f3025])).

fof(f3027,plain,
    ( spl10_232
    | ~ spl10_46
    | ~ spl10_72
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f2992,f554,f520,f384,f3025])).

fof(f384,plain,
    ( spl10_46
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f554,plain,
    ( spl10_76
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f2992,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl10_46
    | ~ spl10_72
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f2991,f555])).

fof(f555,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_76 ),
    inference(avatar_component_clause,[],[f554])).

fof(f2991,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_struct_0(sK1)
    | ~ spl10_46
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f2989,f521])).

fof(f2989,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl10_46 ),
    inference(resolution,[],[f385,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f385,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f384])).

fof(f1824,plain,
    ( ~ spl10_55
    | ~ spl10_79 ),
    inference(avatar_split_clause,[],[f108,f564,f410])).

fof(f108,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,
    ( ( ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
        & ( r1_tsep_1(sK3,sK2)
          | r1_tsep_1(sK3,sK1) ) )
      | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
        & ( r1_tsep_1(sK2,sK3)
          | r1_tsep_1(sK1,sK3) ) ) )
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
                    ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                        & ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) ) )
                      | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                        & ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) ) ) )
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
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,sK1,X2))
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,sK1) ) )
                  | ( ~ r1_tsep_1(k2_tsep_1(X0,sK1,X2),X3)
                    & ( r1_tsep_1(X2,X3)
                      | r1_tsep_1(sK1,X3) ) ) )
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
              ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,X1) ) )
                | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                  & ( r1_tsep_1(X2,X3)
                    | r1_tsep_1(X1,X3) ) ) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,sK2))
                & ( r1_tsep_1(X3,sK2)
                  | r1_tsep_1(X3,X1) ) )
              | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,sK2),X3)
                & ( r1_tsep_1(sK2,X3)
                  | r1_tsep_1(X1,X3) ) ) )
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X3,X1) ) )
            | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
              & ( r1_tsep_1(X2,X3)
                | r1_tsep_1(X1,X3) ) ) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( ~ r1_tsep_1(sK3,k2_tsep_1(X0,X1,X2))
            & ( r1_tsep_1(sK3,X2)
              | r1_tsep_1(sK3,X1) ) )
          | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),sK3)
            & ( r1_tsep_1(X2,sK3)
              | r1_tsep_1(X1,sK3) ) ) )
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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
                     => ( ( ( r1_tsep_1(X3,X2)
                            | r1_tsep_1(X3,X1) )
                         => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                        & ( ( r1_tsep_1(X2,X3)
                            | r1_tsep_1(X1,X3) )
                         => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
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
                   => ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      & ( ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',t42_tmap_1)).

fof(f1822,plain,
    ( spl10_182
    | spl10_9
    | ~ spl10_20
    | spl10_25
    | ~ spl10_122 ),
    inference(avatar_split_clause,[],[f1176,f1151,f245,f231,f189,f1820])).

fof(f245,plain,
    ( spl10_25
  <=> ~ r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f1151,plain,
    ( spl10_122
  <=> ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f1176,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_25
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f1175,f190])).

fof(f1175,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_20
    | ~ spl10_25
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f1172,f232])).

fof(f1172,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_25
    | ~ spl10_122 ),
    inference(resolution,[],[f1152,f246])).

fof(f246,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f245])).

fof(f1152,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl10_122 ),
    inference(avatar_component_clause,[],[f1151])).

fof(f1235,plain,
    ( spl10_134
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f614,f610,f1233])).

fof(f610,plain,
    ( spl10_80
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f614,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_80 ),
    inference(resolution,[],[f611,f134])).

fof(f611,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f610])).

fof(f1171,plain,
    ( spl10_128
    | spl10_1
    | ~ spl10_4
    | spl10_11
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f505,f238,f196,f175,f161,f1169])).

fof(f196,plain,
    ( spl10_11
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f238,plain,
    ( spl10_22
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f505,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f504,f162])).

fof(f504,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f503,f176])).

fof(f503,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f494,f197])).

fof(f197,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f196])).

fof(f494,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_22 ),
    inference(resolution,[],[f489,f239])).

fof(f239,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f238])).

fof(f489,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f488,f145])).

fof(f488,plain,(
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
    inference(subsumption_resolution,[],[f487,f146])).

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

fof(f487,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',d5_tsep_1)).

fof(f1153,plain,
    ( spl10_122
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f499,f224,f182,f175,f161,f1151])).

fof(f499,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f498,f162])).

fof(f498,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f497,f176])).

fof(f497,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f492,f183])).

fof(f492,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_18 ),
    inference(resolution,[],[f489,f225])).

fof(f612,plain,
    ( spl10_80
    | ~ spl10_48
    | ~ spl10_70
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f602,f520,f514,f390,f610])).

fof(f390,plain,
    ( spl10_48
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f514,plain,
    ( spl10_70
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f602,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_48
    | ~ spl10_70
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f601,f515])).

fof(f515,plain,
    ( l1_struct_0(sK2)
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f514])).

fof(f601,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK2)
    | ~ spl10_48
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f599,f521])).

fof(f599,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl10_48 ),
    inference(resolution,[],[f391,f111])).

fof(f391,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f390])).

fof(f598,plain,
    ( spl10_48
    | ~ spl10_52
    | ~ spl10_70
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f597,f520,f514,f402,f390])).

fof(f402,plain,
    ( spl10_52
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f597,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl10_52
    | ~ spl10_70
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f596,f521])).

fof(f596,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK3)
    | ~ spl10_52
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f593,f515])).

fof(f593,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl10_52 ),
    inference(resolution,[],[f403,f133])).

fof(f403,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f402])).

fof(f571,plain,
    ( ~ spl10_32
    | spl10_77 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | ~ spl10_32
    | ~ spl10_77 ),
    inference(subsumption_resolution,[],[f568,f289])).

fof(f289,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl10_32
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f568,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl10_77 ),
    inference(resolution,[],[f558,f114])).

fof(f558,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl10_77 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl10_77
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f559,plain,
    ( ~ spl10_77
    | spl10_46
    | ~ spl10_50
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f551,f520,f396,f384,f557])).

fof(f396,plain,
    ( spl10_50
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f551,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl10_50
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f549,f521])).

fof(f549,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl10_50 ),
    inference(resolution,[],[f397,f133])).

fof(f397,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f396])).

fof(f535,plain,
    ( ~ spl10_36
    | spl10_73 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | ~ spl10_36
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f532,f304])).

fof(f304,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl10_36
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f532,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl10_73 ),
    inference(resolution,[],[f524,f114])).

fof(f524,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl10_73
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f530,plain,
    ( ~ spl10_34
    | spl10_71 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | ~ spl10_34
    | ~ spl10_71 ),
    inference(subsumption_resolution,[],[f527,f296])).

fof(f296,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl10_34
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f527,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl10_71 ),
    inference(resolution,[],[f518,f114])).

fof(f518,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl10_71 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl10_71
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f404,plain,
    ( spl10_46
    | spl10_48
    | spl10_50
    | spl10_52 ),
    inference(avatar_split_clause,[],[f105,f402,f396,f390,f384])).

fof(f105,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t42_tmap_1.p',dt_m1_pre_topc)).

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
