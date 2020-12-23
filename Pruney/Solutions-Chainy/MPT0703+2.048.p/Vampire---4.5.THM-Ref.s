%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 193 expanded)
%              Number of leaves         :   29 (  88 expanded)
%              Depth                    :    7
%              Number of atoms          :  313 ( 601 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f907,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f56,f60,f64,f68,f72,f76,f80,f88,f116,f128,f140,f198,f533,f763,f779,f827,f845,f904])).

fof(f904,plain,
    ( spl3_1
    | ~ spl3_12
    | ~ spl3_120 ),
    inference(avatar_contradiction_clause,[],[f903])).

fof(f903,plain,
    ( $false
    | spl3_1
    | ~ spl3_12
    | ~ spl3_120 ),
    inference(subsumption_resolution,[],[f877,f35])).

fof(f35,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f877,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_12
    | ~ spl3_120 ),
    inference(superposition,[],[f844,f87])).

fof(f87,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_12
  <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f844,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(sK0,X2),sK1)
    | ~ spl3_120 ),
    inference(avatar_component_clause,[],[f843])).

fof(f843,plain,
    ( spl3_120
  <=> ! [X2] : r1_tarski(k3_xboole_0(sK0,X2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).

fof(f845,plain,
    ( spl3_120
    | ~ spl3_28
    | ~ spl3_118 ),
    inference(avatar_split_clause,[],[f831,f824,f196,f843])).

fof(f196,plain,
    ( spl3_28
  <=> ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,k3_xboole_0(X5,X6))
        | r1_tarski(k3_xboole_0(X4,X7),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f824,plain,
    ( spl3_118
  <=> r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).

fof(f831,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(sK0,X2),sK1)
    | ~ spl3_28
    | ~ spl3_118 ),
    inference(resolution,[],[f826,f197])).

fof(f197,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_tarski(X4,k3_xboole_0(X5,X6))
        | r1_tarski(k3_xboole_0(X4,X7),X5) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f196])).

fof(f826,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ spl3_118 ),
    inference(avatar_component_clause,[],[f824])).

fof(f827,plain,
    ( spl3_118
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_106
    | ~ spl3_109 ),
    inference(avatar_split_clause,[],[f822,f777,f761,f85,f43,f824])).

fof(f43,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f761,plain,
    ( spl3_106
  <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).

fof(f777,plain,
    ( spl3_109
  <=> ! [X5,X4] :
        ( r1_tarski(k9_relat_1(sK2,X5),k3_xboole_0(X4,k2_relat_1(sK2)))
        | ~ r1_tarski(X5,k10_relat_1(sK2,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).

fof(f822,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_106
    | ~ spl3_109 ),
    inference(forward_demodulation,[],[f821,f87])).

fof(f821,plain,
    ( r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ spl3_3
    | ~ spl3_106
    | ~ spl3_109 ),
    inference(forward_demodulation,[],[f791,f762])).

fof(f762,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))
    | ~ spl3_106 ),
    inference(avatar_component_clause,[],[f761])).

fof(f791,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ spl3_3
    | ~ spl3_109 ),
    inference(resolution,[],[f778,f45])).

fof(f45,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f778,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X5,k10_relat_1(sK2,X4))
        | r1_tarski(k9_relat_1(sK2,X5),k3_xboole_0(X4,k2_relat_1(sK2))) )
    | ~ spl3_109 ),
    inference(avatar_component_clause,[],[f777])).

fof(f779,plain,
    ( spl3_109
    | ~ spl3_74
    | ~ spl3_106 ),
    inference(avatar_split_clause,[],[f766,f761,f531,f777])).

fof(f531,plain,
    ( spl3_74
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f766,plain,
    ( ! [X4,X5] :
        ( r1_tarski(k9_relat_1(sK2,X5),k3_xboole_0(X4,k2_relat_1(sK2)))
        | ~ r1_tarski(X5,k10_relat_1(sK2,X4)) )
    | ~ spl3_74
    | ~ spl3_106 ),
    inference(superposition,[],[f532,f762])).

fof(f532,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f531])).

fof(f763,plain,
    ( spl3_106
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f759,f113,f70,f53,f48,f761])).

fof(f48,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f53,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f113,plain,
    ( spl3_17
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f759,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f758,f115])).

fof(f115,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f758,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f757,f55])).

fof(f55,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f757,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f71,f50])).

fof(f50,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        | ~ v1_relat_1(X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f533,plain,
    ( spl3_74
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f529,f74,f53,f531])).

fof(f74,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f529,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f75,f55])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f198,plain,
    ( spl3_28
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f186,f138,f62,f196])).

fof(f62,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f138,plain,
    ( spl3_21
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(k3_xboole_0(X0,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f186,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_tarski(X4,k3_xboole_0(X5,X6))
        | r1_tarski(k3_xboole_0(X4,X7),X5) )
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(resolution,[],[f139,f63])).

fof(f63,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f139,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k3_xboole_0(X0,X3),X2) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl3_21
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f133,f126,f78,f138])).

fof(f78,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f126,plain,
    ( spl3_19
  <=> ! [X3,X2,X4] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k3_xboole_0(X2,X4),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f133,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(k3_xboole_0(X0,X3),X2) )
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(resolution,[],[f127,f79])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f127,plain,
    ( ! [X4,X2,X3] :
        ( r1_tarski(k3_xboole_0(X2,X4),X3)
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl3_19
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f119,f78,f62,f126])).

fof(f119,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k3_xboole_0(X2,X4),X3) )
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f79,f63])).

fof(f116,plain,
    ( spl3_17
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f111,f58,f53,f113])).

fof(f58,plain,
    ( spl3_6
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f111,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f59,f55])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f88,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f81,f66,f38,f85])).

fof(f38,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f66,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f81,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f67,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f80,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f76,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f72,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f68,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f60,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f38])).

fof(f24,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f33])).

fof(f25,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (7191)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (7191)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f907,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f56,f60,f64,f68,f72,f76,f80,f88,f116,f128,f140,f198,f533,f763,f779,f827,f845,f904])).
% 0.21/0.41  fof(f904,plain,(
% 0.21/0.41    spl3_1 | ~spl3_12 | ~spl3_120),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f903])).
% 0.21/0.41  fof(f903,plain,(
% 0.21/0.41    $false | (spl3_1 | ~spl3_12 | ~spl3_120)),
% 0.21/0.41    inference(subsumption_resolution,[],[f877,f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.41  fof(f877,plain,(
% 0.21/0.41    r1_tarski(sK0,sK1) | (~spl3_12 | ~spl3_120)),
% 0.21/0.41    inference(superposition,[],[f844,f87])).
% 0.21/0.41  fof(f87,plain,(
% 0.21/0.41    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_12),
% 0.21/0.41    inference(avatar_component_clause,[],[f85])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    spl3_12 <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.41  fof(f844,plain,(
% 0.21/0.41    ( ! [X2] : (r1_tarski(k3_xboole_0(sK0,X2),sK1)) ) | ~spl3_120),
% 0.21/0.41    inference(avatar_component_clause,[],[f843])).
% 0.21/0.41  fof(f843,plain,(
% 0.21/0.41    spl3_120 <=> ! [X2] : r1_tarski(k3_xboole_0(sK0,X2),sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).
% 0.21/0.41  fof(f845,plain,(
% 0.21/0.41    spl3_120 | ~spl3_28 | ~spl3_118),
% 0.21/0.41    inference(avatar_split_clause,[],[f831,f824,f196,f843])).
% 0.21/0.41  fof(f196,plain,(
% 0.21/0.41    spl3_28 <=> ! [X5,X7,X4,X6] : (~r1_tarski(X4,k3_xboole_0(X5,X6)) | r1_tarski(k3_xboole_0(X4,X7),X5))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.41  fof(f824,plain,(
% 0.21/0.41    spl3_118 <=> r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).
% 0.21/0.41  fof(f831,plain,(
% 0.21/0.41    ( ! [X2] : (r1_tarski(k3_xboole_0(sK0,X2),sK1)) ) | (~spl3_28 | ~spl3_118)),
% 0.21/0.41    inference(resolution,[],[f826,f197])).
% 0.21/0.41  fof(f197,plain,(
% 0.21/0.41    ( ! [X6,X4,X7,X5] : (~r1_tarski(X4,k3_xboole_0(X5,X6)) | r1_tarski(k3_xboole_0(X4,X7),X5)) ) | ~spl3_28),
% 0.21/0.41    inference(avatar_component_clause,[],[f196])).
% 0.21/0.41  fof(f826,plain,(
% 0.21/0.41    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) | ~spl3_118),
% 0.21/0.41    inference(avatar_component_clause,[],[f824])).
% 0.21/0.41  fof(f827,plain,(
% 0.21/0.41    spl3_118 | ~spl3_3 | ~spl3_12 | ~spl3_106 | ~spl3_109),
% 0.21/0.41    inference(avatar_split_clause,[],[f822,f777,f761,f85,f43,f824])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.41  fof(f761,plain,(
% 0.21/0.41    spl3_106 <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).
% 0.21/0.41  fof(f777,plain,(
% 0.21/0.41    spl3_109 <=> ! [X5,X4] : (r1_tarski(k9_relat_1(sK2,X5),k3_xboole_0(X4,k2_relat_1(sK2))) | ~r1_tarski(X5,k10_relat_1(sK2,X4)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).
% 0.21/0.41  fof(f822,plain,(
% 0.21/0.41    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) | (~spl3_3 | ~spl3_12 | ~spl3_106 | ~spl3_109)),
% 0.21/0.41    inference(forward_demodulation,[],[f821,f87])).
% 0.21/0.41  fof(f821,plain,(
% 0.21/0.41    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2))) | (~spl3_3 | ~spl3_106 | ~spl3_109)),
% 0.21/0.41    inference(forward_demodulation,[],[f791,f762])).
% 0.21/0.41  fof(f762,plain,(
% 0.21/0.41    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) ) | ~spl3_106),
% 0.21/0.41    inference(avatar_component_clause,[],[f761])).
% 0.21/0.41  fof(f791,plain,(
% 0.21/0.41    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2))) | (~spl3_3 | ~spl3_109)),
% 0.21/0.41    inference(resolution,[],[f778,f45])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f43])).
% 0.21/0.41  fof(f778,plain,(
% 0.21/0.41    ( ! [X4,X5] : (~r1_tarski(X5,k10_relat_1(sK2,X4)) | r1_tarski(k9_relat_1(sK2,X5),k3_xboole_0(X4,k2_relat_1(sK2)))) ) | ~spl3_109),
% 0.21/0.41    inference(avatar_component_clause,[],[f777])).
% 0.21/0.41  fof(f779,plain,(
% 0.21/0.41    spl3_109 | ~spl3_74 | ~spl3_106),
% 0.21/0.41    inference(avatar_split_clause,[],[f766,f761,f531,f777])).
% 0.21/0.41  fof(f531,plain,(
% 0.21/0.41    spl3_74 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.21/0.41  fof(f766,plain,(
% 0.21/0.41    ( ! [X4,X5] : (r1_tarski(k9_relat_1(sK2,X5),k3_xboole_0(X4,k2_relat_1(sK2))) | ~r1_tarski(X5,k10_relat_1(sK2,X4))) ) | (~spl3_74 | ~spl3_106)),
% 0.21/0.41    inference(superposition,[],[f532,f762])).
% 0.21/0.41  fof(f532,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_74),
% 0.21/0.41    inference(avatar_component_clause,[],[f531])).
% 0.21/0.41  fof(f763,plain,(
% 0.21/0.41    spl3_106 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_17),
% 0.21/0.41    inference(avatar_split_clause,[],[f759,f113,f70,f53,f48,f761])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl3_4 <=> v1_funct_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    spl3_9 <=> ! [X1,X0] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.41  fof(f113,plain,(
% 0.21/0.41    spl3_17 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.41  fof(f759,plain,(
% 0.21/0.41    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) ) | (~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_17)),
% 0.21/0.41    inference(forward_demodulation,[],[f758,f115])).
% 0.21/0.41  fof(f115,plain,(
% 0.21/0.41    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | ~spl3_17),
% 0.21/0.41    inference(avatar_component_clause,[],[f113])).
% 0.21/0.41  fof(f758,plain,(
% 0.21/0.41    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) ) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 0.21/0.41    inference(subsumption_resolution,[],[f757,f55])).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f53])).
% 0.21/0.41  fof(f757,plain,(
% 0.21/0.41    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(sK2)) ) | (~spl3_4 | ~spl3_9)),
% 0.21/0.41    inference(resolution,[],[f71,f50])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    v1_funct_1(sK2) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f48])).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) ) | ~spl3_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f70])).
% 0.21/0.41  fof(f533,plain,(
% 0.21/0.41    spl3_74 | ~spl3_5 | ~spl3_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f529,f74,f53,f531])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.41  fof(f529,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl3_5 | ~spl3_10)),
% 0.21/0.41    inference(resolution,[],[f75,f55])).
% 0.21/0.41  fof(f75,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) | ~spl3_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f74])).
% 0.21/0.41  fof(f198,plain,(
% 0.21/0.41    spl3_28 | ~spl3_7 | ~spl3_21),
% 0.21/0.41    inference(avatar_split_clause,[],[f186,f138,f62,f196])).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    spl3_7 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.41  fof(f138,plain,(
% 0.21/0.41    spl3_21 <=> ! [X1,X3,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(k3_xboole_0(X0,X3),X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.41  fof(f186,plain,(
% 0.21/0.41    ( ! [X6,X4,X7,X5] : (~r1_tarski(X4,k3_xboole_0(X5,X6)) | r1_tarski(k3_xboole_0(X4,X7),X5)) ) | (~spl3_7 | ~spl3_21)),
% 0.21/0.41    inference(resolution,[],[f139,f63])).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f62])).
% 0.21/0.41  fof(f139,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X3),X2)) ) | ~spl3_21),
% 0.21/0.41    inference(avatar_component_clause,[],[f138])).
% 0.21/0.41  fof(f140,plain,(
% 0.21/0.41    spl3_21 | ~spl3_11 | ~spl3_19),
% 0.21/0.41    inference(avatar_split_clause,[],[f133,f126,f78,f138])).
% 0.21/0.41  fof(f78,plain,(
% 0.21/0.41    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.41  fof(f126,plain,(
% 0.21/0.41    spl3_19 <=> ! [X3,X2,X4] : (~r1_tarski(X2,X3) | r1_tarski(k3_xboole_0(X2,X4),X3))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.41  fof(f133,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(k3_xboole_0(X0,X3),X2)) ) | (~spl3_11 | ~spl3_19)),
% 0.21/0.41    inference(resolution,[],[f127,f79])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f78])).
% 0.21/0.41  fof(f127,plain,(
% 0.21/0.41    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X2,X4),X3) | ~r1_tarski(X2,X3)) ) | ~spl3_19),
% 0.21/0.41    inference(avatar_component_clause,[],[f126])).
% 0.21/0.41  fof(f128,plain,(
% 0.21/0.41    spl3_19 | ~spl3_7 | ~spl3_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f119,f78,f62,f126])).
% 0.21/0.41  fof(f119,plain,(
% 0.21/0.41    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k3_xboole_0(X2,X4),X3)) ) | (~spl3_7 | ~spl3_11)),
% 0.21/0.41    inference(resolution,[],[f79,f63])).
% 0.21/0.41  fof(f116,plain,(
% 0.21/0.41    spl3_17 | ~spl3_5 | ~spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f111,f58,f53,f113])).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    spl3_6 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.41  fof(f111,plain,(
% 0.21/0.41    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | (~spl3_5 | ~spl3_6)),
% 0.21/0.41    inference(resolution,[],[f59,f55])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) ) | ~spl3_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f58])).
% 0.21/0.41  fof(f88,plain,(
% 0.21/0.41    spl3_12 | ~spl3_2 | ~spl3_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f81,f66,f38,f85])).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    spl3_2 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) | (~spl3_2 | ~spl3_8)),
% 0.21/0.41    inference(resolution,[],[f67,f40])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f38])).
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f66])).
% 0.21/0.41  fof(f80,plain,(
% 0.21/0.41    spl3_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f31,f78])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(flattening,[],[f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.41  fof(f76,plain,(
% 0.21/0.41    spl3_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f30,f74])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    spl3_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    spl3_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f28,f66])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f27,f62])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f26,f58])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f53])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    v1_relat_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.41    inference(ennf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.41    inference(negated_conjecture,[],[f7])).
% 0.21/0.41  fof(f7,conjecture,(
% 0.21/0.41    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    spl3_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f22,f48])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    v1_funct_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f20])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f23,f43])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.41    inference(cnf_transformation,[],[f20])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl3_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f24,f38])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.41    inference(cnf_transformation,[],[f20])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ~spl3_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f25,f33])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ~r1_tarski(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f20])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (7191)------------------------------
% 0.21/0.41  % (7191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (7191)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (7191)Memory used [KB]: 11129
% 0.21/0.41  % (7191)Time elapsed: 0.014 s
% 0.21/0.41  % (7191)------------------------------
% 0.21/0.41  % (7191)------------------------------
% 0.21/0.41  % (7184)Success in time 0.055 s
%------------------------------------------------------------------------------
