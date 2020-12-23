%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:26 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 503 expanded)
%              Number of leaves         :   24 ( 161 expanded)
%              Depth                    :   20
%              Number of atoms          :  233 ( 817 expanded)
%              Number of equality atoms :   73 ( 424 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f86,f91,f1664,f1695])).

fof(f1695,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f1694])).

fof(f1694,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f1684,f1663])).

fof(f1663,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f1661])).

fof(f1661,plain,
    ( spl3_12
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1684,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | ~ spl3_1
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f90,f694,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f694,plain,
    ( ! [X2,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK0,X1),X2),k10_relat_1(sK0,X2))
    | ~ spl3_1 ),
    inference(superposition,[],[f605,f172])).

fof(f172,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f75,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(X2,X1)) ) ),
    inference(backward_demodulation,[],[f69,f142])).

fof(f142,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f138,f130])).

fof(f130,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f42,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f138,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f45,f128])).

fof(f128,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f67,f125])).

fof(f125,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f42,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f67,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f75,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f605,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(backward_demodulation,[],[f101,f597])).

fof(f597,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(backward_demodulation,[],[f182,f595])).

fof(f595,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f594,f45])).

fof(f594,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f130,f96])).

fof(f96,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f93,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f93,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f42,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f182,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(forward_demodulation,[],[f181,f96])).

fof(f181,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X0)) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) ),
    inference(forward_demodulation,[],[f180,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(unit_resulting_resolution,[],[f42,f149])).

fof(f180,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(forward_demodulation,[],[f177,f44])).

fof(f177,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f42,f43,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k9_relat_1(k6_relat_1(X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f68,f142])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f43,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f99,f44])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f90,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_4
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1664,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f653,f83,f73,f1661])).

fof(f83,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f653,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f626,f172])).

fof(f626,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f271,f597])).

fof(f271,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f262,f44])).

fof(f262,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f42,f43,f70,f150,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f150,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f118,f142])).

fof(f118,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k3_enumset1(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2),X0)),sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f85,f66,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f85,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f41,f88])).

fof(f41,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f86,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f83])).

fof(f40,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (2266)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.51  % (2238)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (2243)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (2245)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (2241)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (2242)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (2236)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (2237)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (2271)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (2265)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (2237)Refutation not found, incomplete strategy% (2237)------------------------------
% 0.22/0.53  % (2237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2237)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2237)Memory used [KB]: 1663
% 0.22/0.53  % (2237)Time elapsed: 0.105 s
% 0.22/0.53  % (2237)------------------------------
% 0.22/0.53  % (2237)------------------------------
% 0.22/0.53  % (2252)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (2244)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (2255)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (2264)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (2261)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (2268)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (2258)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (2256)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (2269)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (2267)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (2257)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (2270)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (2240)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (2262)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (2260)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.55  % (2263)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.55  % (2254)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.55  % (2247)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.58/0.57  % (2259)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.58/0.58  % (2246)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.28/0.69  % (2262)Refutation found. Thanks to Tanya!
% 2.28/0.69  % SZS status Theorem for theBenchmark
% 2.28/0.69  % SZS output start Proof for theBenchmark
% 2.28/0.69  fof(f1711,plain,(
% 2.28/0.69    $false),
% 2.28/0.69    inference(avatar_sat_refutation,[],[f76,f86,f91,f1664,f1695])).
% 2.28/0.69  fof(f1695,plain,(
% 2.28/0.69    ~spl3_1 | spl3_4 | ~spl3_12),
% 2.28/0.69    inference(avatar_contradiction_clause,[],[f1694])).
% 2.28/0.69  fof(f1694,plain,(
% 2.28/0.69    $false | (~spl3_1 | spl3_4 | ~spl3_12)),
% 2.28/0.69    inference(subsumption_resolution,[],[f1684,f1663])).
% 2.28/0.69  fof(f1663,plain,(
% 2.28/0.69    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | ~spl3_12),
% 2.28/0.69    inference(avatar_component_clause,[],[f1661])).
% 2.28/0.69  fof(f1661,plain,(
% 2.28/0.69    spl3_12 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))),
% 2.28/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.28/0.69  fof(f1684,plain,(
% 2.28/0.69    ~r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | (~spl3_1 | spl3_4)),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f90,f694,f57])).
% 2.28/0.69  fof(f57,plain,(
% 2.28/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f37])).
% 2.28/0.69  fof(f37,plain,(
% 2.28/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.28/0.69    inference(flattening,[],[f36])).
% 2.28/0.69  fof(f36,plain,(
% 2.28/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.28/0.69    inference(nnf_transformation,[],[f1])).
% 2.28/0.69  fof(f1,axiom,(
% 2.28/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.28/0.69  fof(f694,plain,(
% 2.28/0.69    ( ! [X2,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK0,X1),X2),k10_relat_1(sK0,X2))) ) | ~spl3_1),
% 2.28/0.69    inference(superposition,[],[f605,f172])).
% 2.28/0.69  fof(f172,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1))) ) | ~spl3_1),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f75,f149])).
% 2.28/0.69  fof(f149,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(X2,X1))) )),
% 2.28/0.69    inference(backward_demodulation,[],[f69,f142])).
% 2.28/0.69  fof(f142,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 2.28/0.69    inference(forward_demodulation,[],[f138,f130])).
% 2.28/0.69  fof(f130,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f42,f53])).
% 2.28/0.69  fof(f53,plain,(
% 2.28/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f25])).
% 2.28/0.69  fof(f25,plain,(
% 2.28/0.69    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.28/0.69    inference(ennf_transformation,[],[f8])).
% 2.28/0.69  fof(f8,axiom,(
% 2.28/0.69    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.28/0.69  fof(f42,plain,(
% 2.28/0.69    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f13])).
% 2.28/0.69  fof(f13,axiom,(
% 2.28/0.69    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.28/0.69  fof(f138,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.28/0.69    inference(superposition,[],[f45,f128])).
% 2.28/0.69  fof(f128,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.28/0.69    inference(backward_demodulation,[],[f67,f125])).
% 2.28/0.69  fof(f125,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f42,f52])).
% 2.28/0.69  fof(f52,plain,(
% 2.28/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f24])).
% 2.28/0.69  fof(f24,plain,(
% 2.28/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.28/0.69    inference(ennf_transformation,[],[f11])).
% 2.28/0.69  fof(f11,axiom,(
% 2.28/0.69    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.28/0.69  fof(f67,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.28/0.69    inference(definition_unfolding,[],[f50,f65])).
% 2.28/0.69  fof(f65,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.28/0.69    inference(definition_unfolding,[],[f48,f64])).
% 2.28/0.69  fof(f64,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.28/0.69    inference(definition_unfolding,[],[f49,f63])).
% 2.28/0.69  fof(f63,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.28/0.69    inference(definition_unfolding,[],[f58,f62])).
% 2.28/0.69  fof(f62,plain,(
% 2.28/0.69    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f6])).
% 2.28/0.69  fof(f6,axiom,(
% 2.28/0.69    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.28/0.69  fof(f58,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f5])).
% 2.28/0.69  fof(f5,axiom,(
% 2.28/0.69    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.28/0.69  fof(f49,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f4])).
% 2.28/0.69  fof(f4,axiom,(
% 2.28/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.28/0.69  fof(f48,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f7])).
% 2.28/0.69  fof(f7,axiom,(
% 2.28/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.28/0.69  fof(f50,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f17])).
% 2.28/0.69  fof(f17,axiom,(
% 2.28/0.69    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 2.28/0.69  fof(f45,plain,(
% 2.28/0.69    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.28/0.69    inference(cnf_transformation,[],[f10])).
% 2.28/0.69  fof(f10,axiom,(
% 2.28/0.69    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.28/0.69  fof(f69,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 2.28/0.69    inference(definition_unfolding,[],[f59,f65])).
% 2.28/0.69  fof(f59,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f28])).
% 2.28/0.69  fof(f28,plain,(
% 2.28/0.69    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.28/0.69    inference(ennf_transformation,[],[f14])).
% 2.28/0.69  fof(f14,axiom,(
% 2.28/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.28/0.69  fof(f75,plain,(
% 2.28/0.69    v1_relat_1(sK0) | ~spl3_1),
% 2.28/0.69    inference(avatar_component_clause,[],[f73])).
% 2.28/0.69  fof(f73,plain,(
% 2.28/0.69    spl3_1 <=> v1_relat_1(sK0)),
% 2.28/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.28/0.69  fof(f605,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X0)) )),
% 2.28/0.69    inference(backward_demodulation,[],[f101,f597])).
% 2.28/0.69  fof(f597,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 2.28/0.69    inference(backward_demodulation,[],[f182,f595])).
% 2.28/0.69  fof(f595,plain,(
% 2.28/0.69    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.28/0.69    inference(forward_demodulation,[],[f594,f45])).
% 2.28/0.69  fof(f594,plain,(
% 2.28/0.69    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 2.28/0.69    inference(superposition,[],[f130,f96])).
% 2.28/0.69  fof(f96,plain,(
% 2.28/0.69    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 2.28/0.69    inference(forward_demodulation,[],[f93,f44])).
% 2.28/0.69  fof(f44,plain,(
% 2.28/0.69    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.28/0.69    inference(cnf_transformation,[],[f10])).
% 2.28/0.69  fof(f93,plain,(
% 2.28/0.69    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f42,f46])).
% 2.28/0.69  fof(f46,plain,(
% 2.28/0.69    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.28/0.69    inference(cnf_transformation,[],[f22])).
% 2.28/0.69  fof(f22,plain,(
% 2.28/0.69    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.28/0.69    inference(ennf_transformation,[],[f12])).
% 2.28/0.69  fof(f12,axiom,(
% 2.28/0.69    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 2.28/0.69  fof(f182,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X0))) )),
% 2.28/0.69    inference(forward_demodulation,[],[f181,f96])).
% 2.28/0.69  fof(f181,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X0)) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)) )),
% 2.28/0.69    inference(forward_demodulation,[],[f180,f173])).
% 2.28/0.69  fof(f173,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X0),X2))) )),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f42,f149])).
% 2.28/0.69  fof(f180,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X0))) )),
% 2.28/0.69    inference(forward_demodulation,[],[f177,f44])).
% 2.28/0.69  fof(f177,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) )),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f42,f43,f148])).
% 2.28/0.69  fof(f148,plain,(
% 2.28/0.69    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k9_relat_1(k6_relat_1(X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 2.28/0.69    inference(backward_demodulation,[],[f68,f142])).
% 2.28/0.69  fof(f68,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.28/0.69    inference(definition_unfolding,[],[f54,f65])).
% 2.28/0.69  fof(f54,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f27])).
% 2.28/0.69  fof(f27,plain,(
% 2.28/0.69    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.28/0.69    inference(flattening,[],[f26])).
% 2.28/0.69  fof(f26,plain,(
% 2.28/0.69    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.28/0.69    inference(ennf_transformation,[],[f15])).
% 2.28/0.69  fof(f15,axiom,(
% 2.28/0.69    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 2.28/0.69  fof(f43,plain,(
% 2.28/0.69    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f13])).
% 2.28/0.69  fof(f101,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.28/0.69    inference(forward_demodulation,[],[f99,f44])).
% 2.28/0.69  fof(f99,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))) )),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f42,f51])).
% 2.28/0.69  fof(f51,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f23])).
% 2.28/0.69  fof(f23,plain,(
% 2.28/0.69    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.28/0.69    inference(ennf_transformation,[],[f9])).
% 2.28/0.69  fof(f9,axiom,(
% 2.28/0.69    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.28/0.69  fof(f90,plain,(
% 2.28/0.69    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_4),
% 2.28/0.69    inference(avatar_component_clause,[],[f88])).
% 2.28/0.69  fof(f88,plain,(
% 2.28/0.69    spl3_4 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.28/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.28/0.69  fof(f1664,plain,(
% 2.28/0.69    spl3_12 | ~spl3_1 | ~spl3_3),
% 2.28/0.69    inference(avatar_split_clause,[],[f653,f83,f73,f1661])).
% 2.28/0.69  fof(f83,plain,(
% 2.28/0.69    spl3_3 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.28/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.28/0.69  fof(f653,plain,(
% 2.28/0.69    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | (~spl3_1 | ~spl3_3)),
% 2.28/0.69    inference(forward_demodulation,[],[f626,f172])).
% 2.28/0.69  fof(f626,plain,(
% 2.28/0.69    r1_tarski(k10_relat_1(sK0,sK2),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) | ~spl3_3),
% 2.28/0.69    inference(backward_demodulation,[],[f271,f597])).
% 2.28/0.69  fof(f271,plain,(
% 2.28/0.69    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_3),
% 2.28/0.69    inference(forward_demodulation,[],[f262,f44])).
% 2.28/0.69  fof(f262,plain,(
% 2.28/0.69    r1_tarski(k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_3),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f42,f43,f70,f150,f60])).
% 2.28/0.69  fof(f60,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f30])).
% 2.28/0.69  fof(f30,plain,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.28/0.69    inference(flattening,[],[f29])).
% 2.28/0.69  fof(f29,plain,(
% 2.28/0.69    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.28/0.69    inference(ennf_transformation,[],[f16])).
% 2.28/0.69  fof(f16,axiom,(
% 2.28/0.69    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 2.28/0.69  fof(f150,plain,(
% 2.28/0.69    ( ! [X0] : (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1)) ) | ~spl3_3),
% 2.28/0.69    inference(backward_demodulation,[],[f118,f142])).
% 2.28/0.69  fof(f118,plain,(
% 2.28/0.69    ( ! [X0] : (r1_tarski(k1_setfam_1(k3_enumset1(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2),X0)),sK1)) ) | ~spl3_3),
% 2.28/0.69    inference(unit_resulting_resolution,[],[f85,f66,f61])).
% 2.28/0.69  fof(f61,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f32])).
% 2.28/0.69  fof(f32,plain,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.28/0.69    inference(flattening,[],[f31])).
% 2.28/0.69  fof(f31,plain,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.28/0.69    inference(ennf_transformation,[],[f3])).
% 2.28/0.69  fof(f3,axiom,(
% 2.28/0.69    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.28/0.69  fof(f66,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0)) )),
% 2.28/0.69    inference(definition_unfolding,[],[f47,f65])).
% 2.28/0.69  fof(f47,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f2])).
% 2.28/0.69  fof(f2,axiom,(
% 2.28/0.69    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.28/0.69  fof(f85,plain,(
% 2.28/0.69    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_3),
% 2.28/0.69    inference(avatar_component_clause,[],[f83])).
% 2.28/0.69  fof(f70,plain,(
% 2.28/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.28/0.69    inference(equality_resolution,[],[f56])).
% 2.28/0.69  fof(f56,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.28/0.69    inference(cnf_transformation,[],[f37])).
% 2.28/0.69  fof(f91,plain,(
% 2.28/0.69    ~spl3_4),
% 2.28/0.69    inference(avatar_split_clause,[],[f41,f88])).
% 2.28/0.69  fof(f41,plain,(
% 2.28/0.69    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.28/0.69    inference(cnf_transformation,[],[f35])).
% 2.28/0.69  fof(f35,plain,(
% 2.28/0.69    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.28/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34,f33])).
% 2.28/0.69  fof(f33,plain,(
% 2.28/0.69    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.28/0.69    introduced(choice_axiom,[])).
% 2.28/0.69  fof(f34,plain,(
% 2.28/0.69    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 2.28/0.69    introduced(choice_axiom,[])).
% 2.28/0.69  fof(f21,plain,(
% 2.28/0.69    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.28/0.69    inference(flattening,[],[f20])).
% 2.28/0.69  fof(f20,plain,(
% 2.28/0.69    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.28/0.69    inference(ennf_transformation,[],[f19])).
% 2.28/0.69  fof(f19,negated_conjecture,(
% 2.28/0.69    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.28/0.69    inference(negated_conjecture,[],[f18])).
% 2.28/0.69  fof(f18,conjecture,(
% 2.28/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 2.28/0.69  fof(f86,plain,(
% 2.28/0.69    spl3_3),
% 2.28/0.69    inference(avatar_split_clause,[],[f40,f83])).
% 2.28/0.69  fof(f40,plain,(
% 2.28/0.69    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.28/0.69    inference(cnf_transformation,[],[f35])).
% 2.28/0.69  fof(f76,plain,(
% 2.28/0.69    spl3_1),
% 2.28/0.69    inference(avatar_split_clause,[],[f38,f73])).
% 2.28/0.69  fof(f38,plain,(
% 2.28/0.69    v1_relat_1(sK0)),
% 2.28/0.69    inference(cnf_transformation,[],[f35])).
% 2.28/0.69  % SZS output end Proof for theBenchmark
% 2.28/0.69  % (2262)------------------------------
% 2.28/0.69  % (2262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.69  % (2262)Termination reason: Refutation
% 2.28/0.69  
% 2.28/0.69  % (2262)Memory used [KB]: 12281
% 2.28/0.69  % (2262)Time elapsed: 0.260 s
% 2.28/0.69  % (2262)------------------------------
% 2.28/0.69  % (2262)------------------------------
% 2.28/0.69  % (2235)Success in time 0.328 s
%------------------------------------------------------------------------------
