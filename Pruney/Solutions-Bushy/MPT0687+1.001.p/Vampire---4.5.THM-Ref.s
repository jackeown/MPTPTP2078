%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0687+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:27 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 459 expanded)
%              Number of leaves         :   15 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  330 (1184 expanded)
%              Number of equality atoms :   63 ( 282 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1376,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f55,f535,f550,f759,f791,f1163,f1253,f1329,f1375])).

fof(f1375,plain,
    ( ~ spl10_13
    | spl10_19 ),
    inference(avatar_contradiction_clause,[],[f1374])).

fof(f1374,plain,
    ( $false
    | ~ spl10_13
    | spl10_19 ),
    inference(subsumption_resolution,[],[f1370,f528])).

fof(f528,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | spl10_19 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl10_19
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f1370,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl10_13 ),
    inference(resolution,[],[f1355,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1355,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl10_13 ),
    inference(resolution,[],[f852,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK8(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f852,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_13 ),
    inference(resolution,[],[f839,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f839,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_13 ),
    inference(resolution,[],[f836,f27])).

fof(f836,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl10_13 ),
    inference(forward_demodulation,[],[f835,f473])).

fof(f473,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(k1_tarski(k2_relat_1(sK1)))) ),
    inference(resolution,[],[f472,f43])).

fof(f43,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f472,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X0)) ) ),
    inference(subsumption_resolution,[],[f471,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f471,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X0))
      | v1_xboole_0(k10_relat_1(sK1,k1_tarski(X0))) ) ),
    inference(resolution,[],[f295,f27])).

fof(f295,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5(k10_relat_1(sK1,k1_tarski(X2))),k10_relat_1(sK1,k1_tarski(X2)))
      | ~ r2_hidden(k2_relat_1(sK1),X2)
      | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X2)) ) ),
    inference(superposition,[],[f264,f106])).

fof(f106,plain,(
    ! [X2] :
      ( sK3(sK1,k1_tarski(X2),sK5(k10_relat_1(sK1,k1_tarski(X2)))) = X2
      | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X2)) ) ),
    inference(resolution,[],[f82,f20])).

fof(f82,plain,(
    ! [X4] :
      ( v1_xboole_0(k10_relat_1(sK1,k1_tarski(X4)))
      | sK3(sK1,k1_tarski(X4),sK5(k10_relat_1(sK1,k1_tarski(X4)))) = X4 ) ),
    inference(resolution,[],[f79,f27])).

fof(f79,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k10_relat_1(sK1,k1_tarski(X3)))
      | sK3(sK1,k1_tarski(X3),X2) = X3 ) ),
    inference(resolution,[],[f77,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1,X0,X1),X0)
      | ~ r2_hidden(X1,k10_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f39,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k2_relat_1(sK1),sK3(sK1,X1,X0))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f209,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f209,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(sK1,X4,X3),k2_relat_1(sK1))
      | ~ r2_hidden(X3,k10_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f207,f45])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f207,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK3(sK1,X1,X0)),sK1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f40,f19])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK3(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK3(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f835,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0),k10_relat_1(sK1,k1_tarski(k1_tarski(k2_relat_1(sK1)))))
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f815,f43])).

fof(f815,plain,
    ( ~ r2_hidden(k2_relat_1(sK1),k1_tarski(k2_relat_1(sK1)))
    | ~ r2_hidden(sK5(k1_xboole_0),k10_relat_1(sK1,k1_tarski(k1_tarski(k2_relat_1(sK1)))))
    | ~ spl10_13 ),
    inference(superposition,[],[f264,f504])).

fof(f504,plain,
    ( k1_tarski(k2_relat_1(sK1)) = sK3(sK1,k1_tarski(k1_tarski(k2_relat_1(sK1))),sK5(k1_xboole_0))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl10_13
  <=> k1_tarski(k2_relat_1(sK1)) = sK3(sK1,k1_tarski(k1_tarski(k2_relat_1(sK1))),sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f1329,plain,
    ( ~ spl10_19
    | spl10_20 ),
    inference(avatar_contradiction_clause,[],[f1328])).

fof(f1328,plain,
    ( $false
    | ~ spl10_19
    | spl10_20 ),
    inference(subsumption_resolution,[],[f1327,f533])).

fof(f533,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl10_20 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl10_20
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f1327,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl10_19 ),
    inference(resolution,[],[f529,f20])).

fof(f529,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f527])).

fof(f1253,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(avatar_contradiction_clause,[],[f1252])).

fof(f1252,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1243,f43])).

fof(f1243,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(resolution,[],[f1203,f48])).

fof(f48,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl10_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1203,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_relat_1(sK1))
        | ~ r2_hidden(X5,k1_tarski(sK0)) )
    | ~ spl10_2
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1185,f844])).

fof(f844,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f725,f534])).

fof(f534,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f532])).

fof(f725,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(resolution,[],[f637,f44])).

fof(f637,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(resolution,[],[f625,f37])).

fof(f625,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f549,f554])).

fof(f554,plain,
    ( k1_xboole_0 = k2_relat_1(k2_relat_1(k1_xboole_0))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl10_24
  <=> k1_xboole_0 = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f549,plain,
    ( v1_xboole_0(k2_relat_1(k2_relat_1(k1_xboole_0)))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl10_23
  <=> v1_xboole_0(k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f1185,plain,
    ( ! [X5] :
        ( r2_hidden(sK8(sK1,X5),k1_xboole_0)
        | ~ r2_hidden(X5,k1_tarski(sK0))
        | ~ r2_hidden(X5,k2_relat_1(sK1)) )
    | ~ spl10_2 ),
    inference(superposition,[],[f118,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl10_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(sK1,X0),k10_relat_1(sK1,X1))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f117,f44])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,k10_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f38,f19])).

fof(f38,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1163,plain,
    ( spl10_1
    | spl10_2
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(avatar_contradiction_clause,[],[f1162])).

fof(f1162,plain,
    ( $false
    | spl10_1
    | spl10_2
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1159,f52])).

fof(f52,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f1159,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | spl10_1
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(resolution,[],[f1142,f49])).

fof(f49,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f1142,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k2_relat_1(sK1))
        | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X3)) )
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1136,f860])).

fof(f860,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(k1_xboole_0,X1),X1)
        | k1_xboole_0 = X1 )
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f855,f534])).

fof(f855,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(k1_xboole_0,X1),X1)
        | k2_relat_1(k1_xboole_0) = X1 )
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(resolution,[],[f844,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f1136,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k2_relat_1(sK1))
        | ~ r2_hidden(sK7(k1_xboole_0,k10_relat_1(sK1,k1_tarski(X3))),k10_relat_1(sK1,k1_tarski(X3)))
        | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X3)) )
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(superposition,[],[f209,f898])).

fof(f898,plain,
    ( ! [X7] :
        ( sK3(sK1,k1_tarski(X7),sK7(k1_xboole_0,k10_relat_1(sK1,k1_tarski(X7)))) = X7
        | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X7)) )
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(resolution,[],[f860,f79])).

fof(f791,plain,
    ( ~ spl10_20
    | spl10_24 ),
    inference(avatar_contradiction_clause,[],[f790])).

fof(f790,plain,
    ( $false
    | ~ spl10_20
    | spl10_24 ),
    inference(subsumption_resolution,[],[f789,f534])).

fof(f789,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ spl10_20
    | spl10_24 ),
    inference(forward_demodulation,[],[f553,f534])).

fof(f553,plain,
    ( k1_xboole_0 != k2_relat_1(k2_relat_1(k1_xboole_0))
    | spl10_24 ),
    inference(avatar_component_clause,[],[f552])).

fof(f759,plain,
    ( ~ spl10_19
    | ~ spl10_20
    | spl10_23 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | ~ spl10_19
    | ~ spl10_20
    | spl10_23 ),
    inference(subsumption_resolution,[],[f628,f753])).

fof(f753,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_20
    | spl10_23 ),
    inference(forward_demodulation,[],[f752,f534])).

fof(f752,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl10_20
    | spl10_23 ),
    inference(forward_demodulation,[],[f548,f534])).

fof(f548,plain,
    ( ~ v1_xboole_0(k2_relat_1(k2_relat_1(k1_xboole_0)))
    | spl10_23 ),
    inference(avatar_component_clause,[],[f547])).

fof(f628,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_19
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f529,f534])).

fof(f550,plain,
    ( spl10_13
    | spl10_23 ),
    inference(avatar_split_clause,[],[f490,f547,f502])).

fof(f490,plain,
    ( v1_xboole_0(k2_relat_1(k2_relat_1(k1_xboole_0)))
    | k1_tarski(k2_relat_1(sK1)) = sK3(sK1,k1_tarski(k1_tarski(k2_relat_1(sK1))),sK5(k1_xboole_0)) ),
    inference(superposition,[],[f442,f473])).

fof(f442,plain,(
    ! [X4] :
      ( v1_xboole_0(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_tarski(X4)))))
      | sK3(sK1,k1_tarski(X4),sK5(k10_relat_1(sK1,k1_tarski(X4)))) = X4 ) ),
    inference(resolution,[],[f408,f27])).

fof(f408,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_tarski(X0)))))
      | sK3(sK1,k1_tarski(X0),sK5(k10_relat_1(sK1,k1_tarski(X0)))) = X0 ) ),
    inference(resolution,[],[f111,f44])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k10_relat_1(sK1,k1_tarski(X0))))
      | sK3(sK1,k1_tarski(X0),sK5(k10_relat_1(sK1,k1_tarski(X0)))) = X0 ) ),
    inference(resolution,[],[f105,f44])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k10_relat_1(sK1,k1_tarski(X0)))
      | sK3(sK1,k1_tarski(X0),sK5(k10_relat_1(sK1,k1_tarski(X0)))) = X0 ) ),
    inference(resolution,[],[f82,f37])).

fof(f535,plain,
    ( spl10_20
    | spl10_13 ),
    inference(avatar_split_clause,[],[f487,f502,f532])).

fof(f487,plain,
    ( k1_tarski(k2_relat_1(sK1)) = sK3(sK1,k1_tarski(k1_tarski(k2_relat_1(sK1))),sK5(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f413,f473])).

fof(f413,plain,(
    ! [X2] :
      ( sK3(sK1,k1_tarski(X2),sK5(k10_relat_1(sK1,k1_tarski(X2)))) = X2
      | k1_xboole_0 = k2_relat_1(k10_relat_1(sK1,k1_tarski(X2))) ) ),
    inference(resolution,[],[f410,f20])).

fof(f410,plain,(
    ! [X4] :
      ( v1_xboole_0(k2_relat_1(k10_relat_1(sK1,k1_tarski(X4))))
      | sK3(sK1,k1_tarski(X4),sK5(k10_relat_1(sK1,k1_tarski(X4)))) = X4 ) ),
    inference(resolution,[],[f111,f27])).

fof(f55,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f17,f51,f47])).

fof(f17,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f18,f51,f47])).

fof(f18,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
