%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 240 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  247 ( 478 expanded)
%              Number of equality atoms :   70 ( 156 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f112,f116,f146,f161,f245,f305,f518,f536,f587,f588])).

fof(f588,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) != k2_relat_1(sK1)
    | k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f587,plain,
    ( spl2_21
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f582,f532,f109,f69,f584])).

fof(f584,plain,
    ( spl2_21
  <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f69,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f109,plain,
    ( spl2_5
  <=> k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f532,plain,
    ( spl2_20
  <=> k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f582,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f568,f111])).

fof(f111,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f568,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(superposition,[],[f88,f534])).

fof(f534,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f532])).

fof(f88,plain,
    ( ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f71,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f71,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f536,plain,
    ( spl2_20
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f528,f507,f532])).

fof(f507,plain,
    ( spl2_18
  <=> r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f528,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_18 ),
    inference(resolution,[],[f509,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f509,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f507])).

fof(f518,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f517,f302,f69,f507])).

fof(f302,plain,
    ( spl2_15
  <=> k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f517,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f498,f76])).

fof(f76,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f74,f46])).

fof(f74,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f37,f36])).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f498,plain,
    ( r1_tarski(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(superposition,[],[f185,f304])).

fof(f304,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f302])).

fof(f185,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f174,f88])).

fof(f174,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),k10_relat_1(sK1,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f96,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl2_3 ),
    inference(resolution,[],[f45,f71])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f52])).

% (16462)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f57,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2))) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f50,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f305,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f295,f157,f69,f302])).

fof(f157,plain,
    ( spl2_11
  <=> k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f295,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(superposition,[],[f86,f159])).

fof(f159,plain,
    ( k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f86,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f71,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f245,plain,
    ( ~ spl2_13
    | spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f240,f114,f69,f59,f242])).

fof(f242,plain,
    ( spl2_13
  <=> k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f59,plain,
    ( spl2_1
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f114,plain,
    ( spl2_6
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f240,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) != k3_xboole_0(sK0,k2_relat_1(sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f231,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f231,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) != k3_xboole_0(k2_relat_1(sK1),sK0)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f61,f183])).

fof(f183,plain,
    ( ! [X0] : k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f176,f86])).

fof(f176,plain,
    ( ! [X0] : k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)))
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f96,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f61,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f161,plain,
    ( spl2_11
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f153,f143,f157])).

fof(f143,plain,
    ( spl2_10
  <=> r1_tarski(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f153,plain,
    ( k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_10 ),
    inference(resolution,[],[f145,f46])).

fof(f145,plain,
    ( r1_tarski(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f146,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f136,f109,f69,f143])).

fof(f136,plain,
    ( r1_tarski(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f80,f111])).

fof(f80,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f71,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

fof(f116,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f107,f64,f114,f69])).

fof(f64,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2 ),
    inference(resolution,[],[f47,f66])).

fof(f66,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f112,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f106,f69,f64,f109])).

fof(f106,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f71,f66,f74,f47])).

fof(f72,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f67,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (16460)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (16458)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (16467)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (16452)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (16459)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (16458)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f589,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f62,f67,f72,f112,f116,f146,f161,f245,f305,f518,f536,f587,f588])).
% 0.20/0.48  fof(f588,plain,(
% 0.20/0.48    k9_relat_1(sK1,k1_relat_1(sK1)) != k2_relat_1(sK1) | k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f587,plain,(
% 0.20/0.48    spl2_21 | ~spl2_3 | ~spl2_5 | ~spl2_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f582,f532,f109,f69,f584])).
% 0.20/0.48  fof(f584,plain,(
% 0.20/0.48    spl2_21 <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl2_3 <=> v1_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl2_5 <=> k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.48  fof(f532,plain,(
% 0.20/0.48    spl2_20 <=> k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.48  fof(f582,plain,(
% 0.20/0.48    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) | (~spl2_3 | ~spl2_5 | ~spl2_20)),
% 0.20/0.48    inference(forward_demodulation,[],[f568,f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) | ~spl2_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f109])).
% 0.20/0.48  fof(f568,plain,(
% 0.20/0.48    k9_relat_1(sK1,k1_relat_1(sK1)) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) | (~spl2_3 | ~spl2_20)),
% 0.20/0.48    inference(superposition,[],[f88,f534])).
% 0.20/0.48  fof(f534,plain,(
% 0.20/0.48    k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | ~spl2_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f532])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) ) | ~spl2_3),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f71,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    v1_relat_1(sK1) | ~spl2_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f536,plain,(
% 0.20/0.48    spl2_20 | ~spl2_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f528,f507,f532])).
% 0.20/0.48  fof(f507,plain,(
% 0.20/0.48    spl2_18 <=> r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.48  fof(f528,plain,(
% 0.20/0.48    k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | ~spl2_18),
% 0.20/0.48    inference(resolution,[],[f509,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.48  fof(f509,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | ~spl2_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f507])).
% 0.20/0.48  fof(f518,plain,(
% 0.20/0.48    spl2_18 | ~spl2_3 | ~spl2_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f517,f302,f69,f507])).
% 0.20/0.48  fof(f302,plain,(
% 0.20/0.48    spl2_15 <=> k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.48  fof(f517,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | (~spl2_3 | ~spl2_15)),
% 0.20/0.48    inference(forward_demodulation,[],[f498,f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f74,f46])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f73,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f37,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.48  fof(f498,plain,(
% 0.20/0.48    r1_tarski(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)),k10_relat_1(sK1,k2_relat_1(sK1))) | (~spl2_3 | ~spl2_15)),
% 0.20/0.48    inference(superposition,[],[f185,f304])).
% 0.20/0.48  fof(f304,plain,(
% 0.20/0.48    k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl2_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f302])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | ~spl2_3),
% 0.20/0.48    inference(forward_demodulation,[],[f174,f88])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),k10_relat_1(sK1,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))))) ) | ~spl2_3),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f96,f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | ~spl2_3),
% 0.20/0.48    inference(resolution,[],[f45,f71])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(superposition,[],[f57,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f38,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f40,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f41,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f51,f52])).
% 0.20/0.48  % (16462)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.48    inference(rectify,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f50,f55])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.20/0.48  fof(f305,plain,(
% 0.20/0.48    spl2_15 | ~spl2_3 | ~spl2_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f295,f157,f69,f302])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    spl2_11 <=> k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.48  fof(f295,plain,(
% 0.20/0.48    k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) = k10_relat_1(sK1,k2_relat_1(sK1)) | (~spl2_3 | ~spl2_11)),
% 0.20/0.48    inference(superposition,[],[f86,f159])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f157])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) ) | ~spl2_3),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f71,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    ~spl2_13 | spl2_1 | ~spl2_3 | ~spl2_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f240,f114,f69,f59,f242])).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    spl2_13 <=> k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl2_1 <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl2_6 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.48  fof(f240,plain,(
% 0.20/0.48    k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) != k3_xboole_0(sK0,k2_relat_1(sK1)) | (spl2_1 | ~spl2_3 | ~spl2_6)),
% 0.20/0.48    inference(forward_demodulation,[],[f231,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) != k3_xboole_0(k2_relat_1(sK1),sK0) | (spl2_1 | ~spl2_3 | ~spl2_6)),
% 0.20/0.48    inference(backward_demodulation,[],[f61,f183])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    ( ! [X0] : (k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0))) ) | (~spl2_3 | ~spl2_6)),
% 0.20/0.48    inference(forward_demodulation,[],[f176,f86])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    ( ! [X0] : (k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)))) ) | ~spl2_6),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f96,f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) ) | ~spl2_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f114])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) | spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f59])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl2_11 | ~spl2_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f153,f143,f157])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    spl2_10 <=> r1_tarski(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_10),
% 0.20/0.48    inference(resolution,[],[f145,f46])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) | ~spl2_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f143])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    spl2_10 | ~spl2_3 | ~spl2_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f136,f109,f69,f143])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) | (~spl2_3 | ~spl2_5)),
% 0.20/0.48    inference(superposition,[],[f80,f111])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,k1_relat_1(sK1)))) ) | ~spl2_3),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f71,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ~spl2_3 | spl2_6 | ~spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f107,f64,f114,f69])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl2_2 <=> v1_funct_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) ) | ~spl2_2),
% 0.20/0.48    inference(resolution,[],[f47,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    v1_funct_1(sK1) | ~spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f64])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl2_5 | ~spl2_2 | ~spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f106,f69,f64,f109])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) | (~spl2_2 | ~spl2_3)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f71,f66,f74,f47])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f69])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f17])).
% 0.20/0.48  fof(f17,conjecture,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f34,f64])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    v1_funct_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ~spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f59])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (16458)------------------------------
% 0.20/0.48  % (16458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (16458)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (16458)Memory used [KB]: 6396
% 0.20/0.48  % (16458)Time elapsed: 0.060 s
% 0.20/0.48  % (16458)------------------------------
% 0.20/0.48  % (16458)------------------------------
% 0.20/0.48  % (16453)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (16466)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (16464)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (16457)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (16469)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (16455)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (16454)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (16451)Success in time 0.135 s
%------------------------------------------------------------------------------
