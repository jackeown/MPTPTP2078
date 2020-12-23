%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 144 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  239 ( 363 expanded)
%              Number of equality atoms :   53 (  72 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f55,f60,f64,f80,f102,f110,f116,f129,f136,f148,f167,f176,f191,f199,f203])).

fof(f203,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_14
    | ~ spl2_27 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl2_3
    | spl2_4
    | ~ spl2_14
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f201,f59])).

fof(f59,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_4
  <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f201,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_3
    | ~ spl2_14
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f200,f54])).

fof(f54,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_3
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f200,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_14
    | ~ spl2_27 ),
    inference(superposition,[],[f109,f198])).

fof(f198,plain,
    ( sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl2_27
  <=> sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f199,plain,
    ( spl2_27
    | ~ spl2_22
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f193,f189,f164,f196])).

fof(f164,plain,
    ( spl2_22
  <=> sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f189,plain,
    ( spl2_26
  <=> ! [X1,X0] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f193,plain,
    ( sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_22
    | ~ spl2_26 ),
    inference(superposition,[],[f190,f166])).

fof(f166,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f164])).

fof(f190,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f184,f174,f43,f189])).

fof(f43,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f174,plain,
    ( spl2_24
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f184,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_24 ),
    inference(resolution,[],[f175,f45])).

fof(f45,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f174])).

fof(f176,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f39,f174])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f167,plain,
    ( spl2_22
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f156,f139,f133,f114,f78,f164])).

fof(f78,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f114,plain,
    ( spl2_15
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f133,plain,
    ( spl2_18
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f139,plain,
    ( spl2_19
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f156,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f155,f135])).

fof(f135,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f155,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f151,f115])).

fof(f115,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f151,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_8
    | ~ spl2_19 ),
    inference(resolution,[],[f140,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f140,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f148,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | spl2_19 ),
    inference(subsumption_resolution,[],[f146,f45])).

fof(f146,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_5
    | spl2_19 ),
    inference(resolution,[],[f141,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f141,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f136,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f131,f127,f48,f43,f133])).

fof(f48,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f127,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f131,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f130,f45])).

fof(f130,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(resolution,[],[f128,f50])).

fof(f50,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_relat_1(X1))
        | k1_relat_1(k7_relat_1(X1,X0)) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f36,f127])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f116,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f111,f100,f43,f114])).

fof(f100,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f111,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f101,f45])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f110,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f41,f108])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f102,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f35,f100])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f80,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f64,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f60,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f55,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f51,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f26,f43])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (26899)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.42  % (26899)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f204,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f46,f51,f55,f60,f64,f80,f102,f110,f116,f129,f136,f148,f167,f176,f191,f199,f203])).
% 0.19/0.42  fof(f203,plain,(
% 0.19/0.42    ~spl2_3 | spl2_4 | ~spl2_14 | ~spl2_27),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f202])).
% 0.19/0.42  fof(f202,plain,(
% 0.19/0.42    $false | (~spl2_3 | spl2_4 | ~spl2_14 | ~spl2_27)),
% 0.19/0.42    inference(subsumption_resolution,[],[f201,f59])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | spl2_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f57])).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    spl2_4 <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.42  fof(f201,plain,(
% 0.19/0.42    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | (~spl2_3 | ~spl2_14 | ~spl2_27)),
% 0.19/0.42    inference(subsumption_resolution,[],[f200,f54])).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f53])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    spl2_3 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.42  fof(f200,plain,(
% 0.19/0.42    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | (~spl2_14 | ~spl2_27)),
% 0.19/0.42    inference(superposition,[],[f109,f198])).
% 0.19/0.42  fof(f198,plain,(
% 0.19/0.42    sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_27),
% 0.19/0.42    inference(avatar_component_clause,[],[f196])).
% 0.19/0.42  fof(f196,plain,(
% 0.19/0.42    spl2_27 <=> sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.19/0.42  fof(f109,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) ) | ~spl2_14),
% 0.19/0.42    inference(avatar_component_clause,[],[f108])).
% 0.19/0.42  fof(f108,plain,(
% 0.19/0.42    spl2_14 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.19/0.42  fof(f199,plain,(
% 0.19/0.42    spl2_27 | ~spl2_22 | ~spl2_26),
% 0.19/0.42    inference(avatar_split_clause,[],[f193,f189,f164,f196])).
% 0.19/0.42  fof(f164,plain,(
% 0.19/0.42    spl2_22 <=> sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.19/0.42  fof(f189,plain,(
% 0.19/0.42    spl2_26 <=> ! [X1,X0] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.19/0.42  fof(f193,plain,(
% 0.19/0.42    sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | (~spl2_22 | ~spl2_26)),
% 0.19/0.42    inference(superposition,[],[f190,f166])).
% 0.19/0.42  fof(f166,plain,(
% 0.19/0.42    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_22),
% 0.19/0.42    inference(avatar_component_clause,[],[f164])).
% 0.19/0.42  fof(f190,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) ) | ~spl2_26),
% 0.19/0.42    inference(avatar_component_clause,[],[f189])).
% 0.19/0.42  fof(f191,plain,(
% 0.19/0.42    spl2_26 | ~spl2_1 | ~spl2_24),
% 0.19/0.42    inference(avatar_split_clause,[],[f184,f174,f43,f189])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    spl2_1 <=> v1_relat_1(sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.42  fof(f174,plain,(
% 0.19/0.42    spl2_24 <=> ! [X1,X0,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.19/0.42  fof(f184,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_24)),
% 0.19/0.42    inference(resolution,[],[f175,f45])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    v1_relat_1(sK1) | ~spl2_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f43])).
% 0.19/0.42  fof(f175,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) ) | ~spl2_24),
% 0.19/0.42    inference(avatar_component_clause,[],[f174])).
% 0.19/0.42  fof(f176,plain,(
% 0.19/0.42    spl2_24),
% 0.19/0.42    inference(avatar_split_clause,[],[f39,f174])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.19/0.42  fof(f167,plain,(
% 0.19/0.42    spl2_22 | ~spl2_8 | ~spl2_15 | ~spl2_18 | ~spl2_19),
% 0.19/0.42    inference(avatar_split_clause,[],[f156,f139,f133,f114,f78,f164])).
% 0.19/0.42  fof(f78,plain,(
% 0.19/0.42    spl2_8 <=> ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.42  fof(f114,plain,(
% 0.19/0.42    spl2_15 <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.19/0.42  fof(f133,plain,(
% 0.19/0.42    spl2_18 <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.19/0.42  fof(f139,plain,(
% 0.19/0.42    spl2_19 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.19/0.42  fof(f156,plain,(
% 0.19/0.42    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | (~spl2_8 | ~spl2_15 | ~spl2_18 | ~spl2_19)),
% 0.19/0.42    inference(forward_demodulation,[],[f155,f135])).
% 0.19/0.42  fof(f135,plain,(
% 0.19/0.42    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_18),
% 0.19/0.42    inference(avatar_component_clause,[],[f133])).
% 0.19/0.42  fof(f155,plain,(
% 0.19/0.42    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | (~spl2_8 | ~spl2_15 | ~spl2_19)),
% 0.19/0.42    inference(forward_demodulation,[],[f151,f115])).
% 0.19/0.42  fof(f115,plain,(
% 0.19/0.42    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_15),
% 0.19/0.42    inference(avatar_component_clause,[],[f114])).
% 0.19/0.42  fof(f151,plain,(
% 0.19/0.42    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) | (~spl2_8 | ~spl2_19)),
% 0.19/0.42    inference(resolution,[],[f140,f79])).
% 0.19/0.42  fof(f79,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) ) | ~spl2_8),
% 0.19/0.42    inference(avatar_component_clause,[],[f78])).
% 0.19/0.42  fof(f140,plain,(
% 0.19/0.42    v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_19),
% 0.19/0.42    inference(avatar_component_clause,[],[f139])).
% 0.19/0.42  fof(f148,plain,(
% 0.19/0.42    ~spl2_1 | ~spl2_5 | spl2_19),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f147])).
% 0.19/0.42  fof(f147,plain,(
% 0.19/0.42    $false | (~spl2_1 | ~spl2_5 | spl2_19)),
% 0.19/0.42    inference(subsumption_resolution,[],[f146,f45])).
% 0.19/0.42  fof(f146,plain,(
% 0.19/0.42    ~v1_relat_1(sK1) | (~spl2_5 | spl2_19)),
% 0.19/0.42    inference(resolution,[],[f141,f63])).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f62])).
% 0.19/0.42  fof(f62,plain,(
% 0.19/0.42    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.42  fof(f141,plain,(
% 0.19/0.42    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_19),
% 0.19/0.42    inference(avatar_component_clause,[],[f139])).
% 0.19/0.42  fof(f136,plain,(
% 0.19/0.42    spl2_18 | ~spl2_1 | ~spl2_2 | ~spl2_17),
% 0.19/0.42    inference(avatar_split_clause,[],[f131,f127,f48,f43,f133])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.42  fof(f127,plain,(
% 0.19/0.42    spl2_17 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.19/0.42  fof(f131,plain,(
% 0.19/0.42    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_17)),
% 0.19/0.42    inference(subsumption_resolution,[],[f130,f45])).
% 0.19/0.42  fof(f130,plain,(
% 0.19/0.42    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | (~spl2_2 | ~spl2_17)),
% 0.19/0.42    inference(resolution,[],[f128,f50])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f48])).
% 0.19/0.42  fof(f128,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) ) | ~spl2_17),
% 0.19/0.42    inference(avatar_component_clause,[],[f127])).
% 0.19/0.42  fof(f129,plain,(
% 0.19/0.42    spl2_17),
% 0.19/0.42    inference(avatar_split_clause,[],[f36,f127])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(flattening,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.19/0.42  fof(f116,plain,(
% 0.19/0.42    spl2_15 | ~spl2_1 | ~spl2_12),
% 0.19/0.42    inference(avatar_split_clause,[],[f111,f100,f43,f114])).
% 0.19/0.42  fof(f100,plain,(
% 0.19/0.42    spl2_12 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.19/0.42  fof(f111,plain,(
% 0.19/0.42    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | (~spl2_1 | ~spl2_12)),
% 0.19/0.42    inference(resolution,[],[f101,f45])).
% 0.19/0.42  fof(f101,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_12),
% 0.19/0.42    inference(avatar_component_clause,[],[f100])).
% 0.19/0.42  fof(f110,plain,(
% 0.19/0.42    spl2_14),
% 0.19/0.42    inference(avatar_split_clause,[],[f41,f108])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f37,f33])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.42  fof(f102,plain,(
% 0.19/0.42    spl2_12),
% 0.19/0.42    inference(avatar_split_clause,[],[f35,f100])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.42  fof(f80,plain,(
% 0.19/0.42    spl2_8),
% 0.19/0.42    inference(avatar_split_clause,[],[f31,f78])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.19/0.42  fof(f64,plain,(
% 0.19/0.42    spl2_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f34,f62])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    ~spl2_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f28,f57])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.19/0.42    inference(cnf_transformation,[],[f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.19/0.42    inference(flattening,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.19/0.42    inference(negated_conjecture,[],[f11])).
% 0.19/0.42  fof(f11,conjecture,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    spl2_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f29,f53])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    spl2_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f27,f48])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.19/0.42    inference(cnf_transformation,[],[f24])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    spl2_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f26,f43])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    v1_relat_1(sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f24])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (26899)------------------------------
% 0.19/0.42  % (26899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (26899)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (26899)Memory used [KB]: 6268
% 0.19/0.42  % (26899)Time elapsed: 0.010 s
% 0.19/0.42  % (26899)------------------------------
% 0.19/0.42  % (26899)------------------------------
% 0.19/0.43  % (26891)Success in time 0.074 s
%------------------------------------------------------------------------------
