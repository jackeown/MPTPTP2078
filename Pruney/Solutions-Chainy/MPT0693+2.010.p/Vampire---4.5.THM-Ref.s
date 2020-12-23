%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 142 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  227 ( 367 expanded)
%              Number of equality atoms :   56 (  91 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f46,f50,f54,f58,f62,f66,f72,f77,f84,f103,f108,f123,f135,f155])).

fof(f155,plain,
    ( ~ spl2_5
    | spl2_15
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl2_5
    | spl2_15
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f49,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f143,plain,
    ( k3_xboole_0(sK0,k2_relat_1(sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0)
    | spl2_15
    | ~ spl2_19 ),
    inference(superposition,[],[f102,f132])).

fof(f132,plain,
    ( ! [X0] : k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_19
  <=> ! [X0] : k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f102,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_15
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f135,plain,
    ( spl2_19
    | ~ spl2_12
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f134,f121,f106,f82,f131])).

fof(f82,plain,
    ( spl2_12
  <=> ! [X0] : r1_tarski(k3_xboole_0(k2_relat_1(sK1),X0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f106,plain,
    ( spl2_16
  <=> ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f121,plain,
    ( spl2_18
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f134,plain,
    ( ! [X1] : k3_xboole_0(k2_relat_1(sK1),X1) = k9_relat_1(sK1,k10_relat_1(sK1,X1))
    | ~ spl2_12
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f125,f107])).

fof(f107,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f125,plain,
    ( ! [X1] : k3_xboole_0(k2_relat_1(sK1),X1) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X1)))
    | ~ spl2_12
    | ~ spl2_18 ),
    inference(resolution,[],[f122,f83])).

fof(f83,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k2_relat_1(sK1),X0),k2_relat_1(sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f119,f64,f39,f34,f121])).

fof(f34,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f39,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f64,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK1))
        | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f108,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f104,f60,f39,f106])).

fof(f60,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f104,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f61,f41])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f103,plain,
    ( ~ spl2_15
    | spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f98,f69,f29,f100])).

fof(f29,plain,
    ( spl2_1
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f69,plain,
    ( spl2_10
  <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f98,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1))
    | spl2_1
    | ~ spl2_10 ),
    inference(superposition,[],[f31,f71])).

fof(f71,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f31,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f84,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f80,f75,f52,f39,f82])).

fof(f52,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f75,plain,
    ( spl2_11
  <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f80,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k2_relat_1(sK1),X0),k2_relat_1(sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f78,f41])).

fof(f78,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(k2_relat_1(sK1),X0),k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(superposition,[],[f53,f76])).

fof(f76,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f77,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f73,f56,f39,f75])).

fof(f56,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f73,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f72,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f67,f44,f39,f69])).

fof(f44,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f67,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f66,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f62,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f58,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f54,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_relat_1)).

fof(f50,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f46,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
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

fof(f42,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f29])).

fof(f21,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (30420)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (30419)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (30419)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f32,f37,f42,f46,f50,f54,f58,f62,f66,f72,f77,f84,f103,f108,f123,f135,f155])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    ~spl2_5 | spl2_15 | ~spl2_19),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    $false | (~spl2_5 | spl2_15 | ~spl2_19)),
% 0.21/0.44    inference(subsumption_resolution,[],[f143,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    k3_xboole_0(sK0,k2_relat_1(sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0) | (spl2_15 | ~spl2_19)),
% 0.21/0.44    inference(superposition,[],[f102,f132])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    ( ! [X0] : (k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0))) ) | ~spl2_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f131])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    spl2_19 <=> ! [X0] : k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1)) | spl2_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    spl2_15 <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    spl2_19 | ~spl2_12 | ~spl2_16 | ~spl2_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f134,f121,f106,f82,f131])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl2_12 <=> ! [X0] : r1_tarski(k3_xboole_0(k2_relat_1(sK1),X0),k2_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl2_16 <=> ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl2_18 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    ( ! [X1] : (k3_xboole_0(k2_relat_1(sK1),X1) = k9_relat_1(sK1,k10_relat_1(sK1,X1))) ) | (~spl2_12 | ~spl2_16 | ~spl2_18)),
% 0.21/0.44    inference(forward_demodulation,[],[f125,f107])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) ) | ~spl2_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f106])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    ( ! [X1] : (k3_xboole_0(k2_relat_1(sK1),X1) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X1)))) ) | (~spl2_12 | ~spl2_18)),
% 0.21/0.44    inference(resolution,[],[f122,f83])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_relat_1(sK1),X0),k2_relat_1(sK1))) ) | ~spl2_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f82])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) ) | ~spl2_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f121])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    spl2_18 | ~spl2_2 | ~spl2_3 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f119,f64,f39,f34,f121])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl2_2 <=> v1_funct_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl2_9 <=> ! [X1,X0] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) ) | (~spl2_2 | ~spl2_3 | ~spl2_9)),
% 0.21/0.44    inference(subsumption_resolution,[],[f118,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f39])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_9)),
% 0.21/0.44    inference(resolution,[],[f65,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    v1_funct_1(sK1) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f34])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) ) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f64])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl2_16 | ~spl2_3 | ~spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f104,f60,f39,f106])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl2_8 <=> ! [X1,X0] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) ) | (~spl2_3 | ~spl2_8)),
% 0.21/0.44    inference(resolution,[],[f61,f41])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) ) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f60])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    ~spl2_15 | spl2_1 | ~spl2_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f98,f69,f29,f100])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl2_1 <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl2_10 <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1)) | (spl2_1 | ~spl2_10)),
% 0.21/0.44    inference(superposition,[],[f31,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) | ~spl2_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f29])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl2_12 | ~spl2_3 | ~spl2_6 | ~spl2_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f80,f75,f52,f39,f82])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl2_6 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    spl2_11 <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_relat_1(sK1),X0),k2_relat_1(sK1))) ) | (~spl2_3 | ~spl2_6 | ~spl2_11)),
% 0.21/0.44    inference(subsumption_resolution,[],[f78,f41])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_relat_1(sK1),X0),k2_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl2_6 | ~spl2_11)),
% 0.21/0.44    inference(superposition,[],[f53,f76])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)) ) | ~spl2_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f75])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl2_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f52])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl2_11 | ~spl2_3 | ~spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f73,f56,f39,f75])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl2_7 <=> ! [X1,X0] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)) ) | (~spl2_3 | ~spl2_7)),
% 0.21/0.44    inference(resolution,[],[f57,f41])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) ) | ~spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f56])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl2_10 | ~spl2_3 | ~spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f67,f44,f39,f69])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl2_4 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) | (~spl2_3 | ~spl2_4)),
% 0.21/0.44    inference(resolution,[],[f45,f41])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f44])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f64])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f60])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f56])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f52])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_relat_1)).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f48])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f39])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f34])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_funct_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f29])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (30419)------------------------------
% 0.21/0.44  % (30419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30419)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (30419)Memory used [KB]: 10618
% 0.21/0.44  % (30419)Time elapsed: 0.009 s
% 0.21/0.44  % (30419)------------------------------
% 0.21/0.44  % (30419)------------------------------
% 0.21/0.44  % (30413)Success in time 0.079 s
%------------------------------------------------------------------------------
